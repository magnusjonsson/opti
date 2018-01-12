open Syntax_tree
open Opti
open Pretty_printer

let input_file = ref ""
let output_file = ref ""

let args_spec =
  ["-i", Arg.Set_string input_file, "The input .opti file";
   "-o", Arg.Set_string output_file, "The output .c file"]

let main () =
  Arg.parse args_spec (fun s -> raise (Arg.Bad s)) "opti_main -i <input.opti> -o <output.c>";

  match !input_file, !output_file with
  | "", _ -> Arg.usage args_spec "Missing -i argument"; exit 1
  | _, "" -> Arg.usage args_spec "Missing -o argument"; exit 1
  | input_file, output_file ->
     let lexbuf = Lexing.from_channel (open_in input_file) in

     let s: specification = try
         Parser.specification_eof Lexer.token lexbuf
       with
         Parsing.Parse_error ->
         let pos = lexbuf.Lexing.lex_curr_p in
         Printf.fprintf stderr "%s:%i: Parse_error at token %s\n" pos.Lexing.pos_fname pos.Lexing.pos_lnum (Lexing.lexeme lexbuf);
         exit 1
     in

     begin match Semantic_checker.run stderr s with
           | Semantic_checker.Ok -> ()
           | Semantic_checker.Failed_checks -> exit 1
     end;
     let imperative_module =
       Opti.generate_imperative_module s
       |> Unused_locals_removal.remove_unused_locals_in_module
     in
     let p = make_pretty_printer (open_out output_file) in
     C_backend.print_module p imperative_module

let () = main ()
