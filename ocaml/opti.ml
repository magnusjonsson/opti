open Expr
open Syntax_tree
open Fresh
open Delta
open Update
open Unit

let direct_dependent_updates (s: specification) (g: fresh_name_generator) ~(direct_dependents_table: (string, string) Hashtbl.t) ~(rank_table: (string, int) Hashtbl.t) (deltas: delta list): update list
    =
  let not_already_in_delta_set (variable_name: string): bool
      =
    deltas |> List.for_all (fun d -> d.delta_variable_name <> variable_name)
  in
  let direct_dependents: string list =
    deltas |> List.map (fun d -> d.delta_variable_name)
           |> List.map (Hashtbl.find_all direct_dependents_table)
           |> List.concat
           |> List.filter not_already_in_delta_set
           |> Utils.nub_list
           |> List.sort (compare_by_rank rank_table)
  in
  direct_dependents |> List.map (compute_update s g deltas)

let perform_update (u: update) : Imperative.step list
    =
  let d : delta = u.update_delta in
  [Imperative.Step_let(d.delta_amount, d.delta_representation, d.delta_unit, u.update_delta_expr);
   Imperative.Step_do(Imperative.Statement_increment(Imperative.Lhs_global(d.delta_variable_name, d.delta_variable_subscripts),
                                                     Expr_ref(d.delta_amount, [])))]
    
let bring_into_loop (loop_subscripts : (string * string) list) (u: update) : update =
  let rename_subscript = Utils.subst_assoc (List.combine (List.map fst u.update_loop_subscripts)
                                                         (List.map fst loop_subscripts))
  in
  {
    update_loop_subscripts = [];
    update_delta_expr = map_subscripts_in_expr rename_subscript u.update_delta_expr;
    update_delta =
      let d = u.update_delta in
      {
        delta_variable_name = d.delta_variable_name;
        delta_variable_subscripts = List.map rename_subscript d.delta_variable_subscripts;
        delta_amount = d.delta_amount;
        delta_representation = d.delta_representation;
        delta_unit = d.delta_unit;
      }
  }

let rec emit_code_to_propagate_deltas (s: specification) (g: fresh_name_generator) ~(direct_dependents_table: (string, string) Hashtbl.t) ~(rank_table: (string, int) Hashtbl.t) ~(deltas: delta list) : Imperative.step list
    =
  let updates: update list = direct_dependent_updates s g direct_dependents_table rank_table deltas in

  (* group the updates by rank and subscripts and perform updates *)

  let update_class (u: update): int * string list =
    Hashtbl.find rank_table u.update_delta.delta_variable_name, List.map snd (u.update_loop_subscripts)
  in

  let update_groups = updates |> List.map (fun u -> update_class u, u) |> List.sort compare |> Utils.group |> List.map snd in

  (* assumption: updates is already sorted *)

  update_groups |> List.map
      (fun updates ->

        let loop_subscripts = (List.hd updates).update_loop_subscripts in

        let updates = updates |> List.map (bring_into_loop loop_subscripts) in
        
        let new_deltas = List.map (fun u -> u.update_delta) updates in

        Imperative.Step_do
          (Imperative.nested_for
             ~subscripts: loop_subscripts
             ~body: begin

               Imperative.Statement_block
                 (List.concat (List.map perform_update updates)
                  @ emit_code_to_propagate_deltas s g ~direct_dependents_table ~rank_table ~deltas:new_deltas)
             end))

let rec compute_direct_dependents_table (s: specification): (string, string) Hashtbl.t
    =
  let direct_dependents: (string, string) Hashtbl.t  = Hashtbl.create 100 in
  s.specification_variables |> List.iter
    (fun (defined_variable_name, v) ->
      match v.variable_definition with
      | Definition_given -> ()
      | Definition_expr d ->
          let rec visit_expr = function
            | Expr_const _ -> ()
            | Expr_ref(used_variable_name,subscripts) -> Hashtbl.add direct_dependents used_variable_name defined_variable_name
            | Expr_unop(_, e1) -> visit_expr e1
            | Expr_binop(_, e1, e2) -> visit_expr e1; visit_expr e2
            | Expr_index_eq_ne(i1,i2,e1,e2) -> visit_expr e1; visit_expr e2
          in
          visit_expr d.definition_expr_summee
    );
  direct_dependents

let rec compute_rank_table (direct_dependents: (string, string) Hashtbl.t): (string, int) Hashtbl.t
    =
  let rank_table = Hashtbl.create 10 in
  let rec compute_rank var: int =
    try
      Hashtbl.find rank_table var
    with Not_found ->
      let rank = var |> Hashtbl.find_all direct_dependents |> List.map compute_rank |> List.fold_left max (-1) |> (fun rank -> rank + 1) in
      Hashtbl.add rank_table var rank;
      rank
  in
  direct_dependents |> Hashtbl.iter (fun var _ -> compute_rank var |> ignore);
  rank_table

let generate_procedure_to_recompute (s: specification) ~(variable_name: string) ~(v: variable) ~(d: definition_expr)
    =
  let index_args : string list = v.variable_subscripts |> List.map fst in
  {
    Imperative.procedure_index_args = index_args;
    Imperative.procedure_value_args = [];
    Imperative.procedure_body =
      [Imperative.Step_let("sum", v.variable_representation, v.variable_unit, Expr_const(0.0));
       Imperative.Step_do(Imperative.nested_for
                            ~subscripts:d.definition_expr_summation_subscripts
                            ~body: (Imperative.Statement_increment(Imperative.Lhs_local("sum", v.variable_representation),
                                                                   d.definition_expr_summee)));
       Imperative.Step_do(Imperative.Statement_assign(Imperative.Lhs_global(variable_name, index_args),
                                                      Expr_ref("sum", [])))]
  }

let generate_procedure_to_propagate_deltas (s: specification) ~(variable_names: string list) : Imperative.procedure
    =
  let g = make_fresh_name_generator() in
  let deltas: delta list =
    variable_names |> List.map
      (fun variable_name ->
        let v = specification_find_variable s variable_name in
        { delta_variable_name = variable_name;
          delta_variable_subscripts = List.map fst v.variable_subscripts;
          delta_amount = fresh_name_generator_generate_name g (variable_name ^ "_delta");
          delta_representation = v.variable_representation;
          delta_unit = v.variable_unit;
        })
  in
  {
    Imperative.procedure_index_args =
      deltas |> List.map (fun d -> d.delta_variable_subscripts) |> List.concat |> Utils.nub_list;
    Imperative.procedure_value_args =
      deltas |> List.map (fun d -> (d.delta_amount, d.delta_representation, d.delta_unit));
    Imperative.procedure_body =
      let direct_dependents_table = compute_direct_dependents_table s in
      let rank_table = compute_rank_table direct_dependents_table in
      emit_code_to_propagate_deltas s g ~direct_dependents_table ~rank_table ~deltas;
  }


let generate_procedure_to_increment_variables (s: specification) ~(variable_names: string list)
    =
  let g = make_fresh_name_generator() in
  let deltas: delta list =
    variable_names |> List.map
      (fun variable_name ->
        let v = specification_find_variable s variable_name in
        { delta_variable_name = variable_name;
          delta_variable_subscripts = List.map fst v.variable_subscripts;
          delta_amount = fresh_name_generator_generate_name g (variable_name ^ "_delta");
          delta_representation = v.variable_representation;
          delta_unit = v.variable_unit;
        }
      )
  in
  {
    Imperative.procedure_index_args =
      deltas |> List.map (fun d -> d.delta_variable_subscripts) |> List.concat |> Utils.nub_list;
    Imperative.procedure_value_args =
      deltas |> List.map (fun d -> (d.delta_amount, d.delta_representation, d.delta_unit));
    Imperative.procedure_body =
      let direct_dependents_table = compute_direct_dependents_table s in
      let rank_table = compute_rank_table direct_dependents_table in
      let apply_deltas =
        deltas |> List.map
            (fun d -> Imperative.Step_do(Imperative.Statement_increment(Imperative.Lhs_global(d.delta_variable_name, d.delta_variable_subscripts),
                                                                        Expr_ref(d.delta_amount, []))))
      in
      apply_deltas @ emit_code_to_propagate_deltas s g ~direct_dependents_table ~rank_table ~deltas;
  }

type assignment = {
  assignment_delta : delta;
  assignment_value : string;
}

let generate_procedure_to_set_variables (s: specification) ~(variable_names: string list)
    =
  let g = make_fresh_name_generator() in
  let assignments: assignment list =
    variable_names |> List.map
      (fun variable_name ->
        let v = specification_find_variable s variable_name in
        {
          assignment_value = fresh_name_generator_generate_name g (variable_name ^ "_new_value");
          assignment_delta = {
            delta_variable_name = variable_name;
            delta_variable_subscripts = v.variable_subscripts |> List.map fst;
            delta_amount = fresh_name_generator_generate_name g (variable_name ^ "_delta");
            delta_representation = v.variable_representation;
            delta_unit = v.variable_unit;
          }
        })
  in
  let deltas = assignments |> List.map (fun a -> a.assignment_delta)
  in
  {
    Imperative.procedure_index_args =
      assignments |> List.map (fun a -> a.assignment_delta.delta_variable_subscripts) |> List.concat |> Utils.nub_list;
    Imperative.procedure_value_args =
      assignments |> List.map (fun a -> (a.assignment_value, a.assignment_delta.delta_representation, a.assignment_delta.delta_unit));
    Imperative.procedure_body =
      let assign_and_compute_deltas =
        List.concat (assignments |> List.map
            (fun a ->
              let d = a.assignment_delta in
              [Imperative.Step_let(d.delta_amount, d.delta_representation, d.delta_unit,
                                   Expr_binop(Binop_sub,
                                              Expr_ref(a.assignment_value, []),
                                              Expr_ref(d.delta_variable_name, d.delta_variable_subscripts)));
               Imperative.Step_do(Imperative.Statement_assign(Imperative.Lhs_global(d.delta_variable_name, d.delta_variable_subscripts),
                                                              Expr_ref(a.assignment_value, [])))]))
      in
      let direct_dependents_table = compute_direct_dependents_table s in
      let rank_table = compute_rank_table direct_dependents_table in
      assign_and_compute_deltas @ emit_code_to_propagate_deltas s g ~direct_dependents_table ~rank_table ~deltas;
  }

let generate_procedure_to_scale_unit (s: specification) (u: string) : Imperative.procedure =
  let f = make_fresh_name_generator() in
  let factor = fresh_name_generator_generate_name f "factor" in
  { Imperative.procedure_index_args = [];
    Imperative.procedure_value_args = [factor, Representation_float64, unit_one];
    Imperative.procedure_body =
      s.specification_variables
      |> List.map
           (fun (variable_name, v : string * variable) ->
             let power = -(base_unit_power u v.variable_unit) in
             if power == 0 then
               []
             else
               let raised_factor = fresh_name_generator_generate_name f "factor" in
               [Imperative.Step_let(raised_factor,
                                    v.variable_representation,
                                    unit_one,
                                    Simplify.smart_int_pow (Expr_ref(factor, [])) power);
                Imperative.Step_do(Imperative.nested_for
                                     v.variable_subscripts
                                     (Imperative.Statement_scale(
                                          Imperative.Lhs_global(variable_name, List.map fst v.variable_subscripts),
                                          Expr_ref(raised_factor, []))))]
           )
      |> List.concat;
  }
;;

let generate_imperative_variables (s: specification) : (string * Imperative.variable) list =
  s.specification_variables |> List.map
      (fun (variable_name, v) ->
        variable_name, {
          Imperative.variable_linkage = v.variable_linkage;
          Imperative.variable_dimensions = v.variable_subscripts |> List.map (fun (name_,range_name) -> range_name);
          Imperative.variable_representation = v.variable_representation;
          Imperative.variable_unit = v.variable_unit;
        })


exception Recompute_given of string * string

let generate_imperative_procedures (s: specification) : (string * Imperative.procedure) list =
  s.specification_goals |> List.map
    (fun (function_name, g) ->
      function_name,
      match g with
      | Goal_recompute variable_name ->
          let v: variable = specification_find_variable s variable_name in
          begin match v.variable_definition with
          | Definition_given -> raise (Recompute_given(function_name, variable_name))
          | Definition_expr d -> generate_procedure_to_recompute s variable_name v d
          end 
      | Goal_propagate_delta variable_names ->
          generate_procedure_to_propagate_deltas s variable_names
      | Goal_set variable_names ->
         generate_procedure_to_set_variables s variable_names
      | Goal_increment variable_names ->
         generate_procedure_to_increment_variables s variable_names
      | Goal_scale_unit unit_ ->
         generate_procedure_to_scale_unit s unit_
    )


let generate_imperative_module (s : specification) : Imperative.module_ =
  {
    Imperative.module_ranges = s.specification_ranges;
    Imperative.module_variables = generate_imperative_variables s;
    Imperative.module_procedures = generate_imperative_procedures s;
  }
