let
  ocamlPackages = (import <nixpkgs> {}).ocaml-ng.ocamlPackages_4_05;
  inherit (ocamlPackages) buildOcaml ounit;
in
buildOcaml rec {
  name = "opti";
  version = "1.0";
  src = ./.;
  buildInputs = [ ounit ];
}
