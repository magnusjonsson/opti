Run:

```
# Should pick up opam and LSP config from shell.nix
# otherwise, nix-shell -p opam directly
nix-shell
opam init
opam install dune
opam install ounit
# Put dune on the path
eval $(opam env)
```

Then:

```
dune build @runtest @install
dune exec opti -- -i <target> -o <out.c> -h <header.h>
```
