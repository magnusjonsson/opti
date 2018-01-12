OCAMLBUILD=ocamlbuild

all:
	${OCAMLBUILD} opti_main.native opti_test.native -pkg oUnit
	./opti_test.native
clean:
	${OCAMLBUILD} -clean
