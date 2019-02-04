Good to run in version 8.4pl5. Remember to change the Coq dir in each makefile before running. Run "make" in this order:

1. cd msl -> make -> cd ..
2. cd rbt -> make -> cd ..
3. cd uf -> make -> cd ..
4. cd part -> make -> cd ..
5. make

For examples, go to tests folder. share_props.v checks basic share properies such as commutativity, associativity,.. while coq_tests.v contains all test cases taken from testcases subfolder. The coq_tests_extraction.ml is the extracted code of coq_tests.v in OCaml with some modifications. Use ocamlopt to compile and run.

To have an overview of the tool ,open share_dec_interface.v.

For questions, send me an email at bachdylan@gmail.com
