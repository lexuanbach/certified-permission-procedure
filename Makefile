COQC="C:/Coq/bin/coqc.exe" -dont-load-proofs 
COQDEP="C:/Coq/bin/coqdep.exe"  
COQDOC="C:/Coq/bin/coqdoc.exe"

FILES = \
base.v \
borders.v \
share_dec_base.v \
base_properties.v \
share_equation_system.v \
share_dec_interface.v \
share_correctness_base.v \
share_correctness.v \
share_decompose_base.v \
share_decompose.v \
share_to_bool.v \
share_simplifier.v \
fbool_solver.v \
bool_to_formula.v \
bool_solver.v \
bound_map.v \
share_bounder.v \
share_solver.v \
partition_modules.v \
share_solver_with_partition.v \
  
.PHONY : clean  all lib docs examples extract

lib: $(FILES:.v=.vo)

.SUFFIXES: .v .vo
.v.vo:
	$(COQC) $*.v

clean:
	rm -f *.vo *~
	rm -f $(FILES:%.v=%.html)
	rm -f $(FILES:%.v=%.glob)

