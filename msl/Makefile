# NOTE: This Makefile is low-tech, but at least it's portable to cygwin.
# We have the .depend file checked into the repository so that 
# this file works even if coqdep cannot be run.  Do "make depend"
# to rebuild the .depend file.

COQC="C:/Coq/bin/coqc.exe" -dont-load-proofs -R . msl
COQDEP="C:/Coq/bin/coqdep.exe"  -R . msl
COQDOC="C:/Coq/bin/coqdoc.exe"

FILES = \
  Axioms.v Extensionality.v base.v eq_dec.v \
  ageable.v sepalg.v psepalg.v age_sepalg.v \
  sepalg_generators.v functors.v sepalg_functors.v combiner_sa.v \
  cross_split.v join_hom_lemmas.v cjoins.v \
  boolean_alg.v tree_shares.v shares.v pshares.v \
  knot.v knot_sa.v knot_prop.v \
  knot_lemmas.v knot_unique.v \
  knot_hered.v knot_hered_sa.v \
  knot_full.v knot_shims.v \
  knot_sa_trivial.v \
  predicates_hered.v predicates_sl.v subtypes.v subtypes_sl.v \
  contractive.v predicates_rec.v \
  msl_standard.v msl_classical.v \
  predicates_sa.v \
#  pred_morphisms.v
#  knot_setoid.v \  takes forever to compile, nobody uses it

.PHONY : clean  all lib docs examples extract

lib: $(FILES:.v=.vo)

.SUFFIXES: .v .vo
.v.vo:
	$(COQC) $*.v

clean:
	rm -f *.vo *~
	rm -f $(FILES:%.v=%.html)
	rm -f $(FILES:%.v=%.glob)
	cd examples; make clean

examples: lib
	cd examples; make

extract:
	coqc -R . msl extract.v

depend:
	$(COQDEP) $(FILES) > .depend
include .depend

