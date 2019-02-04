COQC="C:/Coq/bin/coqc.exe" -dont-load-proofs -R . rbt
COQDEP="C:/Coq/bin/coqdep.exe"  -R . rbt
COQDOC="C:/Coq/bin/coqdoc.exe"

FILES = \
  MMapInterface.v \
  MMapGenTree.v \
  MMapRBT.v \
  
.PHONY : clean  all lib docs examples extract

lib: $(FILES:.v=.vo)

.SUFFIXES: .v .vo
.v.vo:
	$(COQC) $*.v

clean:
	rm -f *.vo *~
	rm -f $(FILES:%.v=%.html)
	rm -f $(FILES:%.v=%.glob)

