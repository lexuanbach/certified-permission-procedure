COQC="C:/Coq/bin/coqc.exe" -dont-load-proofs -R . uf
COQDEP="C:/Coq/bin/coqdep.exe"  -R . uf
COQDOC="C:/Coq/bin/coqdoc.exe"

FILES = \
  base.v \
  UF_interface.v \
  UF_base.v \
  UF_implementation.v \
  
.PHONY : clean  all lib docs examples extract

lib: $(FILES:.v=.vo)

.SUFFIXES: .v .vo
.v.vo:
	$(COQC) $*.v

clean:
	rm -f *.vo *~
	rm -f $(FILES:%.v=%.html)
	rm -f $(FILES:%.v=%.glob)

