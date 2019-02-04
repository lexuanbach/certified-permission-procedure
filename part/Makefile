COQC="C:/Coq/bin/coqc.exe" -dont-load-proofs -R . part
COQDEP="C:/Coq/bin/coqdep.exe"  -R . part
COQDOC="C:/Coq/bin/coqdoc.exe"

FILES = \
  base.v \
  partition_interface.v \
  partition_base.v \
  partition_interface.v \
  partition_ibase.v \
  partition_implementation.v \
  
.PHONY : clean  all lib docs examples extract

lib: $(FILES:.v=.vo)

.SUFFIXES: .v .vo
.v.vo:
	$(COQC) $*.v

clean:
	rm -f *.vo *~
	rm -f $(FILES:%.v=%.html)
	rm -f $(FILES:%.v=%.glob)

