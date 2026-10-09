all:
	rocq makefile -f _CoqProject -o Makefile.coq
	$(MAKE) -f Makefile.coq -j8

clean:
	@if [ -f Makefile.coq ]; then $(MAKE) -f Makefile.coq cleanall; fi
