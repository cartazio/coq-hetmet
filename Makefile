coqc     := coqc -noglob
coqfiles := $(shell find src -name \*.v)
allfiles := $(coqfiles) $(shell find src -name \*.hs)

default: build/CoqPass.hs

build/CoqPass.hs: build/Makefile.coq $(allfiles)

        # first we build with -dont-load-proofs, since that runs very quickly
	cd build; make -f Makefile.coq OPT="-dont-load-proofs" Main.vo

        # however the final extraction must be done without -dont-load-proofs
	cd build; make -f Makefile.coq Extraction.vo
	cat src/Extraction-prefix.hs build/Extraction.hs > build/CoqPass.hs

build/Makefile.coq: $(coqfiles)
	mkdir -p build
	rm -f build/*.v
	rm -f build/*.d
	cd build; ln -s ../src/*.v .
	cd build; coq_makefile *.v > Makefile.coq

clean:
	rm -rf build