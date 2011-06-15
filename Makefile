coqc     := coqc -noglob -opt
coqfiles := $(shell find src -name \*.v  | grep -v \\\#)
allfiles := $(coqfiles) $(shell find src -name \*.hs | grep -v \\\#)
coq_version := $(shell coqc -v | head -n1 | sed 's_.*version __' | sed 's_ .*__')
coq_version_wanted := 8.3pl2-tracer

default: all

all: $(allfiles)
	$(MAKE) build/Makefile.coq
	cd build; $(MAKE) -f Makefile.coq OPT="-opt -dont-load-proofs" All.vo

build/CoqPass.hs: $(allfiles)
ifeq ($(coq_version),$(coq_version_wanted))
	make build/Makefile.coq
	cd build; $(MAKE) -f Makefile.coq OPT="-opt -dont-load-proofs" ExtractionMain.vo
	cd build; $(MAKE) -f Makefile.coq Extraction.vo
	cat src/Extraction-prefix.hs                                     > build/CoqPass.hs
	cat build/Extraction.hs | grep -v '^module' | grep -v '^import' >> build/CoqPass.hs
else
	@echo
	@echo ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
	@echo ++ YOU DO NOT HAVE COQ VERSION $(coq_version_wanted) INSTALLED  ++
	@echo ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
	@echo
	@echo Therefore, I am going to "git pull" from the coq-extraction-baked-in
	@echo branch of the repository.
	@echo
	git pull http://git.megacz.com/coq-hetmet.git coq-extraction-baked-in:master
endif


build/Makefile.coq: $(coqfiles) src/categories/src
	mkdir -p build
	rm -f build/*.v
	rm -f build/*.d
	cd build; ln -fs `find ../src -name \*.v` .
	cd build; coq_makefile *.v > Makefile.coq

src/categories/src:
	git submodule update --init src/categories
	cd src/categories; git checkout master

clean:
	rm -rf build

examples/test.pdf:
	../../../inplace/bin/ghc-stage2 GArrowTikZ.hs
	./GArrowTikZ > test.tex
	pdflatex test.tex
	open test.pdf

examples/doc/index.html:
	mkdir -p examples/doc
	haddock --html Unify.hs
	open Unify.html


merged:
	mkdir -p .temp
	cd src; for A in *.v; do cat $$A  | grep -v '^Require Import' > ../.temp/`echo $$A | sed s_\\\\.v_._`; done
	cd src/categories/src; for A in *.v; do cat $$A | \
	   grep -v '^Require Import' > ../../../.temp/`echo $$A | sed s_\\\\.v_._`; done
	cp src/Banner.v .temp/GArrows.v
	cd .temp; grep '^Require Import ' ../src/All.v | sed 's_Require Import _echo;echo;echo;echo;echo;cat _' | bash >> GArrows.v
	cd .temp; time $(coqc) -dont-load-proofs -verbose GArrows.v
	echo
	echo COMPILATION OK
	echo

pushcheck:
	ssh megacz.com -- 'rm -rf /tmp/pushcheck; mkdir /tmp/pushcheck; cd /tmp/pushcheck; git clone http://git.megacz.com/ghc-hetmet.git && git clone http://git.megacz.com/coq-hetmet.git ghc-hetmet/compiler/hetmet'
	rsync -are ssh --progress --verbose --exclude .git --exclude src/categories/build/ --exclude build/ ./ megacz.com:/tmp/pushcheck/ghc-hetmet/compiler/hetmet/
	ssh megacz.com -- '/vol/megacz/pushcheck2.sh'


# this is for Adam's use only!
push: build/CoqPass.hs
	git push http://git.megacz.com/coq-hetmet.git master
	git add -f build/CoqPass.hs; \
	  git commit -m 'update baked-in CoqPass.hs' && \
	  (git push -f http://git.megacz.com/coq-hetmet.git master:coq-extraction-baked-in; \
	   git reset HEAD^)
	rm -rf .temp
	mkdir .temp
	cd .temp; ln -s ../src/*.v .
	cd .temp; for A in *.v; do \
	  echo Latexing $$A ... ;\
	  echo '\\documentclass[9pt,landscape]{article}' > $$A.tex; \
	  echo '\\usepackage[landscape]{geometry}'       >> $$A.tex; \
	  echo '\\usepackage[cm]{fullpage}'       >> $$A.tex; \
	  echo '\\usepackage{amsmath}'        >> $$A.tex; \
	  echo '\\usepackage{amssymb}'        >> $$A.tex; \
	  echo '\\usepackage{stmaryrd}'       >> $$A.tex; \
	  echo '\\usepackage{upgreek}'        >> $$A.tex; \
	  echo '\\usepackage{parskip}'        >> $$A.tex; \
	  echo '\\begin{document}'            >> $$A.tex; \
	  echo '{{\\tt{'           >> $$A.tex; \
	  echo ''           >> $$A.tex; \
	  java -jar ~/bin/unicode2tex.jar < ../src/$$A >> $$A.tex;\
	  echo '}}}'                           >> $$A.tex; \
	  echo '\\end{document}'              >> $$A.tex; \
	  pdflatex $$A.tex < /dev/null; done
	ssh login.eecs.berkeley.edu -- 'rm public_html/coq-in-ghc/pdfs/*.pdf' ; true
	scp .temp/*.pdf login.eecs.berkeley.edu:public_html/coq-in-ghc/pdfs/
	rm -rf .temp
