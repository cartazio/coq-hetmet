coqc     := coqc -noglob
coqfiles := $(shell find src -name \*.v)
allfiles := $(coqfiles) $(shell find src -name \*.hs)

default: build/CoqPass.hs

build/CoqPass.hs: $(allfiles)
	make build/Makefile.coq
	cd build; make -f Makefile.coq Extraction.vo
	cat src/Extraction-prefix.hs                                     > build/CoqPass.hs
	cat build/Extraction.hs | grep -v '^module' | grep -v '^import' >> build/CoqPass.hs

build/Makefile.coq: $(coqfiles)
	mkdir -p build
	rm -f build/*.v
	rm -f build/*.d
	cd build; ln -s ../src/*.v .
	cd build; coq_makefile *.v > Makefile.coq

clean:
	rm -rf build



# this is for Adam's use only!
publish:
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

push: build/CoqPass.hs
	git push http://git.megacz.com/coq-garrows.git master
	git add -f build/CoqPass.hs
	git commit -m 'update baked-in CoqPass.hs'
	git push http://git.megacz.com/coq-garrows.git master:coq-extraction-baked-in
	git reset HEAD^
