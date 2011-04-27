all:
	../../../inplace/bin/ghc-stage2 -dcore-lint -fforce-recomp -fcoqpass -ddump-coqpass -ddump-to-file \
		`ls *.hs | grep -v Regex | grep -v Unify.hs | grep -v GArrowTikZ.hs ` +RTS -K500M 
	../../../inplace/bin/ghc-stage2 -dcore-lint -fforce-recomp \
		RegexMatcher.hs Unify.hs GArrowTikZ.hs

tikz:
	mkdir .build
	../../../inplace/bin/ghc-stage2 -odir .build -hidir .build GArrowTikZ.hs Unify.hs
	./GArrowTikZ > .build/test.tex
	cd .build; pdflatex test.tex
	open .build/test.pdf
