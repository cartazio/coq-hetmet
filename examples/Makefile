ghc_opt := -fwarn-incomplete-patterns -Werror

open:
	make demo
	open .build/test.pdf

sanity:
	../../../inplace/bin/ghc-stage2 -dcore-lint -fforce-recomp -fcoqpass -ddump-coqpass -ddump-to-file \
		`ls *.hs | grep -v Regex | grep -v Unify.hs | grep -v GArrowTikZ.hs ` +RTS -K500M 
	../../../inplace/bin/ghc-stage2 -dcore-lint -fforce-recomp \
		RegexMatcher.hs Unify.hs GArrowTikZ.hs

demo:
	mkdir -p .build
	../../../inplace/bin/ghc-stage2 $(ghc_opt) -odir .build -hidir .build -c Demo.hs -fforce-recomp
	../../../inplace/bin/ghc-stage2 $(ghc_opt) -odir .build -hidir .build --show-iface .build/Demo.hi
	../../../inplace/bin/ghc-stage2 $(ghc_opt) -odir .build -hidir .build GArrowTikZ.hs Demo.hs DemoMain.hs Unify.hs -o .build/demo
	./.build/demo > .build/test.tex
	cd .build; pdflatex test.tex
