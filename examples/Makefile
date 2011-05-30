ghc_opt := -fwarn-incomplete-patterns -Werror

open:
	make demo
	open .build/test.pdf

#sanity += BiGArrow.hs
#sanity += CircuitExample.hs
sanity += CommandSyntaxExample.hs
sanity += DotProduct.hs
sanity += GArrowTutorial.hs
sanity += GArrowVerilog.hs
sanity += ImmutableHeap.hs
sanity += IsomorphismForCodeTypes.hs
sanity += LambdaCalculusInterpreter.hs
sanity += TypeSafeRun.hs
sanity += Unflattening.hs

sanity_opts = -dcore-lint -fforce-recomp -fcoqpass -ddump-coqpass -ddump-to-file

sanity:
	for A in $(sanity); do ../../../inplace/bin/ghc-stage2 $(sanity_opts) $$A +RTS -K500M || exit -1; done


demo:
	mkdir -p .build
	../../../inplace/bin/ghc-stage2 $(ghc_opt) -odir .build -hidir .build -c Demo.hs -fforce-recomp
	../../../inplace/bin/ghc-stage2 $(ghc_opt) -odir .build -hidir .build --show-iface .build/Demo.hi
	../../../inplace/bin/ghc-stage2 $(ghc_opt) -odir .build -hidir .build GArrowTikZ.hs Demo.hs DemoMain.hs Unify.hs -o .build/demo
	./.build/demo > .build/test.tex
	cd .build; pdflatex test.tex
