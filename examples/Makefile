# -fwarn-incomplete-patterns

ghc = ../../../inplace/bin/ghc-stage2
#ghc = ghc
ghc_opt :=  -Werror -odir .build -hidir .build

open:
	make demo
	open .build/test.pdf

#sanity += BiGArrow.hs
sanity += IFLDemos.hs
sanity += CircuitExample.hs
sanity += CommandSyntaxExample.hs
sanity += DotProduct.hs
sanity += GArrowTutorial.hs
sanity += GArrowVerilog.hs
sanity += ImmutableHeap.hs
sanity += IsomorphismForCodeTypes.hs
sanity += LambdaCalculusInterpreter.hs
sanity += TypeSafeRun.hs
#sanity += Unflattening.hs

sanity_opts  = -dcore-lint -fforce-recomp -fcoqpass -ddump-coqpass -ddump-to-file
sanity_opts += -fsimpleopt-before-flatten
sanity_opts += -odir .build -hidir .build 

sanity:
	for A in $(sanity); do echo; echo; $(ghc) $(sanity_opts) $$A +RTS -K500M || exit -1; done

demo-pretty:
	$(ghc) $(ghc_opt) -main-is GArrowPretty GArrowPretty.hs -o GArrowPretty

demo-v:
	$(ghc) $(ghc_opt) -main-is GArrowVerilog GArrowVerilog.hs -o GArrowVerilog
	./GArrowVerilog

demo-verilog:
	$(ghc) $(sanity_opts) -c VerilogDemo.hs
	$(ghc) $(ghc_opt) -main-is GArrowVerilog GArrowVerilog.hs -o GArrowVerilog
	./GArrowVerilog

demo:
	mkdir -p .build
	$(ghc) $(ghc_opt) -c Demo.hs -fforce-recomp
	$(ghc) $(ghc_opt) --show-iface .build/Demo.hi
	$(ghc) $(ghc_opt) GArrowTikZ.hs Demo.hs DemoMain.hs Unify.hs -o .build/demo
	./.build/demo > .build/test.tex
	cd .build; TEXINPUTS=../tex-bits/:$TEXINPUTS: pdflatex test.tex
