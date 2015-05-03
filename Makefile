all:
	happy -gca Pargram.y
	alex -g Lexgram.x
	latex Docgram.tex; dvips Docgram.dvi -o Docgram.ps
	ghc --make Testgram.hs -o Testgram
clean:
	-rm -f *.log *.aux *.hi *.o *.dvi
	-rm -f Docgram.ps
distclean: clean
	-rm -f Docgram.* Lexgram.* Pargram.* Layoutgram.* Skelgram.* Printgram.* Testgram.* Absgram.* Testgram ErrM.* SharedString.* gram.dtd XMLgram.* Makefile*

