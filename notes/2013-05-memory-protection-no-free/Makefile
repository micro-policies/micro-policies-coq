ifeq ($(USER),demange)
  OTT = "/Users/demange/ott_distro_0.21.2/bin/ott"
else
  OTT = "$(shell which ott || echo \"$(HOME)\"/bin/ott)"
endif

PDFLATEX = pdflatex -halt-on-error -synctex=1

all: 
	$(MAKE) once
#	$(PDFLATEX) main
#	$(PDFLATEX) main

once:  temp/main.tex temp/defns.tex 
	$(PDFLATEX) main
#	bibtex main
	cp main.pdf temp.pdf

clean:
	@ rm -rf temp *.aux *.log main.pdf 
	@ rm *~ *.log main.pdf *.out *.bbl *.blg main.synctex.gz

temp/defns.tex: defns.ott Makefile
	if [ ! -d "temp" ]; then mkdir temp; fi
	${OTT} -tex_wrap false -i defns.ott -o temp/defns.tex

temp/main.tex: main.tex temp/defns.tex
	if [ ! -d "temp" ]; then mkdir temp; fi
	${OTT} -i defns.ott -tex_wrap false -tex_filter $< $@

.PHONY : all clean
