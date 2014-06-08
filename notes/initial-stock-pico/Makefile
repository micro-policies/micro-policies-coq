ifeq ($(USER),demange)
  OTT = "/Users/demange/ott_distro_0.21.2/bin/ott"
else
  OTT = "$(shell which ott || echo \"$(HOME)\"/bin/ott)"
endif

doc: main.pdf 

all: doc

%.pdf.loop: 
	pdflatex temp/$*
	pdflatex temp/$*
	pdflatex temp/$*

main.pdf: temp/main.tex temp/defns.tex 
	${MAKE} $@.loop

once: temp/main.tex temp/defns.tex 
	pdflatex temp/main	

clean:
	@ rm -rf temp *.aux *.log *.out main.pdf 

temp/defns.tex: defns.ott Makefile
	if [ ! -d "temp" ]; then mkdir temp; fi
	${OTT} -tex_wrap false -i defns.ott -o temp/defns.tex

temp/main.tex: main.tex temp/defns.tex
	if [ ! -d "temp" ]; then mkdir temp; fi
	${OTT} -i defns.ott -tex_wrap false -tex_filter $< $@

.PHONY : all clean
