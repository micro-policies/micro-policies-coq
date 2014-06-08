all: ott-all ott tex

tex:     sfi.pdf
ott:     sfi-rules.tex
ott-all: sfi-rules-all.pdf

sfi.pdf: sfi-rules.tex sfi.tex
	pdflatex sfi.tex
	pdflatex sfi.tex

sfi-rules.tex: sfi-rules.ott
	ott -i sfi-rules.ott -tex_wrap false -o sfi-rules.tex

sfi-rules-all.pdf: sfi-rules.ott
	ott -i sfi-rules.ott -o sfi-rules-all.tex
	pdflatex sfi-rules-all.tex

clean:
	rm -f sfi-rules.tex sfi-rules.v sfi-rules-all.tex
	rm -f *.aux
	rm -f *.log
	rm -f *.pdf
