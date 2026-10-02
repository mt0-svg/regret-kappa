# Build: make (the PDF), then make map (STATEMENTS.md at the root of the repository, from main.tex and main.aux).

all:
	latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex

map: all
	bash statement_map.sh

clean:
	latexmk -C main.tex

.PHONY: all map clean
