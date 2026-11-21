.PHONY: paper verify clean
TEX := $(shell command -v xelatex 2>/dev/null)
paper:
ifneq ($(TEX),)
	xelatex -interaction=nonstopmode -halt-on-error paper.tex
	xelatex -interaction=nonstopmode -halt-on-error paper.tex
else
	tectonic --keep-logs paper.tex
endif
verify:
	python3 verify.py
clean:
	rm -f paper.aux paper.log paper.out
