.PHONY: all agdatex popl

all: cat.vo yade.vo

%.vo: %.v
	coqc -R . Yade $<

clean:
	rm *.vo *.vok *.vos *.glob

