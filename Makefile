.PHONY: all agdatex popl

all: cat.vo yade.vo

%.vo: %.v
	coqc -R . Yade $<


