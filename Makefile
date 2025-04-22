.PHONY: all

all: example

distributivelaw: yade.vo cat.vo cattactic.vo distributivelaw.vo

example: yade.vo example.vo
	
%.vo: %.v
	coqc -R . Yade $<

clean:
	rm *.vo *.vok *.vos *.glob

