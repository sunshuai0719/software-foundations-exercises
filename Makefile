# MakeFile for the 'Software Foundations Exercises' project.

all : Poly

Poly: Lists

Lists: Basics
	coqc Lists.v

Basics: Cases
	coqc Basics.v

Cases:
	coqc Cases.v

clean:
	rm *.vo
	rm *.glob

# end-of-MakeFile