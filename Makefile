# MakeFile for the 'Software Foundations Exercises' project.

all : Imp

Imp: SfLib
	coqc Imp.v

SfLib:
	coqc SfLib.v

Rel: Logic
	coqc Rel.v

Logic: Prop
	coqc Logic.v

Prop: Gen
	coqc Prop.v

Gen: Poly
	coqc Gen.v

Poly: Lists
	coqc Poly.v

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