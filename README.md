# elementary_combinatory_logic_in_coq
combinatory logic with coq

Copyright Colin20g 
November 2021

Compilation instructions: put the file in any folder and enter the command coqc combinatory_logic.v

Description: This program is an implementation of combinatory logic in coq. The file can be compiled with COQ 8.9 (at least; we don't use any library and the file is self-contained).
It defines terms and a simple type system and it contain proofs of the following results:

-The Church-Rosser theorem which states that the reduction of combinatory logic terms is confluent.

-The normalization theorem which says that every typable term is strongly normalizable: every reduction sequence 
which starts from a typable term is finite.

-The subject-reduction theorem: for any type a and any terms x and x', if x has type a and x reduces to x' then x' has type a

-An abstraction operator: basically the simplest one: a new letter is added to the context C with the coq "option" operator and we 
define for any term f, lambda f := SKK if f= None (the new variable), lambda f := S(lambda g)(lambda h) if f=gh and lambda f = Kf in any 
other case (namely if f=S,K, or "Some v" when v is a constant in C). For every term t we then show that (lambda f)t is reduced to f[None := t]
where g[y:=u] denotes te term obtained by replacing every occurrence of the letter y in the term g by the term u.  

-a fixed point combinator

-Church integers and basic arithmetic operations on them

-The Rice theorem (for his formalism): there are no non constant maps taking their values in the booleans in combinatory logic.

-The standardization theorem and the fact that the strategy consisting in succesively contracting the leftmost redex in 
a term eventually produces the unique normal form of the term, if the term has a normal form (in the program, "normal form" is called "irredcucible").
