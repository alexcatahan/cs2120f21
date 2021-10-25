import data.set

/-
CS2120 F21 HW5

The goals of this assignment are to give you
practice with proofs of propositions that use
existential quantificaton, and to develop your
understanding of formal and informal proofs in
set theory.
-/

/-
PART I: EXISTENTIAL QUANTIFICATION.
-/

/-
To start, suppose that α and β are arbitrary
types, and p and q are predicates on values
of these types: α and β, respectively.
-/

axioms 
  (α β : Type)    -- data types
  (p : α → Prop)  -- predicates
  (q : β → Prop)

/-
In this context complete the following tasks:

(1) Write a fluent English-language statement
of the proposition to be proved. 

(2) Provide a formal proof of the proposition.

(3) Write an informal proof of the proposition.
-/

-- here's the proposition
example : 
  (∃ (f : α → β), ∀ (a : α), p a → q (f a)) →
  (∃ (a : α), p a) → 
  (∃ (b : β), q b) := 

/-
What does this propositon say? Explain it in
plain English. Here's a start: "If there's a 
function that maps/takes every α value that ... 
-- your completed English rendition here:
If there's a function that maps/takes every α value and
turns it to a corresponding β value, then for all values a of type α,
if the predicate p is true for a, then the predicate
q onto the mapping function applied to a is true. 
In this context, if there exists an a of type α such that 
the predicate p is true for a, then there exists
a b of type β such that the predicate of q is true for b.
-/


-- Give your formal proof here
begin
  assume h,
  assume h2,
  cases h with w pf,
  cases h2 with w2 pf2,
  apply exists.intro (w w2),
  exact (pf w2 pf2),

end
/-
informal proof:
First assume there exists a function f that maps
α types to β types, such that if 
the predicate p applied to the alpha type is true, then the
proposition q is true for the mapping function applied to 
the alpha type. We then  assume that there exists a value 
of type α, call it a, such that the predicate p is true for a. 
We now need to prove that there exists a value b of type β
such that the predicate q is true for b. We do this by case
analysis on our assumptions. Because of case analysis,
we can now provide a witness to the existential proposition, 
which says there exists a value of type β, and now all that 
is left to prove is that the predicate q can be applied 
to the witness. We do this by applying a proof that
for all a of type α, if the predicate p true for a, 
then the proposition q is true for the mapping function 
applied to a, onto a witness of an α type and a proof that 
the predicate p is applied to the α type. 
-/
  

