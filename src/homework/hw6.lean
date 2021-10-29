import data.set

/-
Exercise: Prove that for any set, L, L ∩ L = L.
-/
example : ∀ {α : Type} (L : set α), L ∩ L = L := 
begin
  assume α L,
  apply set.ext _,
  assume x,
  apply iff.intro,
  --forward
  assume h,
  cases h with xinL xinL,
  apply xinL,
  --backward
  assume xinL,
  apply and.intro xinL xinL,

end


/-
Exercise: Give a formal statement and proof, then an 
English language proof, that the union operator on 
sets is commutative.
-/
example : ∀ {α : Type} (L X : set α), L ∪ X = X ∪ L := 
begin 
  assume α L X,
  apply set.ext _,
  assume x,
  split,
  --forward
  assume LunX,
  cases LunX,
  apply or.intro_right,
  apply LunX,
  apply or.intro_left,
  apply LunX,
  --backward
  assume XinL,
  cases XinL,
  apply or.intro_right,
  exact XinL,
  apply or.intro_left,
  exact XinL,
  
end

/-
English Proof:
To prove that L union X is the same as X union L we can first apply
cases on L union X. The two cases is that some element, call it x,
is in L or x is in X. We now have to proof that x is in X or L, 
and in the first case of our case analysis, x is in L, and in the 
second case of our case analysis x is in X,
so the disjuntion, or union, is true. We now have to prove the 
backwards proposition that if x is in X union L, then x is in 
L union X. We again do this by utilizing case analysis 
and the introduction rule for or, since unions can be thought 
of as disjunctions. Once we prove this, L ∪ X = X ∪ L is proved
to be true. 
-/



/-
Exercise: Prove that ⊆ is reflexive and transitive.
Give a formal statement, a formal proof, and an English
language (informal) proof of this fact.
-/
example : ∀ {α : Type} (A : set α), A ⊆ A ∧ ∀ {α : Type} (A B C: set α), A ⊆ B → B ⊆ C → A ⊆ C:=
begin 
--reflexive
assume α A,
split,
assume x,
assume xinA,
apply xinA,
--transitive
assume α A B C,
assume AsubB,
assume BsubC,
assume x,
assume xinA,
have xinB : x ∈ B := AsubB xinA,
have xinC : x ∈ C := BsubC xinB,
exact xinC,

end

/-
English Proof:
First we have to prove that ⊆ if reflexive, which means that 
a set is a subset or equal to itself. If we have a set called 
A, then A being a subset of equal to A means if x is in A, 
then x is in A. Since this subset or equal to is really 
and implication we can assume the premise, that x is in A, 
and use that assumption to prove x is in A. Now what is 
left to prove is the ⊆ is transitive. First we assume that 
we have three sets, A B and C, and we assume A is a subset
of B, and B is a subset of C. What is left to be proven is 
A is a subset of C. What our assumptions really are saying 
is that an element x is in A which implies x is in B, and our second
assumption says if x is in B then x is in C. Combining the meanings
of these assumption we arrive at the proof that if x is in A, 
then x is in C, which is the definition of a subset so 
transitivity is proven.

-/

/-
Exercise: Prove that ∪ and ∩ are associative.
Give a formal statement, a formal proof, and an 
English language (informal) proof of this fact.
-/
example : ∀ {α : Type} (A B C : set α), (A ∪ B) ∪ C = A ∪ (B ∪ C) ∧ (A ∩ B) ∩ C = A ∩ (B ∩ C) :=
begin 
  --union
  assume α A B C,
  split,
  apply set.ext _,
  assume x,
  split,
  assume h,
  cases h,
  cases h,
  apply or.intro_left,
  exact h,
  apply or.intro_right,
  apply or.intro_left,
  exact h,
  apply or.intro_right,
  apply or.intro_right,
  exact h,
  --backward
  assume h,
  cases h,
  apply or.intro_left,
  apply or.intro_left,
  exact h,
  cases h,
  apply or.intro_left,
  apply or.intro_right,
  exact h,
  apply or.intro_right,
  exact h,
  --intersection
  apply set.ext _,
  assume x,
  split,
  assume h,
  cases h with AandB C,
  apply and.intro,
  have xinA : x ∈ A := and.elim_left AandB,
  apply xinA,
  split,
  have xinB : x ∈ B := and.elim_right AandB,
  exact xinB,
  exact C,
  assume h,
  cases h with A BandC,
  split,
  split,
  exact A,
  have xinB := and.elim_left BandC,
  apply xinB,
  have xinC := and.elim_right BandC,
  apply xinC,

end

/-
English proof:
First we have to prove that the union of sets is associative. 
Since this proof is dealing with the equality of sets, we reduce
the problem by applying the set extensionality axiom. What is now
left to be proven is the biimplication of the set extensionality, which
says an element, call it x, is in the union of the set A union B with
the set C, if and only if x is in the union of the set
B union C with the set A. To prove the forward proposition
(if x is in the union of the sets A union B and C, then x is in the union 
of sets B union C and A) we assume we have some element x, and 
then we assume that x is in the union of sets A union B and C. What 
is left to be proven is that x is in the union of sets B union C
with set A. We can do this by recognizing that our assumption is 
really a disjuntion, with 2 cases: x is in set A union B
or x is in set C. With this disjunction we can run 
case analysis. In the first case, where x is in set A union B, we can 
run case analysis again to further break it down into two seperate cases, 
where x is in set A or x is in set B. In the case where x is in A
we can prove that x is in the union of sets B union C and set A, because
that proof goal is true if X is in the set B or C, or in the set A, 
and we have an assumption that x is in set A. In the case where x is
in B we can again simplify our proof goal into proving x is in B using 
the or introduction rule since unions can be thought of as disjunctions. 
Our case is where x is in B, so that is proven. In the case where x is
in C, we again can use or introduction rules to simplify our goal
down to proving x is in C, which is proven by our assumption. Now what
is left to be proven is the backwards proposition, that is x is in 
the unions of sets B union C with A, then x is in the unions of sets 
A union B with C. We can again utlize case analysis and the or introduction 
rule to simplify this goal into three cases, one where we prove x is in A, 
one where x is in B, and another proving x is in C. Using our assumption we 
can prove these goals, and in that context the union operator being 
associative is proven. To prove that the intersection operator on sets is associate
we can again reduce this goal using the set extensionality axiom. We then 
assume the premise that x is in the intersection of sets A intersection B 
and C, and since intersections can be thought of as "ands", we can 
simplify our goal using the and introduction rule. What is left to be 
proven is that x is in A and x is in B and x is in C, and by applying
the and elimination rule to our assumption we can arrive at these 
conclusions. In this context, intersection being associative is proven. 
-/

/-
Assignment: read (at least skim) the Sections 1 and 2 of 
the Wikipedia page on set identities: 
https://en.wikipedia.org/wiki/List_of_set_identities_and_relations 
There, , among *many* other facts, you will find definitions 
of left and right distributivity. To complete the remainder
of this assignment, you need to understand what it means for 
one operator to be left- (or right-) distributive over another. 
-/


/-
Exercise: Formally state and prove both formally and 
informally that ∩ is left-distributive over ∩.
-/
example: ∀ {α : Type} (A B C : set α), A ∩ (B ∩ C) = (A ∩ B) ∩ (B ∩ C) :=
begin
   assume α A B C,
   apply set.ext _,
   assume x,
   split,
   assume h,
   split,
   split,
   have xinA := and.elim_left h,
   exact xinA,
   have BandC := and.elim_right h,
   have xinB := and.elim_left BandC,
   exact xinB,
   split,
   have BandC := and.elim_right h,
   have xinB := and.elim_left BandC,
   exact xinB,
   have BandC := and.elim_right h,
   have xinC := and.elim_right BandC,
   exact xinC,
   assume h,
   split,
   have AandB := and.elim_left h,
   have xinA := and.elim_left AandB,
   exact xinA,
   split,
   have AandB := and.elim_left h,
   have xinB := and.elim_right AandB,
   exact xinB,
   have BandC := and.elim_right h,
   have xinC := and.elim_right BandC,
   exact xinC,
   
end


/-
Exercise: Formally state and prove both formally 
and informally that ∪ is left-distributive over ∩.
-/
example : ∀ {α : Type} (A B C : set α), A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C) :=
begin 
  assume α A B C,
  apply set.ext _,
  assume x,
  split,
  assume h,
  split,
  cases h,
  apply or.intro_left,
  exact h,
  apply or.intro_right,
  apply and.elim_left h,
  cases h,
  apply or.intro_left,
  exact h,
  apply or.intro_right,
  apply and.elim_right h,
  assume h,
  have AorB := and.elim_left h,
  have AorC := and.elim_right h,
  cases AorB,
  cases AorC,
  apply or.intro_left,
  exact AorB,
  apply or.intro_left,
  exact AorB,
  cases AorC,
  apply or.intro_left,
  exact AorC,
  apply or.intro_right,
  apply and.intro AorB AorC,
  
end


