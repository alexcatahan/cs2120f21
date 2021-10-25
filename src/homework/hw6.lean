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
and in the first case x is in L, and in the second case x is in X,
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


