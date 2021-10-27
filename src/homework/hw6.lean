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
B union C with the set A. To prove both the forward
and backward propositions it suffices to prove the x is in set A
or x is in set B or x is in set C. We can do this by recognizing 
that our assumption is really a disjuntion, which we can run 
cases analyses on. By case analysis on our union of sets we 
can prove that x is in A or x is in B or x is in C, and in this context
our the associative property of the union operator is proven.
To prove that the intersection operator on sets is associate
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
English proof:
To prove that the intersection operator is left-distributive
over the intersection operator, we need to prove that the 
intersection of set A with the intersection of sets B and C 
is the same as the intersection of the two sets A intersect with B
and B intersect with C. First we reduce our goal of equality into 
one of bimplication using the set extensionality axiom. To prove our
goals we need to recognize that the intersection operator can be 
thought of as an "and", so it suffices to prove that an element, 
call it x, is in set A, and x is in set B, and x is in set C. 
We can break up our goals into these "ulimate" goals (x is in A, and
x is in B, and x is in C) by applying the introduction rule for and. 
Since our equality goal turned into two goals of implication, we can 
assume the premise, and in every case we can apply the elimination 
rule for and onto our assummption, which gives us the proofs 
that x is in A, and x is in B, and x is in C. Once we prove that 
the same element is in each set, then the left-distributive property
of intersection over intersection is proven. 
-/

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

/-
Our goal is to prove that the union operator is left 
distributive over the intersection operator. To prove this
goal, it suffices to prove an element, call it x, is in the
union of set A with the intersection of sets B and C if and only
if x is in the intersection of the sets A union B and set A union C. 
We can then break this biimplication into two implication goals. To 
prove that x is in the union of set A with the intersecion of sets B
and C implies x is in the intersection of the set A union B and set A
union C, we first assume that x is indeed in the union of set A with
the intersection of sets B and C. What this assumption is really saying 
is that x is in A or x is in B and C, which is a dijunction we can
run case analysis on. We have to show that x being in the intersection
of the set A union B and set A union C logically follows from our assumption. 
In the case where x is in set A, we can show that x is in set A,
which satisfys x is in the intersection of two unions with set A. In
the case where x is in the intersection of B and C, we can derive
proof that x is in B, and a proof that x is in C, using the elimination
rule for and. If x is in B and x is in C, we can prove that x is in
the intersection of one union that includes set B, and another union
that includes set C. Now what is left to prove is that x is in 
the intersection of the sets A union B and set A union C implies
that x is in the union of set A with the intersection of sets B and C. 
We first assume that x is in the intersection of sets A union B and A
union C. With this assumption we can derive proofs that x is in 
A or B, or x is in A or C, both are disjunctions we can run case analysis
on. Using case analysis we can prove x is in each needed set, and in this
context our goal is proven. 
-/


