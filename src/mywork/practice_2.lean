/-
Prove the following simple logical conjectures.
Give a formal and an English proof of each one.
Your English language proofs should be complete
in the sense that they identify all the axioms
and/or theorems that you use.
-/

example : true := true.intro

/-
true has a single proof, true.intro
-/


example : false := _    -- trick question? why?

/-
Trick question because false as a proposition
has no proofs at all. It is an uninhabited type.
-/

example : ∀ (P : Prop), P ∨ P ↔ P := 
begin
  assume P,
  apply iff.intro _ _,
  assume porp,
  apply or.elim porp,
  assume p,
  exact p,
  assume p,
  exact p,
  assume p,
  exact or.intro_left P p,
end

/-
example : ∀ (P : Prop), P ∨ P ↔ P := 

Proof: We assume that P is an arbitrary 
proposition. Our goal is to prove 
We then apply the iff.intro which P ∨ P ↔ P
returns a bidirectional proof of P ∨ P → P ∧ P → P ∨ P. 
We now have two goals. First, to prove 
P ∨ P → P, we assume P ∨ P is true, and
call the proof of P ∨ P, porp, then show 
that P follows. We do this by applying
or.elim to porp, which means both propositions
in the "or" statement (P ∨ P), implies P, so P → P ∧ P → P. 
Now we have to prove two implications, which, in 
both cases, we do by assuming P, and using that 
assumption to prove P. Now we have to prove P → P ∨ P. 
Again we will use the introduction rule for implications, 
assume the premise is true (p : P) and show the rest 
follows by logical consequence. We assume P is true 
and apply or.intro_left to simplify P ∨ P to just P. 
We can now use the assumption of the proof of P to prove P.  
In that context ∀ (P : Prop), P ∨ P ↔ P is proven. 
-/

example : ∀ (P : Prop), P ∧ P ↔ P := 
begin
  assume P,
  apply iff.intro _ _,
  assume pp,
  have p : P := and.elim_left pp,
  exact p,
  assume p,
  apply and.intro,
  exact p,
  exact p,
end
/-
example : ∀ (P : Prop), P ∧ P ↔ P := 

Proof: We assume that P is an arbritrary 
proposition. Our goal is to prove P ∧ P ↔ P.
We can apply iff.intro whichs 
splits the ↔ connective into two implication 
arrows. This means we now have two
goals of P ∧ P → P and P → P ∧ P. 
To prove the goal P ∧ P → P, we first assume 
P ∧ P is true, and call the proof pp. We can
then construct a proof of P using (have p : P := and.elim_left pp). 
We can use this proof of P to prove P. Now we have to 
prove the second goal of P → P ∧ P. To prove this, 
we first assume P and our goald becomes P ∧ P. 
We can now apply the and introduction 
rule which shows if P ∧ P is true then P is true and 
P is true. Our goal is now to prove P. 
To prove P is true we use the assumption 
of the proof of P. In that context ∀ (P : Prop), P ∧ P ↔ P
is proven.

-/

example : ∀ (P Q : Prop), P ∨ Q ↔ Q ∨ P := 
begin
  assume P Q,
  apply iff.intro _ _,
  assume porq,
  cases porq,
  apply or.intro_right,
  exact porq,
  apply or.intro_left,
  exact porq,
  assume qp,
  cases qp,
  apply or.intro_right,
  exact qp,
  apply or.intro_left,
  exact qp,
end
/-
example : ∀ (P Q : Prop), P ∨ Q ↔ Q ∨ P :=

Proof: We assume that P and Q are arbitrary
propositions. Our goal is to prove 
P ∨ Q ↔ Q ∨ P. We can apply iff.intro
to make the goal P ∨ Q ↔ Q ∨ P split into two goals,
P ∨ Q → Q ∨ P ∧ Q ∨ P → P ∨ Q. To prove the
first goal of P ∨ Q → Q ∨ P, we first assume 
we have a proof (porq : P ∨ Q). We can do a case
analysis on porq, one case P is true and the other
case Q is true. In both cases we have to prove Q ∨ P. 
In the first case, where P is true, we can apply or.intro_right
to Q ∨ P, to simplify our goal to just prove P. We can then use 
the truth of this case, P, to prove P. In the other case, 
where Q is true, we can apply or.intro_left to Q ∨ P
to simplify our goal to just prove Q. Since this case has Q 
to be true, we can use that to prove Q. What is left to be
proven is Q ∨ P → P ∨ Q. We can assume we have a proof called
qp, that shows Q ∨ P is true. We can then run a case analysis 
on qp. In one case Q is true, and in the other case P is true. 
In both cases we have the goal of proving P ∨ Q. In the case 
where Q is true, we can apply or.intro_right to P ∨ Q, and then
use qp to prove Q. In the case where P is true we can apply
or.intro_left to P ∨ Q, and use qp to prove P. In that context 
∀ (P Q : Prop), P ∨ Q ↔ Q ∨ P is proven. 
-/

example : ∀ (P Q : Prop), P ∧ Q ↔ Q ∧ P := 
begin
  assume P Q,
  apply iff.intro _ _,
  assume pq,
  apply and.intro _ _,
  apply and.elim_right pq,
  apply and.elim_left pq,
  assume qp,
  apply and.intro _ _,
  apply and.elim_right qp,
  apply and.elim_left qp,
end
/-
example : ∀ (P Q : Prop), P ∧ Q ↔ Q ∧ P := 

Proof: First we assume P and Q are arbitrary 
propositions. We now have to prove P ∧ Q ↔ Q ∧ P.
We can apply iff.intro to make
our goal become proving two implications of 
P ∧ Q → Q ∧ P and Q ∧ P → P ∧ Q. To prove
P ∧ Q → Q ∧ P we first assume (pq : P ∧ Q) is 
true. We can then apply and.intro to make the goal
of proving Q ∧ P, into two seperate goals of proving
Q and proving P. To prove Q we can apply and.elim_right 
to pq, and similarly to prove P we can apply
and.elim_left to pq. What is left to be proven
is Q ∧ P → P ∧ Q. As with any implication, we start by 
assuming the premise is true (qp : Q ∧ P). We can then 
apply and.intro to make the goal of proving 
P ∧ Q turn into two seperate goals of proving P
and proving Q. We can then apply and.elim_right on 
qp to prove P, and apply and.elim_left on qp to
prove Q. In that context ∀ (P Q : Prop), P ∧ Q ↔ Q ∧ P
is proven. 
-/

example : ∀ (P Q R : Prop), P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) := 
begin
  assume P Q R,
  apply iff.intro _ _,
  assume pqr,
  have qr : (Q ∨ R) := and.elim_right pqr,
  apply or.elim qr,
  assume q,
  apply or.intro_left,
  have p : P := and.elim_left pqr,
  apply and.intro p q,
  assume r,
  apply or.intro_right,
  have p : P := and.elim_left pqr,
  apply and.intro p r,
  assume pqpr,
  apply and.intro,
  cases pqpr,
  apply and.elim_left pqpr,
  apply and.elim_left pqpr,
  apply or.elim pqpr,
  assume pq,
  apply or.intro_left,
  apply and.elim_right pq,
  assume pr,
  apply or.intro_right,
  apply and.elim_right pr,
end
/-
example : ∀ (P Q R : Prop), P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) := 

Proof: First we assume P, Q, and R are arbitrary propositions. 
Our goal is to prove P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R). We can 
apply iff.intro to split our goal into two implications. Our 
new goals are to prove P ∧ (Q ∨ R) → (P ∧ Q) ∨ (P ∧ R) and to
prove (P ∧ Q) ∨ (P ∧ R) → P ∧ (Q ∨ R). To prove 
P ∧ (Q ∨ R) → (P ∧ Q) ∨ (P ∧ R) we first assume we have a proof, 
call it pqr, of P ∧ (Q ∨ R). We can then contrust a proof Q ∨ R
using (have qr : (Q ∨ R) := and.elim_right pqr). We can then apply
or.elim to qr, which makes our goals turn into proving Q → (P ∧ Q) ∨ (P ∧ R)
and R → (P ∧ Q) ∨ (P ∧ R). To prove Q → (P ∧ Q) ∨ (P ∧ R), we first
assume Q (q : Q). We can then use or.intro_left to simplify
our goal to prove (P ∧ Q). We can construct a proof of P using
(have p : P := and.elim_left pqr), and then we can apply
and.intro to p and q to prove P ∧ Q. We now have to prove 
R → (P ∧ Q) ∨ (P ∧ R). To prove this, we first assume R is true
(r : R). We can then apply or.intro_right to simplify 
our goal to just prove (P ∧ R). We can construct a proof of P
again by using (have p : P := and.elim_left pqr, and then we 
can apply and.intro to p and r to prove P ∧ R. What is left
to be proven is P ∧ Q ∨ P ∧ R → P ∧ (Q ∨ R). To prove this
we first assume that we have a proof, pqpr, that
shows P ∧ Q ∨ P ∧ R is true. Now we have to prove P ∧ (Q ∨ R)
logically follows pqpr. To do this we can apply and.intro, which
splits our and proposition into two seperate propositions
of P and Q ∨ R. To prove P we can do a case analysis on pqpr. In 
one case P ∧ Q is true, and in another case P ∧ R is true. In 
both cases we have to prove P. In the case that P ∧ Q is true, 
we can apply and.elim_left on pqpr to get a proof of P. We
can then use that proof of P to prove P. In the case that P ∧ R
is true we can use and.elim_left on pqpr again to get a proof of P,
and use that proof of P to prove P. Now what is left to be
proven is Q ∨ R. We can apply or.elim on pqpr to make two 
implication propositions, where P ∧ Q → Q ∨ R and 
P ∧ R → Q ∨ R. To prove P ∧ Q → Q ∨ R we can assume we have a 
proof, pq, of P ∧ Q. We can then apply or.intro_left to simplify
the or proposition to just Q. We can then prove Q be applying 
and.elim_right to pq. Now we have P ∧ R → Q ∨ R left to prove. 
We can assume we have a proof, pr, of P ∧ R. We can then apply
or.elim_right on Q ∨ R, to simplify this or proposition to just 
R. We can then prove R by applying and.elim_right to P ∧ R. 
In that context ∀ (P Q R : Prop), P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R)
is proven. 

-/

example : ∀ (P Q R : Prop), P ∨ (Q ∧ R) ↔ (P ∨ Q) ∧ (P ∨ R) := 
begin
  assume P Q R,
  apply iff.intro _ _,
  assume pqr,
  apply and.intro _ _,
  apply or.elim pqr,
  assume p,
  apply or.intro_left,
  exact p,
  assume qr,
  apply or.intro_right,
  apply and.elim_left qr,
  apply or.elim pqr,
  assume p,
  apply or.intro_left,
  exact p,
  assume qr,
  apply or.intro_right,
  apply and.elim_right qr,
  -- backwards
  assume pqpr,
  have pq: (P ∨ Q) := and.elim_left pqpr,
  have pr: (P ∨ R) := and.elim_right pqpr,
  apply or.elim pq,
  assume p,
  apply or.intro_left,
  exact p,
  assume q,
  apply or.elim pr,
  assume p,
  apply or.intro_left,
  exact p,
  assume r,
  have qr : (Q ∧ R) := and.intro q r,
  apply or.intro_right,
  exact qr,
  
end

example : ∀ (P Q : Prop), P ∧ (P ∨ Q) ↔ P := 
begin
  assume P Q,
  apply iff.intro _ _,
  assume ppq,
  apply and.elim_left ppq,
  -- backwards
  assume p,
  apply and.intro _ _,
  exact p,
  apply or.intro_left,
  exact p,
end
/-
example : ∀ (P Q : Prop), P ∧ (P ∨ Q) ↔ P := 

Proof: We first assume P and Q are arbitrary
propositions. Our goal is to prove P ∧ (P ∨ Q) ↔ P.
We can apply iff.intro to make our goal
turn into two seperate goals of P ∧ (P ∨ Q) → P and
P → P ∧ (P ∨ Q). To prove P ∧ (P ∨ Q) → P, we first 
assume the premise is true (ppq : P ∧ (P ∧ Q)). 
Our goal is now to prove P, which we can do by 
apply and.elim_left to ppq, which returns a proof
of P. What is left to prove is P → P ∧ (P ∨ Q). 
First we assume P is true (p : P). We can then
apply and.intro to split the goal of P ∧ (P ∨ Q)
into proving P and proving P ∨ Q. To prove P we
use the assumption (p : P). To prove P ∨ Q
is true we can apply or.intro_left, because to prove 
P ∨ Q it suffices to just prove P. We can then use the 
assumption of P (p : P) to prove P. In that context
∀ (P Q : Prop), P ∧ (P ∨ Q) ↔ P is proven. 
-/

example : ∀ (P Q : Prop), P ∨ (P ∧ Q) ↔ P := 
begin
  assume P Q,
  apply iff.intro _ _,
  assume ppq,
  apply or.elim ppq,
  assume p,
  exact p,
  assume pq,
  apply and.elim_left pq,
  --backwards
  assume p,
  apply or.intro_left,
  exact p,
end

/-
example : ∀ (P Q : Prop), P ∨ (P ∧ Q) ↔ P := 

Proof: First we assume P and Q are arbitrary
propositions. Our main goal is to prove 
P ∨ (P ∧ Q) ↔ P. We can apply the iff.intro
to make our goal become two goals or proving 
P ∨ (P ∧ Q) → P and proving P → P ∨ (P ∧ Q). 
To prove P ∨ (P ∧ Q) → P we first assume 
P ∨ (P ∧ Q) is true, call it ppq. What is left 
to prove is P. We can use or.elim on ppq, to make
our goal become two implications of P → P and
P ∧ Q → P. To prove P → P we assume P and use that
assumption to prove P. To prove P ∧ Q → P, 
we assume (pq : P ∧ Q) is true, and we can 
apply and.elim_left on pq to get a proof of P. 
We can then use that proof of P to prove P. 
What is left to be proven is P → P ∨ (P ∧ Q). 
To prove this implication we assume P, and then apply 
or.intro_left to P ∨ (P ∧ Q) to simplify it
to proving just P, since proving either of the propositions
in an "or" statement is sufficient to prove the
whole statement. We can now use our assumption of P to prove
P. In that context ∀ (P Q : Prop), P ∨ (P ∧ Q) ↔ P
is proven. 
-/

example : ∀ (P : Prop), P ∨ true ↔ true := 
begin
  assume p,
  apply iff.intro _ _,
  assume ptrue,
  apply true.intro,
  assume true,
  apply or.intro_right,
  exact true,
end
/-
example : ∀ (P : Prop), P ∨ true ↔ true := 

Proof: First we assume P is an arbitrary proposition. 
Our goal is to prove P ∨ true ↔ true. We can split 
this goal into two goals using iff.intro. Now
our goals are to prove P ∨ true → true and to prove
true → P ∨ true. To prove P ∨ true → true, we can 
assume P ∨ true is true, and then apply true.intro
to prove true is true. What is left to be proven
is true → P ∨ true. To prove this we first assume true,
and then we can apply or.intro_right, which leaves
us with a goal of proving true. We can use our assumption
true to prove true, or use true.intro to prove true. 
In that context ∀ (P : Prop), P ∨ true ↔ true is proven.
-/

example : ∀ (P : Prop), P ∨ false ↔ P := 
begin
  assume P,
  apply iff.intro _ _,
  assume pf,
  cases pf,
  exact pf,
  cases pf,
  assume p,
  apply or.intro_left,
  exact p,
  
end
/-
example : ∀ (P : Prop), P ∨ false ↔ P := 

Proof: First we assume P is an arbitrary proposition.
Our goal is to prove P ∨ false ↔ P. We can apply
iff.intro to split this goal into two goals, 
leaving us with a goal of proving P ∨ false → P
and proving P → P ∨ false. To prove P ∨ false → p, 
we first assume P ∨ false is true, call it pf.
We can then use cases to do a case analysis on pf. 
In one case pf is true because of P, in another case
pf is true because of false. In both cases, P is left to
be proven. In the first case, we can prove P because this 
case is where P is true. In the second case, we can prove
P by doing cases on false. What is left to be proven is
P → P ∨ false. To prove this we assume P is true. We can
then apply or.intro_left and use our assumption of P 
to prove P. In that context ∀ (P : Prop), P ∨ false ↔ P
is proven. 
-/

example : ∀ (P : Prop), P ∧ true ↔ P := 
begin
  assume P,
  apply iff.intro _ _,
  assume pt,
  apply and.elim_left pt,
  assume p,
  apply and.intro,
  exact p,
  exact true.intro,

end

/-
example : ∀ (P : Prop), P ∧ true ↔ P := 

Proof: First we assume P is an arbitrary 
proposition. Our goal is to prove P ∧ true ↔ P. 
We can apply iff.intro to split out goal into two
seperate goals, one goal of proving P ∧ true → P, 
and another goal of proving P → P ∧ true. To prove
P ∧ true → P, we assume P ∧ true is true, call it pt. 
to prove P we can apply and.elim_left on pt, which 
gives us a proof of P. What is left to be proven is 
P → P ∧ true. We can prove this by assumming (p : P) is true.
We can then apply and.intro to make the goal of
procing P ∧ true into two seperate goals of proving 
P and proving true. To prove P we can use our assumption 
that P is true. To prove true we can use true.intro. 
In that context ∀ (P : Prop), P ∧ true ↔ P is proven. 
-/

example : ∀ (P : Prop), P ∧ false ↔ false := 
begin
  assume P,
  apply iff.intro _ _,
  assume pf,
  apply and.elim_right pf,
  --backwards
  assume f,
  apply and.intro,
  cases f,
  exact f,
  
end

/-
example : ∀ (P : Prop), P ∧ false ↔ false := 

Proof: First we assume P is an arbitrary proposition. 
Our goal is to prove P ∧ false ↔ false. We can
apply iff.intro to split out goal into two implications.
Our goals are now to prove P ∧ false → false, and to
prove false → P ∧ false. To prove P ∧ false → false, 
we can assume we have a proof, pf, of P ∧ false. We 
can then apply and.elim_right of pf to prove that false
follows this proposition. What is left to be proven is 
false → P ∧ false. To prove this we first assume false. We
can then apply and.intro to split out goal of proving 
P ∧ false, into two seperate goals of proving P, and 
a goal of proving false. To prove P we can use cases on our 
assumption of false. To prove false we can just use our
assumption of false. In that context 
∀ (P : Prop), P ∧ false ↔ false is proven. 

-/

