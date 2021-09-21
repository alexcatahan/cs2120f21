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
has no proofs at all. It's a type without any values
which is called an uninhabited type.
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

example : ∀ (P : Prop), P ∧ P ↔ P := 
begin
   assume P,
  apply iff.intro _ _,
  assume pp,
  apply and.elim pp,
  assume p,
  assume p,
  exact p,
  assume p,
  split,
  exact p,
  exact p,

end

example : ∀ (P Q : Prop), P ∨ Q ↔ Q ∨ P := 
begin
    assume P Q,
  apply iff.intro _ _,
  assume porq,
  apply or.elim porq,
  assume p,
  apply or.intro_right,
  exact p,
  assume q,
  apply or.intro_left,
  exact q,
  assume qorp,
  apply or.elim qorp,
  assume q,
  apply or.intro_right,
  exact q,
  assume p,
  apply or.intro_left,
  exact p,
end

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

example : ∀ (P Q R : Prop), P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) := 
begin
    assume P Q R,
  apply iff.intro _ _,
  assume p,
  cases p with p QorR,
  apply or.intro_left,
  apply and.intro _ _,
  cases QorR with q r,
  exact p,
  exact p,
  apply or.elim QorR,
  assume q,
  exact q,
  assume r,
end

example : ∀ (P Q R : Prop), P ∨ (Q ∧ R) ↔ (P ∨ Q) ∧ (P ∨ R) := 
begin
end

example : ∀ (P Q : Prop), P ∧ (P ∨ Q) ↔ P := 
begin
end

example : ∀ (P Q : Prop), P ∨ (P ∧ Q) ↔ P := 
begin
end

example : ∀ (P : Prop), P ∨ true ↔ true := 
begin
end

example : ∀ (P : Prop), P ∨ false ↔ P := 
begin
end

example : ∀ (P : Prop), P ∧ true ↔ P := 
begin
end

example : ∀ (P : Prop), P ∧ false ↔ false := 
begin
end


