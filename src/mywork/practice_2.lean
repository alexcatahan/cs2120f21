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
  apply and.intro _ _,
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
  assume pqr,
  have p : P := and.elim_left pqr,
  have qr : (Q ∨ R) := and.elim_right pqr,
  apply or.elim qr,
  assume q,
  apply or.intro_left,
  apply and.intro p q,
  assume r,
  apply or.intro_right,
  apply and.intro p r,
  -- backwards junction,
  assume pqpr,
  apply and.intro _ _,
  apply or.elim pqpr,
  assume pq,
  apply and.elim_left pq,
  assume pr,
  apply and.elim_left pr,
  apply or.elim pqpr,
  assume pq,
  apply or.intro_left,
  apply and.elim_right pq,
  assume pr,
  apply or.intro_right,
  apply and.elim_right pr,
 
end

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

example : ∀ (P : Prop), P ∨ false ↔ P := 
begin
  assume P,
  apply iff.intro _ _,
  assume pf,
  apply or.elim pf,
  assume p,
  exact p,
  assume f,
  cases f,
  assume p,
  apply or.intro_left,
  exact p,

end

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

example : ∀ (P : Prop), P ∧ false ↔ false := 
begin
  assume P,
  apply iff.intro _ _,
  assume pf,
  apply and.elim_right pf,
  assume f,
  apply and.intro,
  
end


