-- 1
example : 0 ≠ 1 :=
begin
  -- ¬ (0 = 1)
  -- (0 = 1) → false
  assume h,
  cases h,
end


-- 2
example : 0 ≠ 0 → 2 = 3 :=
begin
  assume h,
  have f : false := h (eq.refl 0),
  exact false.elim (f),
end

-- 3
example : ∀ (P : Prop), P → ¬¬P :=
begin
  assume P,
  assume (p : P),
  -- ¬¬P
  -- ¬P → false
  -- (P → false) → false
  assume h,
  have f := h p,
  exact f,
end 

-- We might need classical (vs constructive) reasoning 
#check classical.em
open classical
#check em

/-
axiom em : ∀ (p : Prop), p ∨ ¬p

This is the famous and historically controversial
"law" (now axiom) of the excluded middle. It's is
a key to proving many intuitive theorems in logic
and mathematics. But it also leads to giving up on
having evidence *why* something is either true or
not true, in that you no longer need a proof of 
either P or of ¬P to have a proof of P ∨ ¬P.
-/

-- 4
theorem neg_elim : ∀ (P : Prop), ¬¬P → P :=
begin
  assume P,
  assume h,
  have pornp := classical.em P,
  cases pornp with p pn,
  assumption,
  contradiction,
end

-- 5
theorem demorgan_1 : ∀ (P Q : Prop), ¬ (P ∧ Q) ↔ ¬ P ∨ ¬ Q :=
begin
  assume P Q,
  apply iff.intro,
  assume npq,
  have pornp := classical.em P,
  have qornq := classical.em Q,
  cases pornp,
  cases qornq,
  have pq : (P ∧ Q) := and.intro pornp qornq,
  contradiction,
  apply or.intro_right,
  exact qornq,
  apply or.intro_left,
  exact pornp,
  assume npnq,
  cases npnq,
  assume h,
  cases h with p q,
  have f := npnq p,
  exact f,
  assume h,
  cases h with p q,
  exact false.elim(npnq q), 
  
end


-- 6
theorem demorgan_2 : ∀ (P Q : Prop), ¬ (P ∨ Q) → ¬P ∧ ¬Q :=
begin
  assume P Q,
  assume npq,
  split,
  have pornp := classical.em P,
  cases pornp with p np,
  have porq := or.intro_left Q p,
  contradiction,
  exact np,
  have qornq := classical.em Q,
  cases qornq with q nq,
  have porq := or.intro_right P q,
  contradiction,
  exact nq,

end


-- 7
theorem disappearing_opposite : 
  ∀ (P Q : Prop), P ∨ ¬P ∧ Q ↔ P ∨ Q := 
begin
  assume P Q,
  apply iff.intro,
  assume pornpq,
  cases pornpq with p npq,
  apply or.intro_left,
  exact p,
  apply or.intro_right,
  have q : Q := and.elim_right npq,
  exact q,
  assume porq,
  have pornp := classical.em P,
  cases pornp,
  apply or.intro_left,
  exact pornp,
  cases porq,
  apply or.intro_left,
  exact porq,
  apply or.intro_right,
  have npq: (¬P ∧ Q) := and.intro pornp porq,
  exact npq,
  
end


-- 8
theorem distrib_and_or : 
  ∀ (P Q R: Prop), (P ∨ Q) ∧ (P ∨ R) ↔
                    P ∨ (Q ∧ R) :=
begin
  assume P Q R,
  apply iff.intro,
  assume pqpr,
  have porq := and.elim_left pqpr,
  have porr := and.elim_right pqpr,
  cases porq,
  apply or.intro_left,
  exact porq,
  cases porr,
  apply or.intro_left,
  exact porr,
  apply or.intro_right,
  have qr : (Q ∧ R) := and.intro porq porr,
  exact qr,
  --backwards
  assume pqr,
  apply and.intro _ _,
  cases pqr,
  apply or.intro_left,
  exact pqr,
  apply or.intro_right,
  exact and.elim_left pqr,
  cases pqr,
  apply or.intro_left,
  exact pqr,
  apply or.intro_right,
  apply and.elim_right pqr,

end

-- remember or is right associative
-- you need this to know what the lefts and rights are
-- 9
theorem distrib_and_or_foil : 
  ∀ (P Q R S : Prop),
  (P ∨ Q) ∧ (R ∨ S) ↔
  (P ∧ R) ∨ (P ∧ S) ∨ (Q ∧ R) ∨ (Q ∧ S) :=
begin
  assume P Q R S,
  apply iff.intro,
  assume pqrs,
  cases pqrs with porq rors,
  cases porq,
  cases rors,
  apply or.intro_left,
  exact and.intro porq rors,
  apply or.intro_right,
  apply or.intro_left,
  exact and.intro porq rors,
  cases rors,
  apply or.intro_right,
  apply or.intro_right,
  apply or.intro_left,
  exact and.intro porq rors,
  apply or.intro_right,
  apply or.intro_right,
  apply or.intro_right,
  exact and.intro porq rors,
  -- backwards
  assume h,
  split,
  cases h,
  apply or.intro_left,
  apply and.elim_left h,
  cases h,
  apply or.intro_left,
  apply and.elim_left h,
  cases h,
  apply or.intro_right,
  apply and.elim_left h,
  apply or.intro_right,
  apply and.elim_left h,
  cases h,
  apply or.intro_left,
  apply and.elim_right h,
  cases h,
  apply or.intro_right,
  apply and.elim_right h,
  cases h,
  apply or.intro_left,
  apply and.elim_right h,
  apply or.intro_right,
  apply and.elim_right h,

end


/- 10
Formally state and prove the proposition that
not every natural number is equal to zero.
-/
lemma not_all_nats_are_zero : ¬∀ (n : ℕ), n = 0 :=
begin
  assume n,
  
  
end 

-- 11. equivalence of P→Q and (¬P∨Q)
example : ∀ (P Q : Prop), (P → Q) ↔ (¬P ∨ Q) :=
begin
  assume P Q,
  apply iff.intro,
  assume pimpq,
  have pornp := classical.em P,
  cases pornp with p np,
  apply or.intro_right,
  have q := pimpq p,
  exact q,
  -- backwards
  apply or.intro_left,
  exact np,
  assume npq,
  assume p,
  apply or.elim npq,
  assume np,
  have f := np p,
  apply false.elim(f),
  assume q,
  exact q,

end

-- 12
example : ∀ (P Q : Prop), (P → Q) → (¬ Q → ¬ P) :=
begin
  assume P Q,
  assume pimpq,
  assume nq,
  have pornp := classical.em P,
  cases pornp,
  have q := pimpq pornp,
  have f := nq q,
  apply false.elim(f),
  exact pornp,

end

-- 13
example : ∀ (P Q : Prop), ( ¬P → ¬Q) → (Q → P) :=
begin
  assume P Q,
  assume npnq,
  assume q,
  have pornp := classical.em P,
  apply or.elim pornp,
  assume p,
  exact p,
  assume np,
  have nq := npnq np,
  have f := nq q,
  apply false.elim(f),
  
end

