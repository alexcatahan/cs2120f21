
/-
A simple predicate.
-/
def ev (n : ℕ) : Prop := n%2=0


/-
Introduction rule for exists
-/
example : exists (n : ℕ), ev n :=
begin
end

example : exists n, ev n := _


example : exists (a b c : ℕ), a*a + b*c = c*c := 
_


example : ∀ (n : ℕ), ∃ (m : ℕ), n = 2 * m :=
begin
  intros,
  apply exists.intro _,
end

example : ∀ (m : ℕ), ∃ (n : ℕ), n = 2 * m :=
begin
  intros,
  apply exists.intro (2*m),
end

example : (∃ (n : nat), ev n) → true :=
begin
assume h,
cases h with v pf,
intros,
end

/- 
Introduction rule for exists: you need a witness and a proof
Elimination rule: the thing must exists so you can get 
it a name and you can use whatever you name it as the 
witness in the rest of my reasoning
In class exercises:
writing the definition of a predicate in lean syntax
-/

def pt (a b c: ℕ): Prop :=
a * a + b * b = c * c
example: pt 3 4 5 := 
begin
  unfold pt,
  apply eq.refl,
end
example : pt 3 4 6 :=
begin
  unfold pt,
  
end

/-

-/

