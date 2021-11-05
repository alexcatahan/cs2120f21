def cong_mod(n a b : ℤ) : Prop :=
∃ k, a - b = k * n 

example : cong_mod (4 : ℤ) (6 : ℤ) (14 : ℤ) :=
begin
  unfold cong_mod,
  apply exists.intro (-2 : ℤ) _,
  apply rfl,
end
