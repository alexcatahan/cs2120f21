axioms
(Ball : Type)
(blue : Ball → Prop)/-
Blue is a predicate, it takes an argument 
and gives a proposition back
-/
(allBallsBlue : ∀ (b : Ball), blue b)
(tomsBall : Ball)

theorem tomsBallsBlue : blue tomsBall :=
  allBallsBlue tomsBall

/-
eq.refl is the introduction rule for equality
substititibility is the eliminaion rule for equality
-/

def ev (n: ℕ) := n % 2 = 0
def odd (n : ℕ) := n%2 =1

def succesore_of_even_is_odd : Prop :=
∀ (n:ℕ), ev n → odd(n+1)

axioms (raining streets_wet : Prop)

axiom if_raining_then_streets_wet : raining → streets_wet

axiom pf_raining : raining

example : streets_wet :=

if_raining_then_streets_wet pf_raining

/-
elimination rule for implies is just you apply it to get a proof 
of the implication
-/

-- communitive means that if  (P ∧ Q) is true then  (Q ∧ P) is true
--associative means you can shift grouping for example,
--(P ∧ (Q ∧ R)) is true then ((P ∧ Q) ∧ R)

/-
To prove false:
1. if you have a variable/proof of type false you can exact that variable
2. if you have a proof of false you can apply the false elimination
rule is false on the proof of false
3. if you have 2 variables that provide a direct contradiction you
can prove false
-/

example: ∃ n :ℕ, n = 1 :=
begin 
exact exists.intro 1 rfl,
end

/-
proof by negation you are trying to prove not P, 
so you assume P and you have P implies false show you just show false

proof by contradicion youre trying to show P, 
so you assume not P, and show that not P leads to a 
contradiction which then proves not not P, 
and then you apply the negation elimination axiom 
to prove P
-/
