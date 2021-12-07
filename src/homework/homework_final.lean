import algebra.algebra.basic tactic.ring
/-
Read, understand (collaborating if necessary) the material
in chapter 17 of Jeremy Avigad's *Logic and Proof.* It's here:
https://leanprover.github.io/logic_and_proof/the_natural_numbers_and_induction.html
-/

/-
The following problems are listed in the Problems section of 
the chapter. 

#1. Solve probem #1, first sentence only.
answer:
 
Principle of Complete Induction: Let P be any property that satifies the following:
for any natural number n, whenever P holds
of every number less than n, it also holds of n.
Then P holds of every natural number

 (P : ℕ → Prop), (∀ (n' : ℕ), ∀ (k : ℕ), k < n', (P k ∧ P n)) → ∀ (n : ℕ), P n

#2. Solve at least one of #2 and #3. Give
    detailed but informal proofs. 
Show that for every n, 0^2 + 1^2 + 2^2 +... n^2 = 1/6 n(1+n)(1+2n) 

informal proof:
First we show that this property is true for 0. This goal is rather trivial
since 0^2 = 1/6 n(1+n)(1+2n) -> 0 = 0. In other words, the case where the 
property is applied to 0 is true by reflexivity of equality. What is left
to be shown is that this property holds for the successor of any natural number,
n'. We do by assuming that we have the natural number n', and we assume that
we know this property is true for n', or 0^2 + 1^2 +...+ n'^2 = 1/6 n'(1+n')(1+2n'),
which is known as the induction hypothesis. If we expand our goal, that this 
property holds for the succesor of n', or P(n'), we get 
0^2 + 1^2 +...+ n'^2 +(n'+1)^2 = 1/6(n'+1)(1+(n'+1))(1+2(n'+1)). Using simple 
algebraic properties we can simplify and distrubute this goal to be
0^2 + 1^2 + ...+ n'^2 +(n'+1)^2 = 1/6(n'+1)(n'+2)(2n'+3). We then recognie that we
can rewrite our goal using our induction hypothesis, since our induction hypothesis
provides an equation for the sequence of terms being added to (n'+1)^2 in the 
left hand side of our goal. After this rewrite we are left to show that
1/6 n'(1+n')(1+2n') + (n'+1)^2 = 1/6(n'+1)(n'+2)(2n'+3). To prove this equality is 
true we will focus on using alegraic rules to manipulate the left hand side. 
First, we can factor out a 1/6 from both terms that are being added, which 
will leave us with 1/6(n'(1+n')(1+2n') + 6(n'+1)^2). We can then expand the
quadratric term to be (n'+1)(n'+1), and this allows us to factor out a
(n'+1) from the entire quantity, which leaves us with 
1/6(n'+1)(n'(1+2n') + 6(n'+1)). By simple algebra, (n'(1+2n') + 6(n'+1)) 
can be re written as (2n'+4n'+3n'+6), which then can be easily seen as factorable
an can be re wrttein as (2n'+3)(n'+2). Using these insights we can rewrite 
1/6(n'+1)(n'(1+2n') + 6(n'+1)) as 1/6(n'+1)(2n'+3)(n'+2). Revisting our 
goal expression we get 1/6(n'+1)(2n'+3)(n'+2) = 1/6(n'+1)(n'+2)(2n'+3), and since
multiplication is communative, the left hand side equals the right hand side and
our goal is proven. 
-/




/-
To test out of the final exam ...

#1: Give a formal proof for #2 or #3.

#2: Formal or detailed informal proofs 10-13

#3 (Extra Credit): #5 or #9

NOT FINALIZED. ADVISORY. 
-/

-- formal proof for #2:
def sum_to_of_squares : ℕ → ℕ
| (nat.zero) := nat.zero
| (nat.succ n') := (sum_to_of_squares n') + (nat.succ n') * (nat.succ n')

def P : ℕ → Prop := 
  λ n,  6 * sum_to_of_squares n
   = n * (1+n) *(1+2*n)

def conjecture := ∀ n, P n

theorem sum_to_opt : conjecture := 
begin
  unfold conjecture,
  assume n,
  unfold P,
  induction n with n' ih_n',
  apply rfl,
  simp [sum_to_of_squares],   
  rw mul_add, 
  rw ih_n',   
  rw nat.succ_eq_add_one,
  ring,
end

-- 10: multiply by 1

example: ∀ (n: ℕ), 1 * n = n :=
begin 
    assume n,
    induction n with n' ihn',
    refl,
    rw nat.succ_eq_add_one,
    rw mul_add,
    rw ihn',
    refl,
end

--11: distribute 

example: ∀ (m n k : ℕ), m * (n + k) = m * n + m * k :=
begin 
    assume m n k,
    induction m with m' ihm',
    simp[nat.add],
    rw nat.succ_eq_add_one,
    rw mul_add,
end

-- 12: associativity of mulplication

example: ∀ (m n k  : ℕ), (m * n) * k = m * (n * k):=
begin
    assume m n k,
    induction k with k' ihk',
    simp[nat.add],
    rw nat.succ_eq_add_one,
    rw mul_add,
    rw mul_add,
    rw mul_add,
    simp[nat.add],
    rw ihk',
end

--13:communativity of multiplication

example: ∀(m n : ℕ), m * n = n * m :=
begin
    assume m n,
    induction n with n' ihn',
    simp[nat.add],
    rw nat.succ_eq_add_one,
    rw mul_add,
    simp[nat.add],
    rw ihn',
    rw right_distrib,
    simp[nat.add],
end

--extra credit #5:
