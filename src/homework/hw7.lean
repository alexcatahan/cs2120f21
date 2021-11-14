import data.set
import tactic.ring

namespace relation

-- PRELIMINARY SETUP

/-
Preliminary set up. For the rest of this file,
we specify an arbitrary binary relation, r, on
an arbitrary type, β, as a two-place predicate, 
with infix notation x ≺ y for (r x y). One can
pronounce these expressions in English as "x is
related to y".
-/
variables {α β : Type}  (r : β → β → Prop)
local infix `≺` : 50 := r  


/-
The default Lean libraries are missing definitions
for the assympetric property of relations and for
the notion of a powerset. We define these terms for
use in the rest of this file.
-/
def asymmetric := ∀ ⦃x y⦄, x ≺ y → ¬ y ≺ x
def powerset (s : set β) := { s' | s' ⊆ s}


-- PROBLEMS

/- 
#1: Give both a formal and an English-language proof. Then
answer the question, is the proposition true if you remove
the first condition, that β is inhabited? Briefly explain
your answer (in English).
-/
example : (∃ (b : β), true) → asymmetric r → ¬reflexive r :=
begin
  assume h,
  cases h with w pf,
  unfold asymmetric,
  unfold reflexive,
  assume asymm,
  assume refl,
  have a := refl w,
  have b := asymm a,
  contradiction,
end
/-
English Proof: 
To prove that if a relation is asymmetric then
the relationship is not reflxive, it suffices to prove 
that for all x and y values of type β, if (x,y) is in the relation
then (y,x) is not in the relation, and in that context, there exists
an x value of type β such that (x,x) is not in the relation. We can 
prove this goal by proof by negation: we assume the premise is true
and then show it leads to a contradiciton. First, we assume
that the relation is asymmetric, then we assume it is reflexive. What
is left to be proven is false. We can prove false by apply the 
reflexive assumption to a β type, call it x, which gives us a proof that the 
pair x x is in the relation. We can build a contradiction by 
apply the assymetric assumption to the proof that x x is in the relation.
Once this contradiction is built, false is proven, and in that context
our goal is proven. 

The proposition is not true if you remove the first condition. 
This is because without the first condition an empty set would be a
valid relation. This would make the proposition not true because
universal generalization is always true over an empty set. Since assymetry
and reflexivity are both for all propositions, the can both be 
true over an empty set. 

-/



/-
#2. Logic, like programming, is subtle. It's very easy for humans
to miss subtle corner cases. As an example, today I ran across
a problem in a textbook by Paul Traiger, a professor emeritus
of philosophy and cognitive science at Occidental College. He
asks students to prove that if a relation is both transitive and 
reflexive that it cannot be anti-symmetric. See the question at
the very bottom of the page here:
https://sites.oxy.edu/traiger/logic/exercises/chapter13/properties_of_relations_exercise.html

Is the conjecture actually logically valid? If not, what condition 
needs to be added to make it so? Try prove this/his version of the
conjecture, as articulated slightly differently below. If you get
stuck, then you need to figure out an additional condition that needs 
to be added as a premise to make the proposition true. In that case,
add the premise and then show that the updated conjecture is true.
-/
-- I added the premise (∃ (b : β), true), because this conjecture is invalid if the set can be empty
example : (∃ (b : β), true) → transitive r → reflexive r → ¬ asymmetric r :=
begin
   unfold transitive reflexive asymmetric,
  assume h,
  assume trans,
  assume refl,
  assume asymm,
  cases h with w pf,
  have r_w_w := refl w,
  have notr_w_w := asymm r_w_w,
  contradiction,
end

/-
The conjecture is not logically valid. The condition that the relation
is inhabited is needed to make it valid. 
-/



/-
#3: Prove that the subset relation on the powerset of any
set, s, is antisymmetric. Formally state and prove, and
then give an informal proof of, this proposition.
-/
example : ∀ (s : set β) 
            (s1 s2 ∈ powerset s), 
            s1 ⊆ s2 → 
            s2 ⊆ s1 → 
            s1 = s2 :=
begin
  assume s s1 s2,
  assume s1ins s2ins,
  assume s1s2 s2s1,
  apply set.ext,
  assume x,
  split,
  assume xs1,
  have xins2 := s1s2 xs1,
  apply xins2,
  assume xins2,
  have xins1 := s2s1 xins2,
  assumption,

end
/-
Informal proof:
To prove that the subset relation on the powerset of any set, s,
is antisymetric it suffices to prove that if s1 and s2 are 
both in the powerset of s, and s1 is a subset of s2, and s2 is a subset 
of s1, then s1 must equal s2. To prove this goal we must prove
that an element, x, is in s1 if and only if x is in s2. Using our
assumptions, and elimination rules, we can apply our assumptions to
to prove if x is in s1 then x is in s2, because s1 is in subset of s2, 
and if x is in s2 then x is in s1, because s2 is a subset of s1. In this
context, it logically follows that s1 and s2 must be equal, and our goal
is proven. 
-/


/-
Given two natural numbers, n and m, we will say that m divides n
if there is a natural number, k, such that n = k*m. Here's a formal
definition of this relation.
-/
def divides (m n : ℕ) := ∃ k, n = k * m


/- 
#4: Formally and informally state and prove each of the following
propositions. Remember that the ring tactic is useful for producing
proofs of simple algebraic equalities involving + and *. You can use
the phrase, "by basic algebra" when translating the use of this tactic
into English. (Or if you wanted to be truly Hobbit-like you could say 
"by the ring axioms!")
-/

-- A: For any n, 1 divides n.
example : ∀ n, divides 1 n :=
begin
  assume n, 
  unfold divides,
  cases n,
  apply exists.intro 0,
  refl,
  apply exists.intro n.succ,
  ring,
end
/-
To prove that 1 divides any natural number, n, it 
suffices to prove than there exists a natural number, k,  such that
you can multiply k by 1 and it equals n. To prove this we can 
use do case analysis and then use the introduction rule for 
existential propositions with appopriate witnesses to help 
achieve our goals. In the first case, the natural number is zero, 
so we provide the witness of 0 and apply reflexivity to prove 0 = 0 *1.
In the second case we provide the witness of a succesive number, and 
by simple algebra the successive number equals the successive number 
times 1. If we show that this proposition is true for the successive number, 
it must be true for all numbers, so in this context our goal is proven.
-/

-- B. For any n, n divides n
example : ∀ n, divides n n :=
begin
  assume n,
  unfold divides,
  apply exists.intro 1,
  ring,
end
/-
To prove that any number, n, divides itself it suffices to 
show that any number is equal to itself multiplied by 1, or n = n * 1. 
By simply algebra we can prove this is true, and in that context our goal
is proven. 
-/

-- #C. prove that divides is reflexive 
example : reflexive divides :=
begin
  unfold reflexive divides,
  assume x,
  apply exists.intro 1,
  ring,
  
end 
/-
To prove to divides is reflexive we must show that 
for all natural numbers, x, there exists a factor, k, that 
equates x to itself. We do this by applying the introduction rule
for existential propositions, and providing the witness of 1. The 
rest can be proven with simple algebraic rules, and in this context
the reflexivitiy of divides is proven. 
-/

-- #D. prove that divides is transitive
example : transitive divides :=
begin
  unfold transitive divides,
  assume x y z,
  assume xy,
  assume yz,
  cases xy with k1 xdy,
  cases yz with k2 ydz,
  apply exists.intro(k2*k1),
  rw ydz,
  rw xdy,
  ring,
end 
/-
To prove the divides is trasitive we must show that if 
y is divisible by x, and z is divisible by y, then z is divisible
by x. We reach this goal by applying cases on existential assumptions, 
where there is only one case that that existential assumption is true, 
so we get two witnesses, k1 and k2, and two proofs that x divdes y and y divdes z. 
We can then apply the introduction rule for existential propositions, 
and provide it with the witness of k1*k2. By subsititing and simple algebraic 
rules, the rest of our goal can be proven, and in that context 
the transitivty of divdes is proven.
-/

/- 
E. Is divides symmetric? if yes, give a proof, otherwise 
give a counterexample and a brief explanation to show that 
it's not.
-/

/-
No, divides is not symmetric. If x is equated to y by a factor of k, 
then by simple alegra we conclude that y must be equated to x by a factor
of 1/k, which in all cases but 1, is not a natural number. 
This shows that divides is not symmetric and a counter example is 4 and 8. 
Counter example:

divides 4 8 -> 8 = k * 4 -> 2 = k
divides 8 4 -> 4 = k * 8 -> there exists no natural number to satisfy this proposition 
-/

/- 
#F. Prove that divides is antisymmetric. 
-/
example : anti_symmetric divides := 
begin  
  unfold anti_symmetric divides,
  assume x y xy yx,
  cases xy with w pf,
  cases yx with w2 pf2,
  rw pf,
  have foo : w = 1 := sorry,
  rw foo,
  ring,
end
/-
To prove that divides is antisymmetric we must show that if you have two 
natural numbers, x and y, and x divides y and y divides x, then x must equal 
y. To prove this we first assume that x divides y and y divides x. 
With these assumptions, we can apply the elimination rule for 
existential propositions to get the ingredients we need to 
prove that x equals y. Through this case analysis we know that, 
y equals x multiplied by a witness, call is w. Now we can rewrite our goal
to be x equals x times w. Since we know this equation is only true
if w is one, we have establish w to be one, and then by simple algebra 
our the rest of our goal, x = 1 * x, is proven. In this context, 
the antisymmetry of divides is proven. 
-/


/- #4
Prove the following propositions. Remember that
throughout this file, each definition implicitly
includes β as a type and r as an arbitrary binary 
relation on β. In addition to formal proofs, give
an English language proof of the last of the three
problems.
-/

-- A
example : asymmetric r → irreflexive r :=
begin
  unfold asymmetric irreflexive,
  assume asymm x k,
  have nk := asymm k,
  contradiction,
end
/-
The prove that if a relation is asymmetric than the relation 
is also irreflxive we must prove that if x and y is in the relation, 
then y and x is not in the relation, and in that context no element 
in the relation can be related to itself. We do this by assuming 
the premsis and applying our assumption of asymmetry to the assumption 
that x and x is in the realtion. The produces a contradiction, and in that 
context our goal is achieved. 
-/

-- B
example : irreflexive r → transitive r → asymmetric r :=
begin
  unfold irreflexive transitive,
  assume irrefl trans,
  assume x y,
  assume rxy,
  assume nryx,
  have f := trans rxy nryx,
  have nrxx := irrefl x,
  contradiction,
end
/-
To prove that if a relation is irreflexive and transitive than it is 
also asymmetric we use the assumption that the relation is transitive 
and apply it to the assumptions the x and y is in the relation and y 
and x is not in the relation, which produces a proof that x and x is 
in the relation. We can then build a contradiction by applying x of type 
β to the irreflexive assumption, which produces a proof that x and x
is not in the relation. This is a contradiction and in that context our 
goal is achieved. 
-/

-- C
example : transitive r → ¬ symmetric r → ¬ irreflexive r :=
begin
  unfold transitive symmetric irreflexive,
  assume trans symm irrefl,
  --stuck: see explanation below

end

/-
This proposition is false. The proof goal cannot be proceded 
because we have no existential assumption where which we can 
run case anlysis on to obtain witness that we need to further 
the proof. 

A counter example to this proposition is the less than relation. 
The less than relation is transitive, for example 1 is less than 2, and 
2 is less than 3, so 1 is less than 3. The less than relation is also
not symmetric, because 1 is less than 2 but 2 is not less than 1. 
and it is also irreflexive, because no number is less than itself. 

-/

end relation
