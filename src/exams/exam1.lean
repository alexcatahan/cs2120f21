/- 
   *******************************
   PART 1 of 2: AXIOMS [50 points]
   *******************************
-/

/-
Explain the inference (introduction and
elimination) rules of predicate logic as
directed below. To give you guidance on
how to answer these questions we include
answers for some questions.
-/


-- -------------------------------------

/- #1: → implies [5 points]

INTRODUCTION

Explain the introduction rule for →. 

[We give you the answer here.]

In English: Given propositions, P and Q, 
a derivation (computation) a proof of Q 
from any proof of P, is a proof of P → Q.

In constructive logic, a derivation is a
given as a function definition. A proof
of P → Q literally is a function, that,
when given any proof of P as an argument
returns a proof of Q. If you define such
a function, you have proved P → Q.

ELIMINATION

Complete the definition of the elimination
rule for →.

(P Q : Prop) (p2q : P → Q) (p : P)
----------------------------------
            q : Q
-/

-- Give a formal proof of the following
example : ∀ (P Q : Prop) (p2q : P → Q) (p : P), Q :=
begin
  assume P Q,
  assume PimpQ,
  assumption,
end

-- Extra credit [2 points]. Who invented this principle?
/-
This principle was known as modus ponens and was
first described by a greek scholar names Theophrastus
-/
-- -------------------------------------


/- #2: true [5 points]

INTRODUCTION

Give the introduction rule for true using
inference rule notation.

[Here's our answer.]

---------- intro
(pf: true)

Give a brief English language explanation of
the introduction rule for true.

-- answer here:
/-
An axiom states that true has a single proof, 
true.intro, and therefore true is unconditionally
true
-/

ELIMINATION

Give an English language description of the
eliimination rule for true.

[Our answer]

A proof of true carries no information so
there's no use for an elimination rule.
-/

-- Give a formal proof of the following:

example : true := true.intro



-- -------------------------------------

/- #3: ∧ - and [10 points]

INTRODUCTION

Using inference rule notation, give the 
introduction rule for ∧.

[Our answer]

(P Q : Prop) (p : P) (q : Q)
---------------------------- intro
        (pq : P ∧ Q)

Given an English language description of
this inference rule. What does it really
say, in plain simple English. 

-- answer here:
/-
Given a proof of a proposition P, 
and a proof of another proposition Q,
you can construct a proof of the conjuction
P and Q (P ∧ Q).
-/

ELIMINATION

Give the elimination rules for ∧ in both
inference rule and English language forms.
-/
--answer:
/-
inference rule notation for ∧

(P Q : Prop) (pq : P ∧ Q)
-------------------------  ∧ elim (right)
          q : Q

(P Q : Prop) (pq : P ∧ Q)
-------------------------  ∧ elim (left)
          p : P

In English:
Given a proof of the conjuction P and 
Q is true, we know P is true, and we know Q is true. 
In lean, if we are given a proof that P ∧ Q
is true, we can construct a proof that the left
side of the conjuction is true (p : P), and we 
can also construct a proof the the right side
of the conjuction is true (q : Q). 

-/
/-
Formally state and prove the theorem that, 
for any propositions P and Q,  Q ∧ P → P. 
-/

example : ∀ (P Q : Prop), Q ∧ P → P := 
begin
  assume P Q QandP,
  exact and.elim_right QandP,
end




-- -------------------------------------

/- #4: ∀ - for all [10 points]

INTRODUCTION

Explain in English the introduction rule for ∀. If 
T is any type (such as nat) and Q is any proposition 
(often in the form of a predicate on values of the
given type), how do you prove ∀ (t : T), Q? What is
the introduction rule for ∀?

-- answer here:
/-
Assume we're given an arbitrary but specific
object of type T (t : T). If we prove that the 
proposition Q is true for t, then it follows
that the proposition Q is true for all objects
of type T. We can make the logical jump that 
if object t of type T satisfies the proposition Q
then that proposition is true for all objects
of type T because we made no assumptions 
whatsoever about t. 

The introduction rule for for all is that if
we can prove something of an arbitrary yet specific
object of type T, then it is true for all objects
of that type. 
-/

ELIMINATION

Here's an inference rule representation of the elim
rule for ∀. First, complete the inference rule by
filling in the bottom half, then Explain in English
what it says.

(T : Type) (Q : Prop), (pf : ∀ (t : T), Q) (t : T)
-------------------------------------------------- elim
                     q : Q 

-- English language answer here
/-
If you have a proof that for all objects of type T, 
the proposition Q is true, then you can apply 
that proof as a kind of function to any specific 
value of type T, say t, to produce a proof of the 
proposition Q. 
-/

Given a proof, (pf : ∀ (t : T), Q), and a value, (t : T),
briefly explain in English how you *use* pf to derive a
proof of Q.

-- answer here:
/-
You can use pf by *applying* the proof pf
to object t of type T, which returns a proof of Q. 
-/
-/


/-
Consider the following assumptions, and then in the
context of these assumptions, given answers to the
challenge problems.
-/

axioms
  (Person : Type)
  (KnowsLogic BetterComputerScientist : Person → Prop)
  (LogicMakesYouBetterAtCS: 
    ∀ (p : Person), KnowsLogic p → BetterComputerScientist p)
  -- formalizee the following assumptions here
  -- (1) Lynn is a person
  -- (2) Lynn knows logic
  -- add answer here (Lynn : Person)
  (Lynn : Person)
  -- add answer here (LynnKnowsLogic: KnowsLogic Lynn)
  (LynnKnowsLogic : KnowsLogic Lynn)
/-
Now, formally state and prove the proposition that
Lynn is a better computer scientist
-/
example : BetterComputerScientist Lynn  := 
begin
  apply LogicMakesYouBetterAtCS Lynn,
  exact LynnKnowsLogic,
end




-- -------------------------------------

/- #5: ¬ - not [10 points] 

The ¬ connective in Lean is short for *not*. Give
the short formal definition of ¬ in Lean. Note that
surround the place where you give your answer with
a namespace. This is just to avoid conflicting with
Lean's definition of not.
-/

namespace hidden
def not (P : Prop) := P → false -- fill in the placeholder
end hidden

/-
Explain precisely in English the "proof strategy"
of "proof by negation." Explain how one uses this
strategy to prove a proposition, ¬P. 
-/

-- answer here:
/-
To prove not P (¬P) by proof by negation, you assume
P is true and then you show that that assumption 
leads to some contradiction. This allows you to 
conclude P → false, or ¬P. 
-/

/-
Explain precisely in English the "proof strategy"
of "proof by contradiction." Explain how one uses
this strategy to prove a proposition, P (notice 
the lack of a ¬ in front of the P). 

Fill in the blanks the following partial answer:

To prove P, assume ¬P and show that this assumption leads to a contradiction.
From this derivation you can conclude ¬¬P.
Then you apply the rule of negation elimination
to that result to arrive a a proof of P. We have
seen that the inference rule you apply in the 
last step is not constructively valid but that it
is classicaly valid, and that accepting the axiom
of the law of excluded middle suffices to establish negation
elimination (better called double negation elimination)
as a theorem.
-/



-- -------------------------------------

/- 
#6: ↔ - if and only if, equivalent to [10 points]
-/

/-
ELIMINATION 

As with ∧, ↔ has two elimination rules. You can 
see their statements here.
-/
#check @iff.elim_left
#check @iff.elim_right

/-
Formally state and prove the theorem that 
biimplication, ↔, is *commutative*. Note: 
put parentheses around each ↔ proposition,
as → has higher precedence than ↔. Recall
that iff has both elim_left and elim_right
rules, just like ∧.
-/

example : ∀ (P Q : Prop), (P ↔ Q) → (Q ↔ P) :=
begin
assume P Q,
assume PbimpQ,
split,
cases PbimpQ with pimpq qimpp,
exact qimpp,
cases PbimpQ with pimpq qimpp,
exact pimpq,

end


/- 
   ************************************************
   PART 2 of 3: PROPOSITIONS AND PROOFS [50 points]
   ************************************************
-/

/- #7 [20 points]

First, give a fluent English rendition of
the following proposition. Note that the
identifier we use, elantp, is short for
"everyone likes a nice, talented person."
Then give a formal proof. Hint: try the
"intros" tactic by itself where you'd
previously have used assume followed by
a list of identifiers. Think about what
each expression means. 
-/

def ELJL : Prop := 
  ∀ (Person : Type) 
    (Nice : Person → Prop)
    (Talented : Person → Prop)
    (Likes : Person → Person → Prop)
    (elantp : ∀ (p : Person), 
      Nice p → Talented p → 
      ∀ (q : Person), Likes q p)
    (JohnLennon : Person)
    (JLNT : Nice JohnLennon ∧ Talented JohnLennon),
    (∀ (p : Person), Likes p JohnLennon) 
  /-
  Proposition in English:

  Person is a type. Nice takes a person and returns
  the proposition that that person is nice. 
  Talented takes a person and returns a 
  proposition that that person is talented. 
  Likes takes in two people and returns that
  the first person likes the second person.
  "elantp" is a proposition that states:

  For all people who are nice and talented,
  everybody likes them. Or, more fluently
  put, everybody likes all people who are
  nice and taleneted. John Lennon is 
  nice and talented, so therefore everybody must
  like John Lennon.
  -/

example : ELJL :=
begin
  unfold ELJL,
  assume person Nice Talented Likes elant JohnLennon JLNT p,
  apply elant,
  exact and.elim_left JLNT,
  exact and.elim_right JLNT,

end



/- #8 [10 points]

If every car is either heavy or light, and red or 
blue, and we want a prove by cases that every car 
is rad, then: 

-- how many cases will need to be considered? _4_
-- list the cases (informaly)
    -- answer here
    /-
    case 1 : heavy and red
    case 2 : light and red
    case 3 : heavy and blue
    case 4 : light and blue
    -/

-/

/-
  *********
  RELATIONS
  *********
-/


/- #9 [20 points]
Equality can be understood as a binary relation
on objects of a given type. There is a binary 
equality relation on natural numbers, rational 
numbers, on strings, on Booleans, and so forth.

We also saw that from the two axioms (inference
rules) for equality, we could prove that it is
not only reflexive, but also both symmetric and
transitive.

Complete the following definitions to express
the propositions that equality is respectively
symmetric and transitive. (Don't worry about
proving these propositions. We just want you
to write them formally, to show that you what
the terms means.)
-/

def eq_is_symmetric : Prop :=
  ∀ (T : Type) (x y : T), x = y → y = x

def eq_is_transitive : Prop :=
   ∀ (T : Type) (x y z : T), x = y → y = z → x = z



/-
  ************
  EXTRA CREDIT
  ************
-/

/- 
EXTRA CREDIT: State and prove the proposition
that (double) negation elimination is equivalent
to excluded middle. You get 1 point for writing
the correct proposition, 2 points for proving it
in one direction and five points for proving it
both directions. 
-/

def negelim_equiv_exmid : Prop := 
  ∀ (P : Prop), P → ¬¬P ↔ P ∨ ¬P

example : negelim_equiv_exmid:=
begin
  unfold negelim_equiv_exmid,
  assume P,
  apply iff.intro _ _,
  assume h,
  apply classical.em P,
  assume em,
  assume P,
  assume f,
  contradiction,
end


/- 
EXTRA CREDIT: Formally express and prove the
proposition that if there is someone everyone
loves, and loves is a symmetric relation, then 
thre is someone who loves everyone. [5 points]
-/

axiom Loves : Person → Person → Prop

example : (∃ (p : Person), ∀ (e : Person), Loves e p) ∧  
          (∀ (p p2 : Person), Loves p2 p → Loves p p2) →
          ∃ (s : Person), ∀ (e1: Person), Loves s e1 := 
begin
assume h,

end

