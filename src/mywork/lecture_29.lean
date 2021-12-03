import algebra.algebra.basic tactic.ring

namespace hidden

inductive nat : Type
| zero : nat 
| succ (n' : nat) : nat

def z := nat.zero

#check z
#reduce z

def o := nat.succ(z)

#check o
#reduce o

def t := nat.succ(o)

#check t
#reduce t

def f : nat := 
begin
  exact nat.succ (nat.succ t),
  --the successor of the succesor of two
end

def inc' : nat → nat :=
begin
  assume n,
  exact nat.succ n,
  --this is scripting language
end

#check inc' f
#reduce inc' f 


def inc : nat → nat 
| n := nat.succ n --this is function definition notation

def dec : nat → nat
| (nat.zero) := nat.zero --if you want to decrement 0 then just return 0
| (nat.succ n') := n' --decrement a number other than 0 find the number, that number is the succesor of some number so retutn that number

def add : nat → nat → nat
| (nat.zero) (m) := m
| (nat.succ n') (m) := nat.succ(add n' m)
  /-answer for n' -/
  --know the answer for n' plus m so the succesor of n' plus m is just the succesor of that answer
  
def mul : nat → nat → nat
|(nat.zero) (m) := nat.zero
|(nat.succ n') (m) := add (m) (mul n' m)
/-n' m (mul nat.mul n' m)-/

def exp : nat → nat → nat
| (nat.zero) (m) := nat.zero
| (m) (nat.zero) := nat.zero.succ
|(n') (nat.succ m') := mul (n') (exp n' m')


theorem sum_to : nat → nat
|(nat.zero) := nat.zero
|(nat.succ n') := add (sum_to n') (n'.succ)

#reduce sum_to f

def P : nat → Prop 
| n := sum_to n = mul n (inc n)



theorem foo : ∀ (n : nat), P n

end hidden