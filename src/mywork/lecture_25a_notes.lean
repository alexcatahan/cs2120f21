import .lecture_24_notes

/-
BASIC SETUP
-/
namespace relations
section relation

/-
Define relation, r, as two-place predicate on 
a type, β, with notation, x ≺ y, for (r x y). 
-/
variables {α β γ : Type}  (r : β → β → Prop)
local infix `≺`:50 := r  

/-
ORDERING RELATIONS ON A TYPE, β 
-/

def strict_ordering :=  asymmetric r ∧ transitive r
--asymmetric: if a is realted to be then b cannot be related to a
--example of strict order is less than, and another example is greater than
--a realtion that is strict ordering is not reflexvie
-- looks like:
--             -> -> -> -> -> ->            
def ordering :=         reflexive r ∧ transitive r ∧ anti_symmetric r


def partial_order :=    reflexive r ∧ transitive r ∧ anti_symmetric r ∧ ¬strongly_connected r


def total_order :=      reflexive r ∧ transitive r ∧ anti_symmetric r ∧ strongly_connected r

end relation
end relations

/-
well order: the realtion r is a well ordering of a set
if its a total order
and if you pick any subset of the set on which you have a relation,
any subset has to have a least element, the lowest element

well order.
-/

def well_ordering := total_order r ∧ 
(
  ∀ (s :set β),
  ∃ (b : β),
    (∀ (b' : β), b' ∈ S →  b ≺ b')

)