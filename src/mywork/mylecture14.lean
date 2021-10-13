axioms
  (Person : Type)
  (Likes : Person → Person → Prop) 
  --likes is a binary relation between two objects of type person
  --two place predicate to represent a binary relation
example :
  ¬(∀ p : Person, Likes p p) ↔
 ∃ p : Person, ¬ Likes p p :=
begin
  split,
  assume h,
  have f := classical.em(∃ (p : Person), ¬ Likes p p),
  cases f with t f,
  exact t,
  have contra : ∀ (p : Person), Likes p p := _,
  contradiction,
  assume p,
  have g := classical.em (Likes p p),
  cases g,
  exact g,
  have a : ∃ (p:Person), ¬Likes p p := exists.intro p g,
  contradiction,
  assume h,
  cases h with p pf,
  assume h1,
  have f := h1 p,
  contradiction,
  
  





  
  
  
  

  
  
end
