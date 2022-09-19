variable (A B : Prop)

example : ((A → B) → A) → A := by 
  intro (h : (A → B) → A)
  apply Or.elim (Classical.em A)
  intro (a : A)
  exact a 
  intro (n : ¬ A)
  have (f : A → B) := fun (a : A) => False.elim (n a)
  exact h f 

example : (A → B) → A := sorry -- this is not provable
