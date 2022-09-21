example (A B C : Prop) : (A → B) → (B → C) → (A → C) := by
  intro (h₁: A → B)
  intro (h₂: B → C)
  intro (a : A)
  have (b : B) := by exact h₁ a
  exact h₂ b 

#check @And.intro 

example (A B : Prop) (a : A) (b : B) : A ∧ B := by 
  apply And.intro 
  exact a 
  exact b 


