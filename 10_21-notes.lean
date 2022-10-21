def f : Nat → Nat := fun n => 2*n^3 + 4*n + 3
def g (n : Nat) : Nat := n^2 + 1 

#check g ∘ f 
#eval f 1 
#eval g (f 1) 
#eval (g ∘ f) 1 

#eval f (g 1)

variable (α β γ δ : Type) 
variable (f : α → β) (g : β → γ) (h : γ → δ) 

theorem Assoc : (h ∘ g) ∘ f = h ∘ (g ∘ f) := by 
  apply funext 
  intro x 
  rfl 

theorem comp_id : f ∘ (@id α) = f := by 
  apply funext 
  intro x 
  rfl 

theorem id_comp : (@id β) ∘ f = f := by 
  apply funext 
  intro x 
  rfl 

variable (f₁ f₂ : α → β) 

#check @congrFun
#check @congrArg 

example (h : f₁ = f₂) (a : α) : f₁ a = f₂ a := by 
  exact congrFun h a  

example (h : ∃ a, f₁ a ≠ f₂ a) : f₁ ≠ f₂  := by 
  intro n 
  have ⟨a,h₁⟩ := h 
  have : f₁ a = f₂ a := congrFun n a 
  exact h₁ this 



