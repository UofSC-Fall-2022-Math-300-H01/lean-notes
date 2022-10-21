variable (α : Type) 
variable (a : α) 

#reduce @id α a

def f (n : Nat) : Nat := n + 1 

#check f 
#eval f 5 

def g : Nat → Nat := fun n => 100000^n 

#check g 
#eval g 2 

#check g ∘ f 
#eval (g ∘ f) 2
#eval g (f 2)

#eval (f ∘ g) 2

variable (β γ δ : Type)

theorem Assoc (f : α → β) (g : β → γ) (h : γ → δ) : 
  (h ∘ g) ∘ f = h ∘ (g ∘ f) := by 
    apply funext 
    intro a 
    rfl 
