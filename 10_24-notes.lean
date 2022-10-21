variable { α β γ : Type }
-- variable (f : α → β) (g : β → γ) 

def Injective (f : α → β) : Prop := ∀ a₁ a₂, f a₁ = f a₂ → a₁ = a₂ 

def Surjective (f : α → β) : Prop := ∀ b, ∃ a, f a = b 

def Bijective (f : α → β) : Prop :=  Injective f ∧ Surjective f 

theorem comp_inj (f : α → β) (g : β → γ) (h : Injective (g ∘ f)) : Injective f := by 
  intro a₁ a₂ h₁ 
  have : g (f a₁) = g (f a₂) := congrArg g h₁ 
  exact h a₁ a₂ this 

theorem comp_surj (f : α → β) (g : β → γ) (h : Surjective (g ∘ f)) : Surjective g := by 
  intro c 
  have ⟨a,h₁⟩ : ∃ a, g (f a) = c := h c 
  exact ⟨f a, h₁⟩ 

def IsLeftInverse (f : α → β) (g : β → α) : Prop := g ∘ f = @id α 

def IsRightInverse (f : α → β) (g : β → α) : Prop := f ∘ g = @id β 

def IsInverse (f : α → β) (g : β → α) : Prop := IsLeftInverse f g ∧ IsRightInverse f g 

theorem left_inv_right_inv (f: α → β) (g : β → α) (h : IsLeftInverse f g) : IsRightInverse g f := by 
  exact h

def hasLeftInverse (f : α → β) : Prop := ∃ (g: β → α), IsLeftInverse f g 

def hasRightInverse (f : α → β) : Prop := ∃ (g : β → α), IsRightInverse f g 

theorem has_left_inv_injective (f : α → β) (h : hasLeftInverse f) : Injective f := by 
  intro a₁ a₂ l₁ 
  have ⟨g,l₂⟩ := h 
  have : (g ∘ f) a₁ = (g ∘ f) a₂ := congrArg g l₁
  rw [congrFun l₂] at this
  calc
    a₁ = id a₁        := by rfl 
    _  = (g  ∘ f) a₂  := this 
    _  = id a₂        := by rw [congrFun l₂] 

#check Classical.propDecidable

#check dif_pos 

theorem injective_has_left_inv (f : α → β) [l : Nonempty α] (h : Injective f) : hasLeftInverse f := by 
  have (a₀ : α) := Classical.choice l  
  let (g : β → α) := by 
    intro b 
    have : Decidable (∃ a, f a = b) := Classical.propDecidable (∃ a, f a = b)
    exact if s : ∃ a, f a = b then Classical.choose s else a₀  
  have : IsLeftInverse f g := by 
    apply funext 
    intro a 
    sorry 
  exists g 
  
