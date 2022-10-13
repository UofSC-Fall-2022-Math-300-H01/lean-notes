variable (α : Type) 

variable (A B : α → Prop) 

variable (C : α → α → Prop) 

theorem totally_fake (A : Prop) : A := sorry 

#check totally_fake

-- ∀ \forall for universal quantifier

example (h : ∀ (x:α), A x) (a : α) : A a := h a 

example : ∀ x, A x → A x := fun (x:α) (h: A x) => h 

-- ∃ \exists for existential quantifier 

#check @Exists α 

#check @Exists.intro 

#check @Exists.elim 

-- = equality 

#check @Eq α 

#check @Eq.refl α 

#check @Eq.symm α 

#check @Eq.trans α 

#check @Eq.subst α A 

variable (f: α → β) 
variable (x y : α)
variable (h : x = y)

#check @congrArg α β x y f 

#check congrArg f h 





