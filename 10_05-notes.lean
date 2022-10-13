-- Declare our domain of discourse 
variable (α : Type) 

-- Declare some predicates 
variable (P Q : α → Prop) 

#check ∀ (x:α), P x 

theorem test (x : α) : P x := sorry 

-- ∀ (x:α), P x is fun (x: α) => P x 
#check test 

-- Introduction rule is just to a map a function 
example : ∀ x, P x → P x := fun x => fun (h : P x) => h

-- Elimination rule is function application 
example (h₁ : ∀ x, P x → Q x) (h₂ : ∀ x, P x) : ∀ x, Q x := fun (x:α) => h₁ x (h₂ x)

-- Once more slowly in tactic mode 
example (h₁ : ∀ x, P x → Q x) (h₂ : ∀ x, P x) : ∀ x, Q x := by
  intro (x : α) 
  have g₁ : P x := by exact h₂ x 
  have g₂ : P x → Q x := by exact h₁ x 
  exact g₂ g₁

--  
#check ∃ (x:α), P x

#check exists (x:α), P x

-- ∃ introduction is a built-in structure
example (x:α) (h:P x) : ∃ y, P y := Exists.intro x h 

#check @Exists α 
#check @Exists.intro α 

-- Guess
#check @Exists.elim α 

example (h : ∃ y, ¬ P y) :  ¬ (∀ x, P x) := by 
  intro (g : ∀ x, P x)
  apply Exists.elim h 
  intro (a : α) 
  intro (l : ¬ P a)   
  exact l (g a) 

-- Equality: reflexivity, symmetry, and transitivity 
#check @Eq α 
#check @Eq.refl
#check @Eq.symm 
#check @Eq.trans

#check @rfl

-- Substituion for predicates 
#check @Eq.subst 

example (x y : α) (h : x = y) (g : P x) : P y := Eq.subst h g 

-- Substitution for functions 
example (β : Type) (x y : α) (h : x = y) (f : α → β) : f x = f y := congrArg f h 

#check @congrArg

-- Can use the rewrite tactic - rw 
example (β : Type) (x y : α) (h : x = y) (f : α → β) : f x = f y := by 
  rw [h]

example (x: α) : x=x := by 
  rfl 

variable (A B : Prop)
theorem not_true : A → B := sorry
#check not_true

example : ∀ (x : α), P x → ∃ (y : α), P y := by 
  intro (a : α)
  intro (h : P a)
  exact ⟨a, h⟩

variable (C : α → α → Prop) 

example : (∃ (x:α), ∀ (y:α), C x y) → ∀ (v:α), ∃ (u:α), C u v := by 
  intro h v 
  apply Exists.elim h 
  intro g f 
  apply Exists.intro 
  exact f v 

variable (P : α → Prop)

example : (¬ ∃ y, P y) → ∀ x, ¬ P x := by 
  intro h a n 
  exact h ⟨a,n⟩

example (f : α → α) (x y : α) (h₁ : x = y) (h₂ : P (f x)) : P (f y) := by 
  rw [h₁] at h₂ 
  assumption 

variable (x y z : α) 

example (h₁ : x = y) (h₂ : z = x) (f : α → α) : f y = f z := by 
  rw [← h₁, h₂] 
  -- calc
  --   f y = f y := by rfl 
  --   _ = f x := by rw [←h₁]
  --   _ = f z := by rw 
  --
example : (∀ x, P x → ¬ Q x) → ¬ ∃ y, P y ∧ Q y := by 
  intro h n 
  apply Exists.elim n 
  intro a g 
  exact h a g.left g.right 
