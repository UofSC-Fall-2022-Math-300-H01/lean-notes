/- Comments -/


import Lean.Parser.Term

#check Prop 

variable (A B C D E : Prop)

#check D 

/- truth and falsity -/

#check True 
#check False 

/- Connectives -/ 

/- Negation -/ 

#check ¬ A 
/- type \neg -/ 
#check Not  
#reduce ¬ A 

/- Implication -/ 

def Implies (P Q : Prop) : Prop := P → Q 
#check A → B 
#check Implies A B
/- \to  -/
#check A -> B 

/- And -/

#check And A B 
#check A /\ B
#check A ∧ B 
/- \and -/ 

/- Or -/ 

#check Or A B 
#check A \/ B 
#check A ∨ B 
/- \or -/

/- Bi-implication -/

#check Iff A B 
#check A ↔ B 
#check Iff 
/- \iff -/

/- Examples -/

#check A ∧ B → C 
#check ¬ A ∨ C ↔ A → B 
#check (A → B) → False  

#check Classical.em A
#check em A

/- What is a proof? -/ 

variable (h : A) 

#check h 

example (h : A) : A := h

theorem identity (h : A) : A := h 

variable {G H : Prop}

theorem superProof (h : G) : H := sorry 

#check superProof

example : A → B := fun (h : A) => (superProof h)

#check And

#check Or.elim
#check Or.inl 
example (h : A ∨ B) : B ∨ A := Or.elim h (fun (a:A) => Or.inr a) _ 

#reduce Not A 

#check Iff.intro

open Lean Parser Term
macro "assume " var:funBinder ", " exp:term : term => `(fun $var => $exp)

#check assume (a:A)

example : (A → A) := 
  assume (a : A), a
  show A from a 

example (h : A → B ∧ C) : A → C := fun (a : A) => And.right (h a)

example : A ∧ B → A ∨ B := fun (p : A ∧ B) => Or.inl (And.left p)

example  (h : A ∧ B) : (B ∧ B) := And.intro (And.right h) (And.right h)

example : (A → B) → (¬ B → ¬ A) := 
  fun (f: A → B) => fun (h : ¬ B) => fun (a : A) => h (f a) 

#check @Classical.byContradiction A  

example : ¬ ¬ A → A := fun (h : ¬ ¬ A) => Classical.byContradiction (fun (n : ¬ A) => h n) 

#check Classical.em

#check False.elim  

example (h : ¬ B → ¬ A) : (A → B) := 
  Or.elim (Classical.em B) (fun (b : B) (_ : A) => b) (fun (n : ¬ B) (a : A) => False.elim (h n a)) 

example : False := by sorry 

example (A B C : Prop) : (A → B ∧ C) → (A → B) ∧ (A → C) := by 
  intro (h : A → B ∧ C)
  have (f : A → B) := fun (a:A) => And.left (h a)
  have (g : A → C) := fun (a:A) => And.right (h a)
  exact And.intro f g  

example (a : A) (b : B) : A ∧ B := by
  apply And.intro
  case left => exact a
  case right => exact b 

example (h : A ∨ B) : B ∨ A := by 
  cases h with 
  | inl a => exact Or.inr a
  | inr b => exact Or.inl b 

example (p q : Prop) (h : p ∨ q): q ∨ p := by
  cases h with
  | inr hq => apply Or.inl; exact hq
  | inl hp => apply Or.inr; exact hp 