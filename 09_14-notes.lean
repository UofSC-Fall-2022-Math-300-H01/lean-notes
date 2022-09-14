variable (A B C : Prop)

example : A ∧ B := sorry 

example : ¬ A := sorry 

example : A ∨ B := sorry 

example : A → B := sorry 

example : A ↔ B := sorry 

-- Elimination and introduction for → 

example (a : A) : A := a 

example : True := trivial 

example : A → A := fun (a:A) => a 

theorem myAwesomeTheorem ( a : A ) : B :=
sorry 

#check myAwesomeTheorem A B 

-- introduction 
example : A → B := myAwesomeTheorem A B 

-- elimination
example (a : A) (f : A → B) : B := f a 

example : A → B → A := fun (a : A) => 
fun (_ : B) => a

-- Elimination and introduction for ∧ 

example (p : A ∧ B) : A := And.left p 

example (p : A ∧ B) : B := And.right p 

#check And.left 

example (a : A) (b : B) : A ∧ B := And.intro a b 

#check And.intro 

-- Elimination and introduction for ∨ 

example (a : A) : A ∨ B := Or.inl a 

example (b : B) : A ∨ B := Or.inr b 

#check Or.elim

example (h : A ∨ B) : B ∨ A := 
  Or.elim h (Or.intro_right B) (Or.intro_left A) 

-- Elimination and introduction for \iff 

example (f : A → B) (g : B → A) : A ↔ B := 
  Iff.intro f g 

example (h : A ↔ B) (a : A) : B := Iff.mp h a 

example (h : A ↔ B) (b : B) : A := Iff.mpr h b 

#check @Iff.mpr A B 