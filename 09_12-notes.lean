variable (A B C : Prop)
-- This is variable 

variable (w : A)
/- 
This is a 
multi-line 
comment telling us 
that w : A means 
w is a proof of the 
proposition A
-/

#check w

-- Negation 

#check Not A 
#check ¬ A -- \neg 
#check Not 

-- Implication 

#check A → B -- \to 
#check A -> B  

-- Conjunction 

#check And A B 
#check A ∧ B -- \and 

-- Disjunction 

#check Or B C
#check B ∨ C -- \or 

-- Bi-implication 

#check A ↔ B  -- \iff

variable (D : Prop)

#check (A ↔ B) ∧ C ∨ D  

-- Truth and falsity 

#check False 
#check True 

theorem myTheorem : True := True.intro 

example : True := trivial 

#check trivial 

