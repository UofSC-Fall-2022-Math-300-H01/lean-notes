/- Comments -/

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
