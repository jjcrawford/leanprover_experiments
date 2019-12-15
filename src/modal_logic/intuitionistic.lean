-- import modal_logic.modal
-- import modal_logic.frame_conditions

variable (W : Type)

inductive modal2
| box : modal2 → modal2
| diamond : modal2 → modal2
| arrow : modal2 → modal2 → modal2
| neg : modal2 → modal2
| and : modal2 → modal2 → modal2
| or : modal2 → modal2 → modal2
| atom : modal2 -- Atoms are (quoted) predicates (W → Prop)
open modal2

prefix `□`:20 := box
prefix `◇`:20 := diamond
notation `ϕ` := atom -- Maybe this is slightly better?
infix `=>`:20 := arrow
infix `or`:20 := or
infix `and`:20 := and

def modalrepr : modal2 → string 
| atom := "ϕ"
| (m1 and m2) := (modalrepr m1) ++ " and " ++ (modalrepr m2)
| (m1 or m2) := (modalrepr m1) ++ " or " ++ (modalrepr m2)
| (m1 => m2) := (modalrepr m1) ++ " => " ++ (modalrepr m2) 
| (neg m) := "neg " ++ (modalrepr m)
| □m := "□" ++ (modalrepr m)
| ◇m := "◇" ++ (modalrepr m)

instance : has_repr modal2 := ⟨modalrepr⟩


def dumbsahlqvist {R : W → W → Prop} : W → modal2 → (W → Prop) 
| w atom := λ x, x = w
| w (box m) := λ x, (∃ y, R y x ∧ (dumbsahlqvist y m x))
| w _ := sorry


#eval dumbsahlqvist w □ϕ



-- ϕ   : λ x, x = w
-- □ϕ  : λ x, R w x
-- ◇ϕ : λ x, R w x