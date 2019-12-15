/-
Copyright (c) 2019 Jack Crawford. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack Crawford

* Here we define modal formulae and 
-/


import modal_logic.frame_conditions
import tactic.rcases

variable W : Type -- Type of possible worlds

inductive modal
| neg : modal → modal
| box : modal → modal
| diamond : modal → modal
| and : modal → modal → modal
| or : modal → modal → modal
| arrow : modal → modal → modal
| atom : (W → Prop) → modal -- Atoms are (quoted) predicates (W → Prop)

open modal

prefix `not`:25 := neg
prefix `□`:25 := box
prefix `◇`:25 := diamond
notation `[`p`]` := atom p -- Maybe this is slightly better?
infix `or`:23 := or
infix `and`:23 := and
infix `=>`:20 := arrow


instance {W : Type} : has_neg (modal W) := ⟨modal.neg⟩

def modalrepr : modal W → string 
| [ϕ] := "ϕ"
| (m1 and m2) := (modalrepr m1) ++ " and " ++ (modalrepr m2)
| (m1 or m2) := (modalrepr m1) ++ " or " ++ (modalrepr m2)
| (m1 => m2) := (modalrepr m1) ++ " => " ++ (modalrepr m2) 
| (neg m) := "neg " ++ (modalrepr m)
| □m := "□" ++ (modalrepr m)
| ◇m := "◇" ++ (modalrepr m)

instance : has_repr (modal W) := ⟨modalrepr W⟩

@[simp] def valuation {W : Type} (R : W → W → Prop) : W → modal W → Prop
| x (□ k) := ∀ y, (R x y) → @valuation y k
| x (◇ k) := ∃ y, (R x y) ∧ valuation y k
| x (k1 => k2) := valuation x k1 → valuation x k2
| x (neg k) := ¬ (valuation x k)
| x (k1 and k2) := valuation x k1 ∧ valuation x k2
| x (k1 or k2) := valuation x k1 ∨ valuation x k2
| x [ϕ] := ϕ x -- To evaluate quoted props at a world we just unquote them and apply them to the world

notation `ϑ` := valuation -- This is dumb notation, but I need to feed 'R' to it when I evaluate. Should probably replace with ⊢ or ⊧ or something but idk