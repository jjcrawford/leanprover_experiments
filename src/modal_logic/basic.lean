/-
Copyright (c) 2019 Jack Crawford. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack Crawford

* Here we define modal formulae and 
-/


import modal_logic.frame_conditions
import tactic.rcases

variable W : Type -- Type of possible worlds

inductive modal {atm : Type}
| atom : atm → modal -- The richest case is when atoms are (quoted) predicates (W → Prop)
| neg : modal → modal
| box : modal → modal
| diamond : modal → modal
| and : modal → modal → modal
| or : modal → modal → modal
| arrow : modal → modal → modal

open modal


notation `#[`p`]` := atom p
prefix `not`:25 := neg
prefix `□`:25 := box
prefix `◇`:25 := diamond
infix `or`:23 := or
infix `and`:23 := and
infix `=>`:20 := arrow


instance {atm : Type} : has_neg modal := ⟨@modal.neg atm⟩

def modalrepr {atm : Type} [has_repr atm]: @modal atm → string 
| #[ϕ] := "ϕ"
| (m1 and m2) := (modalrepr m1) ++ " and " ++ (modalrepr m2)
| (m1 or m2) := (modalrepr m1) ++ " or " ++ (modalrepr m2)
| (m1 => m2) := (modalrepr m1) ++ " => " ++ (modalrepr m2) 
| (neg m) := "neg " ++ (modalrepr m)
| □m := "□" ++ (modalrepr m)
| ◇m := "◇" ++ (modalrepr m)

instance {atm : Type} [has_repr atm] : has_repr modal := ⟨@modalrepr atm _⟩

@[simp] def interpretation {W : Type} {atm : Type} (val : atm → W → Prop) (R : W → W → Prop) : W → (@modal atm) → Prop
| x (□ k) := ∀ y, (R x y) → @interpretation y k
| x (◇ k) := ∃ y, (R x y) ∧ interpretation y k
| x (k1 => k2) := interpretation x k1 → interpretation x k2
| x (neg k) := ¬ (interpretation x k)
| x (k1 and k2) := interpretation x k1 ∧ interpretation x k2
| x (k1 or k2) := interpretation x k1 ∨ interpretation x k2
| x #[ϕ] := (val ϕ) x 

notation `ϑ` := interpretation -- This is dumb notation, but I need to feed 'R' to it when I evaluate. Should probably replace with ⊢ or ⊧ or something but idk