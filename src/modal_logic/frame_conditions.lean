/-
Copyright (c) 2019 Jack Crawford. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack Crawford

* Here we define some slightly less-common frame conditions that a relation could exhibit.
* We prove that these correspond to their associated axiom shapes in common.lean
-/


section relation
universes u v
variables {β : Sort v} (r : β → β → Prop)
local infix `≺`:50 := r

def dense := ∀ ⦃x z⦄, x ≺ z → ∃ y, x ≺ y ∧ y ≺ z 

def serial := ∀ ⦃x⦄, ∃ y, x ≺ y

def euclidean := ∀ ⦃x y z⦄, x ≺ y ∧ x ≺ z → y ≺ z

def eq_fc := ∀ ⦃x y⦄, x ≺ y → x = y

def convergent := ∀ ⦃x y z⦄, x ≺ y ∧ x ≺ z → ∃ w, y ≺ w ∧ z ≺ w

def H_fc := ∀ ⦃x y z⦄, x ≺ y ∧ x ≺ z → y ≺ z ∨ z ≺ y

end relation