/-
Copyright (c) 2019 Jack Crawford. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack Crawford

* We show that axiom shapes correspond to frame conditions for a number of the most common possible axioms
* I found these on Wikipedia. https://en.wikipedia.org/wiki/Kripke_semantics#Common_modal_axiom_schemata

* eucl_axiom_2 came from an old COMP4630 assignment question I did for extra practice

* Every axiom here except for the one simply called 'H' is actually just a special case of the General Axiom
* from general_axiom.lean, I just wanted to do these for fun and practice as I warmed up to it.
-/


import modal_logic.basic

variable W : Type -- Type of possible worlds


theorem k_axiom {ϕ₁ ϕ₂ : modal W} {R : W → W → Prop} : ∀ x : W, ϑ R x (□(ϕ₁ => ϕ₂) => (□ϕ₁ => □ϕ₂)) :=
λ _ DAtoB DA y hy, DAtoB y hy (DA y hy)

def refl_axiom {R : W → W → Prop} : Prop := 
∀ (ϕ : modal W) (x : W), ϑ R x (□ϕ => ϕ)

def trans_axiom {R : W → W → Prop} : Prop :=
∀ (ϕ : modal W) (x : W), ϑ R x (□ϕ => □□ϕ)

def dense_axiom {R : W → W → Prop} : Prop :=
∀ (ϕ : modal W) (x : W), ϑ R x (□□ϕ => □ϕ)

def serial_axiom {R : W → W → Prop} : Prop :=
∀ (ϕ : modal W) (x : W), ϑ R x (□ϕ => ◇ϕ)
 
def symm_axiom {R : W → W → Prop} : Prop :=
∀ (ϕ : modal W) (x : W), ϑ R x (ϕ => □◇ϕ)

def eucl_axiom {R : W → W → Prop} : Prop :=
∀ (ϕ : modal W) (x : W), ϑ R x (◇ϕ => □◇ϕ) 

def eucl_axiom_2 {R : W → W → Prop} : Prop :=     -- completely redundant, just for fun
∀ (ϕ : modal W) (x : W), ϑ R x (◇□ϕ => □ϕ)

def eq_axiom {R : W → W → Prop} : Prop := -- A better name for this? ϕ → □ϕ
∀ (ϕ : modal W) (x : W), ϑ R x (ϕ => □ϕ)

def conv_axiom {R : W → W → Prop} : Prop :=
∀ (ϕ : modal W) (x : W), ϑ R x (◇□ϕ => □◇ϕ)

def H_axiom {R : W → W → Prop} : Prop :=
∀ (ϕ₁ ϕ₂ : modal W) (x : W), ϑ R x (□(□ϕ₁ => ϕ₂) or □(□ϕ₂ => ϕ₁))

-- Proofs that some common axioms and their frame conditions correspond

theorem refl_axiom_from_refl_fc {R : W → W → Prop} : reflexive R → @refl_axiom W R :=
λ r_fc ϕ x sϕ, sϕ x (r_fc x)

theorem refl_fc_from_refl_axiom {R : W → W → Prop} : @refl_axiom W R → reflexive R :=
λ r_ax w, (r_ax [λ u, R w u] w) (λ u hwu, hwu)

theorem trans_axiom_from_trans_fc {R : W → W → Prop} : transitive R → @trans_axiom W R :=
λ t_fc ϕ x sϕ y hxy z hyz, sϕ z (@t_fc x y z hxy hyz)

theorem trans_fc_from_trans_axiom {R : W → W → Prop} : @trans_axiom W R → transitive R :=
λ t_ax x y z hxy hyz, (t_ax [λ u, R x u] x ) (λ _ a, a) y hxy z hyz

theorem dense_axiom_from_dense_fc {R : W → W → Prop} : dense R → @dense_axiom W R :=
λ d_fc ϕ x sϕ z hxz, by
    rcases (@d_fc x z hxz) with ⟨y, ⟨hxy, hyz⟩⟩;
    from sϕ y hxy z hyz

theorem dense_fc_from_dense_axiom {R : W → W → Prop} : @dense_axiom W R → dense R :=
λ d_ax x z hxz, ((d_ax [λ z, ∃ y : W, (R x y) ∧ (R y z)] x) (λ y hxy z hyz, ⟨y, ⟨hxy, hyz⟩⟩)) z hxz

theorem serial_axiom_from_serial_fc {R : W → W → Prop} : serial R → @serial_axiom W R :=
λ s_fc ϕ x sϕ, by
    cases @s_fc x with y hxy;
    from ⟨y, ⟨hxy, sϕ y hxy⟩⟩

theorem serial_fc_from_serial_axiom {R : W → W → Prop} : @serial_axiom W R → serial R :=
λ s_ax x, (s_ax [λ y, R x y] x (λ _ a, a)).rec_on (λ u hxu, Exists.intro u hxu.left)

theorem symm_axiom_from_symm_fc {R : W → W → Prop} : symmetric R → @symm_axiom W R :=
λ s_fc ϕ x h y hxy, ⟨x, ⟨@s_fc x y hxy, h⟩⟩

theorem symm_fc_from_symm_axiom {R : W → W → Prop} : @symm_axiom W R → symmetric R :=
λ s_ax x y hxy, exists_eq_right'.elim_left ((s_ax [λ y, x = y] x) (eq.refl x) y hxy)

theorem eucl_axiom_from_eucl_fc {R : W → W → Prop} : euclidean R → @eucl_axiom W R :=
λ e_fc ϕ x dx, by
    rcases dx with ⟨y , ⟨hy, ϕy⟩⟩;
    from λ u hu, ⟨y, ⟨@e_fc x u y ⟨hu,hy⟩,ϕy⟩⟩

theorem eucl_fc_from_eucl_axiom {R : W → W → Prop} : @eucl_axiom W R → euclidean R :=
λ e_ax x y z hxyz, exists_eq_right.elim_left ((e_ax [λ y, y = z] x) (exists_eq_right.elim_right hxyz.right) y hxyz.left)

theorem eucl_axiom_2_from_eucl_fc {R : W → W → Prop} : euclidean R → @eucl_axiom_2 W R :=
λ e_fc ϕ x dsϕ, by
    rcases dsϕ with ⟨y,⟨hy, H1⟩⟩;
    from  λ z hz, H1 z (@e_fc x y z ⟨hy, hz⟩)

theorem eucl_fc_from_eucl_axiom_2 {R : W → W → Prop} : @eucl_axiom_2 W R → euclidean R :=
λ e_ax2 x y z hxyz, ((e_ax2 [λ u, R y u] x) ⟨_, ⟨hxyz.left, λ u hu, hu⟩ ⟩) z hxyz.right

theorem eq_axiom_from_eq_fc {R : W → W → Prop} : @eq_fc W R → @eq_axiom W R :=
λ e_fc ϕ x ϕx y hxy, by conv{congr,skip, rw ←(@e_fc x y hxy)}; from ϕx

theorem eq_fc_from_eq_axiom {R : W → W → Prop} : @eq_axiom W R → @eq_fc W R :=
λ e_fc x y, e_fc [λ y, x = y] _ (eq.refl x) _

theorem conv_axiom_from_conv_fc {R : W → W → Prop} : convergent R → @conv_axiom W R :=
λ c_fc ϕ x dsϕ y hxy, by
    rcases dsϕ with ⟨z, ⟨hxz , sϕ⟩⟩;
    rcases (@c_fc x y z ⟨hxy, hxz⟩) with ⟨w, ⟨hyw, hzw⟩⟩;
    from ⟨w, ⟨hyw, sϕ w hzw⟩⟩

theorem conv_fc_from_conv_axiom {R : W → W → Prop} : @conv_axiom W R → convergent R :=
λ c_ax x y z hxyz, -- need to clean this one up
begin
cases hxyz with hxy hxz,
have H1, from exists_imp_distrib.elim_left (c_ax [λ u, R y u] x) y,
have H2, from (and_imp.elim_left (H1)) hxy,
simp at H2,
rcases (H2 z hxz) with ⟨w, ⟨hw, ϕw⟩⟩,
from ⟨w, ⟨ϕw, hw⟩⟩,
end

section -- quarantining out the only classical result here. This is really ugly and I hate it.
open classical
    theorem H_axiom_from_H_fc {R : W → W → Prop} : @H_fc W R → @H_axiom W R :=
    begin
    intros h_fc ϕ₁ ϕ₂ x,
    dsimp,
    dsimp[H_fc] at h_fc,

    cases em (∀ (y : W), (R x y) → (∀ (y_1 : W), (R y y_1) → (ϑ R y_1 ϕ₁)) → (ϑ R y ϕ₂)),
    apply or.inl,
    assumption,
    apply or.inr,
    intros y hxy h2,
    cases em (ϑ R y ϕ₁) with H2 H2,
    assumption,

    exfalso,

    apply h,
    intros z hxz h3,
    apply h2,
    have h4, from h_fc ⟨hxy, hxz⟩,
    cases h4,
    assumption,
    exfalso,
    apply H2,
    apply h3,
    assumption,
    end
end

theorem H_fc_from_H_axiom {R : W → W → Prop} : @H_axiom W R → H_fc R :=
begin
unfold H_axiom H_fc,
intros H_ax x y z hxyz,
cases hxyz with hxy hxz,
let ϕ₁ : modal W, from [λ u, R y u],
let ϕ₂ : modal W, from [λ u, R z u],

have H1, from H_ax ϕ₁ ϕ₂ x,
simp at H1,

cases H1,
have H2, from H1 y hxy,
have H3 : (∀ (y_1 : W), (R y y_1) → (ϑ R y_1 ϕ₁)), 
intros w hyw,
simp[ϕ₁],
from hyw,
have H4, from H2 H3,
simp[ϕ₂] at H4,
from or.inr H4,

have H2, from H1 z hxz,
have H3 : (∀ (y_1 : W), (R z y_1) → (ϑ R y_1 ϕ₂)), 
intros w hzw,
simp[ϕ₂],
from hzw,
have H4, from H2 H3,
simp[ϕ₂] at H4,
from or.inl H4,
end