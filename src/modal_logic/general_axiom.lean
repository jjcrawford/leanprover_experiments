/-
Copyright (c) 2019 Jack Crawford. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack Crawford

* Here we prove the result by Lemmon and Scott (1977) about the General Axiom 
* (as stated here https://plato.stanford.edu/entries/logic-modal/#GenAxi)
*
* The statement of the theorem is that the "General Axiom"
*                ◇^h □^i ϕ → □^j ◇^k
* corresponds to the frame condition
*    (w R^h v) ∧ (w R^j u) → ∃ x, (v R^i x) ∧ (u R^k x)
* for all worlds w, v, u.
*
-/

import modal_logic.basic
import tactic.rcases

variable W : Type -- Type of possible worlds


@[simp] def compose {W : Type} : (W → W → Prop) → (W → W → Prop) → (W → W → Prop) :=
λ R1 R2 w1 w2, ∃ u, R1 w1 u ∧ R2 u w2

@[simp] def relpow {W : Type} : (W → W → Prop) → ℕ → (W → W → Prop) 
| R 0 := λ w1 w2, w1=w2
| R (n+1) := compose (relpow R (n)) R

@[simp] def boxpow {W : Type} : ℕ → modal W → modal W
| 0 m := m
| (n+1) m := □(boxpow n m)

@[simp] def diamondpow {W : Type} : ℕ → modal W → modal W 
| 0 m := m
| (n+1) m := ◇(diamondpow n m)

-- if we can decrement m by incrementing n, we can keep doing this until n:=m+n and m:=0  
lemma induction_max {P: ℕ → ℕ → Prop} {h : ∀ (m n : ℕ), P (m+1) n = P m (n+1)} : Π (m n : ℕ), (P m n) = P 0 (m+n) 
| 0 n    := by simp
| (m+1) n := begin
    apply eq.trans,
    from h m n,

    have H₂, from induction_max m (n+1),
    simp[nat.add] at H₂,
    simp[nat.add],
    from H₂,
end

-- to prove w R^n y → y⊢□^(m+1)ϕ we can show w R^(n+1) z → z ⊢ □^m ϕ, looking "one step into the future"
lemma boxrel {R : W → W → Prop} (k : modal W) : ∀ (m n : ℕ) (w : W), (∀ (y : W), relpow R n w y → (ϑ R y (boxpow (m+1) k))) = (∀ (y : W), relpow R (n+1) w y → (ϑ R y (boxpow (m) k)))
| 0 n w     := by simp;
            from ⟨λ h u y rpnwy Ryu, h y rpnwy u Ryu,
                  λ h u rpnwu y Ruy, h y u rpnwu Ruy⟩
| (m+1) n w := by simp;
            from ⟨λ h u y rpnwy Ryu z Ruz, h y rpnwy u Ryu z Ruz,
            λ h u rpnwu y Ruy z Ryz, h y u rpnwu Ruy z Ryz⟩

-- to prove w R^n y ∧ y⊢◇^(m+1)ϕ we can show w R^(n+1) z ∧ z ⊢ ◇^m ϕ, looking "one step into the future"
lemma diarel {R : W → W → Prop} (k : modal W) : ∀ (m n : ℕ) (w : W), (∃ (y : W), relpow R n w y ∧ (ϑ R y (diamondpow (m+1) k))) = (∃ (y : W), relpow R (n+1) w y ∧ (ϑ R y (diamondpow (m) k)))
| 0 n w     := by simp;
            from ⟨λ ⟨u, ⟨rpnwu, ⟨y, ⟨Ruy, rvyk⟩⟩⟩⟩, ⟨y, ⟨⟨u, ⟨rpnwu, Ruy⟩⟩, rvyk⟩⟩,
                  λ ⟨y, ⟨⟨u, ⟨rpnwu, Ruy⟩⟩, rvyk⟩⟩, ⟨u, ⟨rpnwu, ⟨y, ⟨Ruy, rvyk⟩⟩⟩⟩⟩
| (m+1) n w := by simp;
            from ⟨λ ⟨u ,⟨rpnwu, ⟨y, ⟨Ruy, ⟨z, ⟨Ryz, zdpmk⟩⟩⟩⟩⟩⟩, ⟨y, ⟨⟨u, ⟨rpnwu, Ruy⟩⟩, ⟨z, ⟨Ryz, zdpmk⟩⟩⟩⟩,
                 λ ⟨y, ⟨⟨u, ⟨rpnwu, Ruy⟩⟩, ⟨z, ⟨Ryz, zdpmk⟩⟩⟩⟩, ⟨u, ⟨rpnwu, ⟨y, ⟨Ruy, ⟨z, ⟨Ryz, zdpmk⟩⟩⟩⟩⟩⟩⟩

-- combine above two lemmas to show that  w R^m y → y⊢□^n ϕ is satisfied when w R^(m+n) z → z⊢ϕ is satisfied, looking "all the way into the future"
lemma boxrel2 {R : W → W → Prop} : ∀ (k : modal W) (m n : ℕ) (w : W), ( ∀ (y : W), relpow R n w y → (ϑ R y (boxpow (m) k))) = (∀ (z : W), relpow R (n+m) w z → (ϑ R z (boxpow (0) k)))
| k 0 n w := by refl
| k (m+1) n w := begin
    have H, from @induction_max (λ i j, (∀ (y : W), relpow R j w y → valuation R y (boxpow i k))) (λ i j : ℕ, @boxrel W R k i j w) (m+1) n,
    simp at H,
    simp,
    from H,
end

-- combine above two lemmas to show that  w R^m y ∧ y⊢◇^n ϕ is satisfied when w R^(m+n) z ∧ z⊢ϕ is satisfied, looking "all the way into the future"
lemma diarel2 {R : W → W → Prop} : ∀ (k : modal W) (m n : ℕ) (w : W), (∃ (y : W), relpow R n w y ∧ (ϑ R y (diamondpow (m) k))) = (∃ (z : W), relpow R (n+m) w z ∧ (ϑ R z (diamondpow (0) k)))
| k 0 n w := by refl
| k (m+1) n w := begin
    have H, from @induction_max (λ i j, (∃ (y : W), relpow R j w y ∧ valuation R y (diamondpow i k))) (λ i j : ℕ, @diarel W R k i j w) (m+1) n,
    simp at H,
    simp,
    from H,
end

-- corollary: w⊢□^n ϕ is satisfied when w R^n z → z ⊢ϕ is satisfied 
@[simp] lemma boxrel3 {R : W → W → Prop} : ∀ (k : modal W) (m : ℕ) (w : W), ϑ R w (boxpow m k) = ∀ z, (relpow R m w z) → (ϑ R z k) :=
begin
    intros k m w,
    have H, from @boxrel2 W R k m 0 w,
    simp at H,
    simp,
    from H,
end

-- corollary: w⊢◇^n ϕ is satisfied when w R^n z ∧ z ⊢ϕ is satisfied 
@[simp] lemma diarel3 {R : W → W → Prop} : ∀ (k : modal W) (m : ℕ), ∀ (w : W), ϑ R w (diamondpow m k) = ∃ z, (relpow R m w z) ∧ (ϑ R z k) :=
begin
    intros k m w,
    have H, from @diarel2 W R k m 0 w,
    simp at H,
    simp,
    from H,
end

-- If ϕ is the proposition [λ u, w R^n u] then w⊢□^n ϕ is always true. 
lemma boxpow_of_relpow {R : W → W → Prop} : ∀ (w : W) (n : ℕ), (ϑ R w (boxpow n [λ u, relpow R n w u]))
| w n := by simp

-- The "General Axiom" as it is referred to by https://plato.stanford.edu/entries/logic-modal/#GenAxi
@[simp] def hijk_axiom {R : W → W → Prop} (h i j k : ℕ) : Prop := 
∀ (ϕ : modal W) (x : W), ϑ R x ((diamondpow h (boxpow i ϕ)) => (boxpow j (diamondpow k ϕ)))

-- The corresponding frame condition for the General Axiom
@[simp] def hijk_fc {R : W → W → Prop} (h i j k : ℕ) : Prop :=
∀ w v u : W, (relpow R h) w v ∧ (relpow R j) w u → ∃ x : W, (((relpow R i) v x) ∧ ((relpow R k) u x)) 

-- The big result: We prove the result by Lemmon and Scott (1977) about the general axiom and its corresponding frame condition:

-- The hijk-convergence frame condition follows from the general axiom
theorem LemmonScott_fc_from_axiom {R : W → W → Prop} : ∀ (h i j k : ℕ), (@hijk_axiom W R h i j k) → (@hijk_fc W R h i j k) 
| h i j k ax := begin
    rintros w v u ⟨rphwv, rpjwu⟩,
    have H₂ : valuation R w (boxpow j (diamondpow k [(λz, relpow R i v z)])),
    apply ax,
    simp,
    from ⟨v, ⟨rphwv, λ z rpivz, rpivz⟩⟩,

    simp only [boxrel3] at H₂,
    have H₃, from H₂ u rpjwu,
    simp at H₃,
    rcases H₃ with ⟨z, ⟨rpkuz, rpivz⟩⟩,

    from ⟨z, ⟨rpivz, rpkuz⟩⟩,
end

-- The general axiom follows from the corresponding hijk-convergence frame condition
theorem LemmonScott_axiom_from_fc {R : W → W → Prop} : ∀ (h i j k : ℕ), (@hijk_fc W R h i j k) → (@hijk_axiom W R h i j k)
| h i j k fc := begin
    intros ϕ w hh,
    simp at hh,
    simp,
    intros y rpjwy,
    rcases hh with ⟨u, ⟨rphwu, HH⟩⟩,

    rcases (fc w u y ⟨rphwu, rpjwy⟩) with ⟨z,⟨rpiuz, rpkyz⟩⟩,
    from ⟨z, ⟨rpkyz, HH z rpiuz⟩⟩,
end