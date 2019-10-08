/-
Copyright (c) 2019 Jack Crawford. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack Crawford
-/

import topology.category.Top.basic
import algebra.category.Group
import category_theory.concrete_category.unbundled_hom
import category_theory.concrete_category.bundled_hom
import category_theory.epi_mono
import topology.basic

-- import category_theory.epi_mono

open category_theory
open Top

-- open function
-- open category_theory.bundled

universe u

class topological_pair (α : Type u) extends topological_space α :=
(subset       : set α)

@[reducible] def Pairs : Type (u+1) := bundled topological_pair

namespace Pairs

instance topological_pair_unbundled (x : Pairs) : topological_pair x := x.str

def pair_map {α β : Type} [topological_pair α] [topological_pair β] (f : α → β) := ∀ a : topological_pair.subset α,  ∃ b : topological_pair.subset β, f a = b

theorem pair_map_id {α : Type} [topological_pair α] : pair_map (id : α → α) :=
λ A, ⟨A, by refl⟩

lemma pair_map.comp {α β γ : Type} [topological_pair α] [topological_pair β] [topological_pair γ] {g : β → γ} {f : α → β} (hg : pair_map g) (hf : pair_map f) :
  pair_map (g ∘ f) :=
begin
intros A,
choose B hB using hf A,
choose C hC using hg B,
from ⟨C, by {rw ←hC, rw ←hB}⟩,
end

instance concrete_category_pair_map : unbundled_hom @pair_map :=
⟨@pair_map_id, @pair_map.comp⟩

-- TODO: Can't synthesize type class instance for has_hom Pairs (?!)
instance hom_has_coe_to_fun (X Y : Pairs.{u}) : has_coe_to_fun (X ⟶ Y) :=
{ F := _, coe := subtype.val }

-- TODO: Can't synthesize type class instance for category_struct Pairs (?!)
@[simp] lemma id_app (X : Pairs.{u}) (x : X) :
  @coe_fn (X ⟶ X) (Pairs.hom_has_coe_to_fun X X) (𝟙 X) x = x := rfl

/-- Construct a bundled `Top` from the underlying type and the typeclass. -/
def of (X : Type u) [topological_space X] : Top := ⟨X⟩

-- TODO: Can't synthesize type class instance for category Pairs (?!)
class homology_theory (H : ∀ n : ℕ, Pairs ⥤ CommGroup) (d : ∀ n : ℕ, nat_trans (H n+1) (H n))  :=
sorry

end Pairs

-- instance unbundled_of_pairs : @unbundled_hom (λ T, (topological_space T) × (set T))
-- begin
-- intros X Y hX hY f,
-- cases hX with TX A,
-- cases hY with TY B,
-- from (@continuous _ _ TX TY f) ∧ (∀  a', ∃ b', f a' = b')
-- end
-- := begin
-- constructor,
-- swap,
-- intros α β γ hα hβ hγ g f cts_g cts_f,
-- cases hα with Tα A,
-- cases hβ with Tβ B,
-- cases hγ with Tγ C,
-- simp,
-- simp at cts_g cts_f,
-- from @continuous.comp α β γ Tα Tβ Tγ g f cts_g cts_f,
-- intros α hα,
-- cases hα with Tα A,
-- simp,
-- from @continuous_id α Tα,
-- end

-- instance unbundled_of_injections : @unbundled_hom (λ T, set T) (λ α β a b f, ∀  a', ∃ b', f a' = b') 
-- := begin
-- constructor,
-- swap,
-- intros,
-- have H1, from hf a',
-- choose b'' hb'' using H1,
-- have H2, from hg b'',
-- choose a'' ha'' using H2,
-- refine ⟨a'', _⟩,
-- rw ←ha'',
-- rw ←hb'',
-- intros α a a',
-- constructor,
-- swap,
-- from a',
-- refl,
-- end



-- end := begin
-- end := sorry


-- class top_pair :=
-- (X : Top.{u})
-- (A : Top.{u})
-- (ι : A → X)
-- (hι : injective ι)

-- def is_pair_hom : (top_pair → top_pair) → Prop :=
-- begin
-- intros f,
-- ∀ 
-- end


-- instance test {X A Y B : Top.{u}} : @category_theory.unbundled_hom (λ f : Top.{u} ⟶ Top.{u}, mono f) begin
-- intros ι₁ ι₂ mono₁ mono₂ h,
-- end := begin
-- end := sorry

-- def is_top_pair (X A : Top.{u}) := ∃ ι : (A → X), injective ι


-- def Pairs : Type (u+1) := {p : Top.{u} × Top.{u} // is_top_pair p.fst p.snd}

-- noncomputable theory

-- def pair_restrict {X A Y : Top.{u}} [is_top_pair X A] : (X → Y) → (A → Y) :=
-- λ f a, by {choose ι hι using _inst_1, from f(ι a)}

-- def is_Pair_hom {X A Y B : Top.{u}} [is_top_pair X A] [is_top_pair Y B] (f : X → Y) :=
-- begin
-- have fh : A → Y, apply pair_restrict f,
-- assumption,
-- choose ι₁ hι₁ using _inst_1,
-- choose ι₂ hι₂ using _inst_2,
-- from f ∘ ι₁ = fh,
-- end

-- def unbundledhom_pairs {X A }

-- lemma all_pair_homs {X A Y B : Top.{u}} [is_top_pair X A] [is_top_pair Y B] (f : X → Y) : (is_Pair_hom f):=
-- begin

-- end

-- instance : bundled Pairs :=

-- begin
-- end

-- import algebra.category.Group
-- import init.classical
-- import topology.instances.real
-- import data.set.intervals

-- def unit_interval : Type := { x : ℝ // 0 ≤ x ∧ x ≤ 1}



-- def typepow : Type → ℕ → Type
-- | T 0 := unit
-- | T 1 := T
-- | T (n+1) := T × (typepow T n) 

-- instance has_pow : has_pow Type ℕ := ⟨typepow⟩

-- instance {n : ℕ} : topological_space (has_pow ℝ n) :=
-- begin

-- end

-- def simplex (n : ℕ) :=
-- begin
-- have rn : Type, from ℝ^n,

-- end

-- variable F : Type
-- variable [decidable_linear_ordered_comm_group F]

-- theorem subseq_converges_of_seq_converges : Π (seq : ℕ → F) (subseq : ℕ → ℕ) (h : ∀ n : ℕ, subseq n ≥ n), (∀ ε : F, ∃ N : ℕ, ∀ n : ℕ, n > N → abs (seq n) < ε) → (∀ ε : F, ∃ N : ℕ, ∀ n : ℕ, n > N → abs (seq (subseq n)) < ε) :=
-- λ seq subseq subgeq convergent ε, by choose N h using (convergent ε); from ⟨N, λ n hn, h (subseq n) (lt_of_lt_of_le hn (subgeq n))⟩

-- import topology.category.Top.basic

-- def S : ℕ → Type := sorry

-- instance : ∀ (n : ℕ), topological_space (S n) := sorry

-- inductive cell (n : ℕ) : Type
-- | zero : ℕ → cell
-- | 

-- def CW (n : ℕ) : Type :=
-- begin
-- induction n with n skeleton,
-- from ℕ,

-- from Σ (f : S n → skeleton), continuous f,

-- end

-- inductive CW (n : ℕ) : Type
-- | zero : ℕ → CW
-- | succ : Π (m : ℕ) [topological_space (CW m)], CW

