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
