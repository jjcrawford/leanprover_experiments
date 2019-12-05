/-
Copyright (c) 2019 Jack Crawford. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack Crawford (this directly mimics topology.category.Top.basic, though)
-/

import topology.category.Top.basic
import algebra.category.Group
import category_theory.concrete_category.bundled_hom
import topology.basic

open category_theory
open Top

-- open function
-- open category_theory.bundled

universe u

-- class topological_pair (α : Type u) extends topological_space α :=
-- (subset       : set α)

class topological_pair (X : Type u) extends topological_space X := 
(snd : Type u)
(snd_top : topological_space snd)
(inclusion : snd → X)
(embed : embedding inclusion)

open topological_pair

@[reducible] def Pairs : Type (u+1) := bundled topological_pair
namespace Pairs

instance topological_pair_unbundled (x : Pairs.{u}) : topological_pair x := x.str

-- def pair_map {α β : Type u} [topological_pair α] [topological_pair β] (f : α → β) := ∀ a : topological_pair.subset α,  ∃ b : topological_pair.subset β, f a = b

structure pair_map ⦃X Y : Type u⦄ (Iα : topological_pair X) (Iβ : topological_pair Y) :=
(map : X → Y)
(subspace_map : snd X → snd Y)
(commutes : ∀ (x : snd X), map (inclusion x) = inclusion (subspace_map x))


-- instance {X Y : Type u} [topological_pair X] [topological_pair Y] (f : X → Y) : has_lift (pair_map f) (snd X → snd Y) :=
-- ⟨λ hf, pair_map.subspace_map hf⟩ 

-- theorem pair_map_id {α : Type u} [topological_pair α] : pair_map (id : α → α) :=
-- λ A, ⟨A, by refl⟩

theorem pair_map_id {α : Type u} [h : topological_pair α] : pair_map h h := --@pair_map _ _ _ _ (id : α → α) (continuous_id) :=
⟨(λ x, x), (λ x, x), λ x, refl (inclusion x)⟩

-- lemma pair_map.comp {α β γ : Type u} [topological_pair α] [topological_pair β] [topological_pair γ] {g : β → γ} {f : α → β} (hg : pair_map g) (hf : pair_map f) :
--   pair_map (g ∘ f) :=
-- begin
-- constructor,
-- swap,
-- intros a,
-- from (pair_map.subspace_map hg) ( (pair_map.subspace_map hf) a),
-- intros x,
-- have H1, from (pair_map.commutes hf) x,
-- have H2, from pair_map.commutes hg ((pair_map.subspace_map hf) x),
-- simp,
-- apply eq.symm,
-- apply eq.trans,
-- from eq.symm H2,
-- congr,
-- from eq.symm H1,
-- end

lemma pair_map.comp {α β γ : Type u} [topological_pair α] [topological_pair β] [topological_pair γ] {g : β → γ} {f : α → β} (hg : pair_map g) (hf : pair_map f) :
  pair_map (g ∘ f) :=


lemma pair_map.comp {α β γ : Type u} [topological_pair α] [topological_pair β] [topological_pair γ] {g : β → γ} {f : α → β} (hg : pair_map g) (hf : pair_map f) :
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


-- class homology_theory (H : ℕ → (Pairs.{u} ⥤ CommGroup)) (d : ∀ n : ℕ, nat_trans (H (n+1)) (H n)) :=
-- sorry
-- (htpy : ∀ {α β : Type u} [topological_pair α] [topological_pair β] (f : α → β) (g : α → β) [continuous f] [continuous g], f ≃ g → f* = g*)


----------------------
-- -- Represents a topological pair (X, A) with embedding ι : A → X
-- class topological_pair (X : Type u) extends topological_space X := 
-- (snd : Type u)
-- (snd_top : topological_space snd)
-- (inclusion : snd → X)
-- (embed : embedding inclusion)

-- open topological_pair 

-- instance topological_pair.snd_has_lift {X : Type u} [topological_pair X] : has_lift (topological_pair.snd X) X :=
-- ⟨topological_pair.inclusion⟩

-- -- The category of topological pairs
-- @[reducible] def Pairs : Type (u+1) := bundled topological_pair 
-- /- I have no idea if 'Pairs' is standard notation, but this is what Vigleik 
--    wrote on the whiteboard so I'm taking it. -

-------------

-- instance test : @bundled_hom  :=
-- begin

-- end
-- instance : category (bundled topological_pair) :=
-- by refine
-- { hom := λ X Y, @hom X.1 Y.1 X.str Y.str,
--   id := λ X, @bundled_hom.id c hom 𝒞 X X.str,
--   comp := λ X Y Z f g, @bundled_hom.comp c hom 𝒞 X Y Z X.str Y.str Z.str g f,
--   comp_id' := _,
--   id_comp' := _,
--   assoc' := _};
-- intros; apply 𝒞.hom_ext;
--   simp only [𝒞.id_to_fun, 𝒞.comp_to_fun, function.left_id, function.right_id]


-- class homology_theory (H : ℕ → (Pairs.{u} ⥤ CommGroup)) (d : ∀ n : ℕ, nat_trans (H (n+1)) (H n)) :=
-- sorry
-- (htpy : ∀ {α β : Type u} [topological_pair α] [topological_pair β] (f : α → β) (g : α → β) [continuous f] [continuous g], f ≃ g → f* = g*)


--------------------------------------
-- namespace Pairs

-- instance topological_pair_unbundled (x : Pairs) : topological_pair x := x.str


-- structure pair_map ⦃X Y : Type u⦄ (Iα : topological_pair X) (Iβ : topological_pair Y) :=
-- (map : X → Y)
-- (subspace_map : snd X → snd Y)
-- (commutes : ∀ (x : snd X), map (inclusion x) = inclusion (subspace_map x))
--------------------------------------------


-- instance test : @unbundled_hom topological_pair pair_map :=
-- begin

-- end
-- instance test : @bundled_hom topological_pair pair_map :=
-- begin

-- end

-- begin
--   intros,
-- end

---------------- epic
-- structure pair_map {X Y : Type u} [topological_pair X] [topological_pair Y] (map : X → Y) := 
-- (subspace_map : snd X → snd Y)
-- (commutes : ∀ (x : snd X), map (inclusion x) = inclusion (subspace_map x))
-------------------------

-- (map : X → Y)
-- (commutes : ∀ a : snd X,  ∃ b : snd Y, map (inclusion a) = inclusion b)
-- (subspace_map : snd X → snd Y . {intro x, choose a b using pair_map.commutes f x, from a})

-- open function
-- noncomputable theory
-- def topological_pair.subspace_map {X Y : Type u} [topological_pair X] [topological_pair Y] (f : pair_map X Y): snd X → snd Y :=
-- by {intro x, choose a b using pair_map.commutes f x, from a}

-- instance {X Y : Type u} [topological_pair X] [topological_pair Y] (f : pair_map X Y) : injective (topological_pair.subspace_map f) :=
-- begin
-- let w : snd X → snd Y, by {intro x, choose a b using pair_map.commutes f x, from a},
-- have H : (w = (topological_pair.subspace_map f)),
-- refl,
-- rw ←H,

-- have H1, from embed X,
-- cases H1 with Xind Xinj,
-- -- unfold injective at Xinj,
-- -- unfold injective,
-- intros a₁ a₂ h,

-- have H2, from embed Y,
-- cases H2 with Yind Yinj,
-- unfold injective at Yinj,

-- have H3, from pair_map.commutes f,

-- -- have H1, from inj a₁ a₂,
-- -- dsimp[inclusion] at inj,

-- -- dsimp[topological_pair.subspace_map] at h,
-- end


----------------------------------------------------------------

-- instance {X Y : Type u} [topological_pair X] [topological_pair Y] (f : X → Y) : has_lift (pair_map f) (snd X → snd Y) :=
-- ⟨λ hf, pair_map.subspace_map hf⟩ 

-- theorem pair_map_id {α : Type u} [topological_pair α] : pair_map (id : α → α) := --@pair_map _ _ _ _ (id : α → α) (continuous_id) :=
-- ⟨_, (λ x, by refl)⟩

-- lemma pair_map.comp {α β γ : Type u} [topological_pair α] [topological_pair β] [topological_pair γ] {g : β → γ} {f : α → β} (hg : pair_map g) (hf : pair_map f) :
--   pair_map (g ∘ f) :=
-- begin
-- constructor,
-- swap,
-- intros a,
-- from (pair_map.subspace_map hg) ( (pair_map.subspace_map hf) a),
-- intros x,
-- have H1, from (pair_map.commutes hf) x,
-- have H2, from pair_map.commutes hg ((pair_map.subspace_map hf) x),
-- simp,
-- apply eq.symm,
-- apply eq.trans,
-- from eq.symm H2,
-- congr,
-- from eq.symm H1,
-- end

-------------------------------------------------------------------



-- instance : category (bundled topological_pair) :=
-- by refine
-- { hom := λ X Y, @pair_map X.1 Y.1 _ _ X.str Y.str,
--   id := λ X, @bundled_hom.id (topological_pair) (pair_map) 𝒞 X X.str,
--   comp := λ X Y Z f g, @bundled_hom.comp (topological_pair) (pair_map) 𝒞 X Y Z X.str Y.str Z.str g f,
--   comp_id' := _,
--   id_comp' := _,
--   assoc' := _};
-- intros; apply 𝒞.hom_ext;
--   simp only [𝒞.id_to_fun, 𝒞.comp_to_fun, function.left_id, function.right_id]


-- instance : category pair_map :=
-- by refine
-- { hom := λ X Y, @hom X.1 Y.1 X.str Y.str,
--   id := λ X, @bundled_hom.id c hom 𝒞 X X.str,
--   comp := λ X Y Z f g, @bundled_hom.comp c hom 𝒞 X Y Z X.str Y.str Z.str g f,
--   comp_id' := _,
--   id_comp' := _,
--   assoc' := _};
-- intros; apply 𝒞.hom_ext;
--   simp only [𝒞.id_to_fun, 𝒞.comp_to_fun, function.left_id, function.right_id]

-- /-- A category given by `bundled_hom` is a concrete category. -/
-- instance concrete_category : concrete_category (bundled c) :=
-- { forget := { obj := λ X, X,
--               map := λ X Y f, 𝒞.to_fun X.str Y.str f,
--               map_id' := λ X, 𝒞.id_to_fun X.str,
--               map_comp' := by intros; erw 𝒞.comp_to_fun; refl },
--   forget_faithful := { injectivity' := by intros; apply 𝒞.hom_ext } }

-----------------------------------------------------------------

-- instance concrete_category_pair_map : unbundled_hom @pair_map :=
-- ⟨@pair_map_id, @pair_map.comp⟩

-- /-- Construct a bundled `Pair` from the underlying type and the typeclass. -/
-- def of (X : Type u) [topological_pair X] : Pairs := ⟨X⟩

-- instance hom_has_coe_to_fun (X Y : Pairs.{u}) : has_coe_to_fun (X ⟶ Y) :=
-- { F := _, coe := subtype.val }

-- @[simp] lemma id_app (X : Pairs.{u}) (x : X) :
--   @coe_fn (X ⟶ X) (Pairs.hom_has_coe_to_fun X X) (𝟙 X) x = x := rfl
---------------------------------------------------

-- class homology_theory (H : ℕ → (Pairs.{u} ⥤ CommGroup)) (d : ∀ n : ℕ, nat_trans (H (n+1)) (H n)) :=
-- sorry
-- (htpy : ∀ {α β : Type u} [topological_pair α] [topological_pair β] (f : α → β) (g : α → β) [continuous f] [continuous g], f ≃ g → f* = g*)

end Pairs

