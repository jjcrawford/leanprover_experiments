import modal_logic.frame_conditions
import tactic.rcases
open classical

variable W : Type -- Type of possible worlds

inductive modal 
| box : modal → modal
| diamond : modal → modal
| arrow : modal → modal → modal
| neg : modal → modal
| and : modal → modal → modal
| or : modal → modal → modal
| atom : (W → Prop) → modal

prefix `□`:20 := modal.box
prefix `◇`:20 := modal.diamond
notation `[`p`]` := modal.atom p -- Maybe this is slightly better?
infix `=>`:20 := modal.arrow


instance {W : Type} : has_neg (modal W) := ⟨modal.neg⟩

open modal

@[simp] def valuation {W : Type} (R : W → W → Prop) : W → modal W → Prop
| x (□ k) := ∀ y, (R x y) → @valuation y k
| x (◇ k) := ∃ y, (R x y) ∧ valuation y k
| x (k1 => k2) := valuation x k1 → valuation x k2
| x (neg k) := ¬ (valuation x k)
| x (and k1 k2) := valuation x k1 ∧ valuation x k2
| x (or k1 k2) := valuation x k1 ∨ valuation x k2
| x [ϕ] := ϕ x -- To evaluate quoted props at a world we just unquote them and apply them to the world

infix `or`:20 := modal.or
infix `and`:20 := modal.and
notation R `ϑ` := valuation R -- This is dumb notation, but I need to feed 'R' to it when I evaluate


-- Some common axioms

theorem k_axiom {ϕ₁ ϕ₂ : W → Prop} {R : W → W → Prop} : ∀ x : W, R ϑ x (□([ϕ₁] => [ϕ₂]) => (□[ϕ₁] => □[ϕ₂])) :=
λ x DAtoB DA y hy, DAtoB y hy (DA y hy)

def refl_axiom {R : W → W → Prop} : Prop := 
∀ (ϕ : W → Prop) (x : W), R ϑ x (□[ϕ] => [ϕ])

def trans_axiom {R : W → W → Prop} : Prop :=
∀ (ϕ : W → Prop) (x : W), R ϑ x (□[ϕ] => □□[ϕ])

def dense_axiom {R : W → W → Prop} : Prop :=
∀ (ϕ : W → Prop) (x : W), R ϑ x (□□[ϕ] => □[ϕ])

def serial_axiom {R : W → W → Prop} : Prop :=
∀ (ϕ : W → Prop) (x : W), R ϑ x (□[ϕ] => ◇[ϕ])

def symm_axiom {R : W → W → Prop} : Prop :=
∀ (ϕ : W → Prop) (x : W), R ϑ x ([ϕ] => □◇[ϕ])

def eucl_axiom {R : W → W → Prop} : Prop :=
∀ (ϕ : W → Prop) (x : W), R ϑ x (◇[ϕ] => □◇[ϕ]) 

def eucl_axiom_2 {R : W → W → Prop} : Prop :=     -- completely redundant, just for fun
∀ (ϕ : W → Prop) (x : W), R ϑ x (◇□[ϕ] => □[ϕ])

def eq_axiom {R : W → W → Prop} : Prop := -- A better name for this? ϕ → □ϕ
∀ (ϕ : W → Prop) (x : W), R ϑ x ([ϕ] => □[ϕ])

def conv_axiom {R : W → W → Prop} : Prop :=
∀ (ϕ : W → Prop) (x : W), R ϑ x (◇□[ϕ] => □◇[ϕ])

def h_axiom {R : W → W → Prop} : Prop :=
∀ (ϕ₁ ϕ₂ : W → Prop) (x : W), R ϑ x (□(□[ϕ₁] => [ϕ₂]) or □(□[ϕ₂] => [ϕ₁]))


-- Proofs that axioms and their frame conditions correspond

theorem refl_axiom_from_refl_fc {R : W → W → Prop} : reflexive R → @refl_axiom W R :=
λ r_fc ϕ x sϕ, sϕ x (r_fc x)

theorem refl_fc_from_refl_axiom {R : W → W → Prop} : @refl_axiom W R → reflexive R := -- (□ϕ → ϕ) gives reflexivity as a FC
begin -- I annotated the first proof
intros r_ax w, -- We assume the reflexivity axiom (□ϕ => ϕ) holds. Consider an arbitrary world w : W
let ϕ := λ u, R w u, -- Let ϕ represent the proposition "I am pointed at by w"
apply r_ax, -- Then if ϕ were true at w, it would say "w points to w", which is the refl fc. By the axiom it suffices we show □ϕ  
dsimp, -- □ϕ evaluated at w says that any world u pointed at by w should satisfy ϕ, which in turn says that "w points at u"
intros u hwu, -- Suppose we have such a world u where w points at u. 
from hwu, -- Then we must show that ϕ holds at u: "w points at u", but we already have this. We are done.
end
-- λ r_ax w, (r_ax (λ u, R w u) w) (λ u hwu, hwu) -- this is the minified version of the same proof

theorem trans_axiom_from_trans_fc {R : W → W → Prop} : transitive R → @trans_axiom W R :=
λ t_fc ϕ x sϕ y hxy z hyz, sϕ z (@t_fc x y z hxy hyz)

theorem trans_fc_from_trans_axiom {R : W → W → Prop} : @trans_axiom W R → transitive R :=
λ t_ax x y z hxy hyz, (t_ax (λ u, R x u) x ) (λ _ a, a) y hxy z hyz

theorem dense_axiom_from_dense_fc {R : W → W → Prop} : dense R → @dense_axiom W R :=
λ d_fc ϕ x sϕ z hxz, by
    rcases (@d_fc x z hxz) with ⟨y, ⟨hxy, hyz⟩⟩;
    from sϕ y hxy z hyz

theorem dense_fc_from_dense_axiom {R : W → W → Prop} : @dense_axiom W R → dense R :=
λ d_ax x z hxz, ((d_ax (λ z, ∃ y : W, (R x y) ∧ (R y z)) x) (λ y hxy z hyz, ⟨y, ⟨hxy, hyz⟩⟩)) z hxz

theorem serial_axiom_from_serial_fc {R : W → W → Prop} : serial R → @serial_axiom W R :=
λ s_fc ϕ x sϕ, by
    cases @s_fc x with y hxy;
    from ⟨y, ⟨hxy, sϕ y hxy⟩⟩

theorem serial_fc_from_serial_axiom {R : W → W → Prop} : @serial_axiom W R → serial R :=
λ s_ax x,
begin
have H1, from s_ax (λ y, R x y) x (by simp),
simp at H1,
from H1,
end

theorem symm_axiom_from_symm_fc {R : W → W → Prop} : symmetric R → @symm_axiom W R :=
λ s_fc ϕ x h y hxy, ⟨x , ⟨@s_fc x y hxy, h⟩⟩

theorem symm_fc_from_symm_axiom {R : W → W → Prop} : @symm_axiom W R → symmetric R :=
λ s_ax x y hxy, by 
{have H, from (s_ax (λ y, x = y) x) (by simp) y hxy,
simp at H,
from H}

theorem eucl_axiom_from_eucl_fc {R : W → W → Prop} : euclidean R → @eucl_axiom W R :=
λ e_fc ϕ x dx, by
    rcases dx with ⟨y , ⟨hy, ϕy⟩⟩;
    from λ u hu, ⟨y, ⟨@e_fc x u y ⟨hu,hy⟩,ϕy⟩⟩

theorem eucl_fc_from_eucl_axiom {R : W → W → Prop} : @eucl_axiom W R → euclidean R :=
λ e_ax x y z hxyz, by 
{have H, from (e_ax (λ y, y = z) x) (by simp; from hxyz.right),
simp at H,
from H y hxyz.left}

theorem eucl_axiom_2_from_eucl_fc {R : W → W → Prop} : euclidean R → @eucl_axiom_2 W R :=
λ e_fc ϕ x dsϕ, by
    rcases dsϕ with ⟨y,⟨hy, H1⟩⟩;
    from  λ z hz, H1 z (@e_fc x y z ⟨hy, hz⟩)

theorem eucl_fc_from_eucl_axiom_2 {R : W → W → Prop} : @eucl_axiom_2 W R → euclidean R :=
λ e_ax2 x y z hxyz, ((e_ax2 (λ u, R y u) x) ⟨_, ⟨hxyz.left,λ u hu, hu⟩ ⟩) z hxyz.right

theorem eq_axiom_from_eq_fc {R : W → W → Prop} : @eq_fc W R → @eq_axiom W R :=
λ e_fc ϕ x ϕx y hxy, by conv{congr,skip, rw ←(@e_fc x y hxy)}; from ϕx

theorem eq_fc_from_eq_axiom {R : W → W → Prop} : @eq_axiom W R → @eq_fc W R :=
λ e_fc x y, by apply e_fc (λ y, x = y);simp

theorem conv_axiom_from_conv_fc {R : W → W → Prop} : convergent R → @conv_axiom W R :=
begin
unfold convergent conv_axiom,
intros c_fc ϕ x dsϕ y hxy,
rcases dsϕ with ⟨z ,⟨hxz , sϕ⟩⟩,
rcases (@c_fc x y z ⟨hxy, hxz⟩) with ⟨w , ⟨hyw, hzw⟩⟩,
from ⟨w , ⟨hyw, sϕ w hzw⟩⟩
end

theorem conv_fc_from_conv_axiom {R : W → W → Prop} : @conv_axiom W R → convergent R :=
λ c_ax x y z hxyz,
begin
have H1, from c_ax (λ u, R y u) x,
simp at H1,
cases hxyz with hxy hxz,
have H2, from H1 y hxy,
simp at H2,
have H3, from H2 z hxz,
rcases H3 with ⟨w, ⟨hw, ϕw⟩⟩,
from ⟨w, ⟨ϕw, hw⟩⟩,
end

-- local attribute classical.prop_decidable 

-- theorem h_axiom_from_h_fc {R : W → W → Prop} : @h_fc W R → @h_axiom W R :=
-- begin
-- unfold h_fc h_axiom,
-- intros h_fc ϕ₁ ϕ₂ x,
-- simp,
-- cases em (∀ (y : W), (R x y) → (∀ (y_1 : W), (R y y_1) → ϕ₁ y_1) → ϕ₂ y),
-- constructor,
-- assumption,

-- apply or.inr,
-- intros y hxy h2,

-- have H2 : ∃ (y : W), ↥(R x y) ∧ ¬ ((∀ (y_1 : W), (R y y_1) → ϕ₁ y_1) → ϕ₂ y), sorry, -- from h

-- rcases H2 with ⟨z, ⟨hxz, ϕz⟩⟩,

-- have H3, from h_fc x y z ⟨hxy,hxz⟩,
-- cases H3,
-- have H4, from h2 z H3,
-- exfalso,
-- apply ϕz,
-- intros hh, from H4,

-- have H5 : ↥(R y y), 
-- cases h_fc x y y ⟨hxy, hxy⟩;assumption,
-- have H6, from h2 y H5,
-- exfalso,
-- apply ϕz,
-- intros test,
-- apply h2,
-- have H7, from h_fc x y z ⟨hxy, hxz⟩,
-- cases H7,
-- assumption,


-- -- intros w hxw ϕw,


-- -- have H4, from h2 y H3,
-- -- exfalso,
-- -- apply ϕz,
-- -- intros hh, from H4,

-- -- have H3 : decidable_pred ϕ₁,
-- -- intros u,
-- -- cases em (ϕ₁ u),
-- -- by_contra,
-- -- apply h,

-- end

theorem h_fc_from_h_axiom {R : W → W → Prop} : @h_axiom W R → H_fc R :=
begin
unfold h_axiom H_fc,
intros h_ax x y z hxyz,
cases hxyz with hxy hxz,
let ϕ₁ : W → Prop, from λ u, R y u,
let ϕ₂ : W → Prop, from λ u, R z u,

have H1, from h_ax ϕ₁ ϕ₂ x,
simp at H1,

cases H1,
have H2, from H1 y hxy,
have H3 : (∀ (y_1 : W), (R y y_1) → ϕ₁ y_1), 
intros w hyw,
simp[ϕ₁],
from hyw,
have H4, from H2 H3,
simp[ϕ₂] at H4,
from or.inr H4,

have H2, from H1 z hxz,
have H3 : (∀ (y_1 : W), (R z y_1) → ϕ₂ y_1), 
intros w hzw,
simp[ϕ₂],
from hzw,
have H4, from H2 H3,
simp[ϕ₂] at H4,
from or.inl H4,
end


-- I was going to try proving the Lemmon-Scott result here but didn't end up getting around to it

@[simp] def compose : (W → W → Prop) → (W → W → Prop) → (W → W → Prop) :=
λ R1 R2 w1 w2, ∃ u, R1 w1 u ∧ R2 u w2

-- instance : has_comp (W → W → Prop) :=
-- begin
-- end

@[simp] def relpow : (W → W → Prop) → ℕ → (W → W → Prop) 
| R 0 := λ w1 w2, w1=w2
| R (n+1) := compose W R (relpow R n)

@[simp] def boxpow : ℕ → modal W → modal W
| 0 m := m
| (n+1) m := □ (boxpow n m)

@[simp] def diamondpow : ℕ → modal W → modal W 
| 0 m := m
| (n+1) m := ◇ (diamondpow n m)


-- theorem forall_rel_from_boxpow {R : W → W → Prop} : ∀ (x : W) (n : ℕ), (∀ (ϕ : W → Prop), (R ϑ x (boxpow W n [ϕ]))) → (∀ u, relpow W R n x u)
-- | x 0    bp u := begin 
-- simp,
-- -- let ϕ : W → Prop, from λ z : W, R x z,
-- have H1, from bp (λ z : W, u = z),
-- simp[boxpow, modalprop] at H1,
-- have H2 : modalprop R x (boxpow W 0 [λ (z : W), u = z]) = modalprop R x [λ (z : W), u = z],
-- simp,
-- rw H2 at H1,
-- simp[modalprop] at H1,
-- from eq.symm H1,
-- end
-- | x (n+1)   bp u := begin
-- simp[relpow],
-- have H1, from forall_rel_from_boxpow x n,

-- have H2 : (∀ (ϕ : W → Prop), R ϑ x (boxpow W n [ϕ])),
-- intros ϕ,
-- -- let ϕ₁ : W → Prop, from λ z, R u z,
-- have H3, from bp (λ z, R u z),
-- simp[boxpow] at H3,

-- -- apply H3,
-- -- simp at bp,

-- end
-- begin
-- intros ϕ x n e_rel u,
-- simp[boxpow] at e_rel,
-- end

@[simp] def hijk_axiom {R : W → W → Prop} (h i j k : ℕ) : Prop := 
∀ (ϕ : W → Prop) (x : W), R ϑ x ((diamondpow W h (boxpow W i [ϕ])) => (boxpow W j (diamondpow W k [ϕ])))

@[simp] def hijk_fc {R : W → W → Prop} (h i j k : ℕ) : Prop :=
∀ x y z : W, (relpow W R h) x y ∧ (relpow W R j) x z → ∃ u : W, (((relpow W R i) y x) ∧ ((relpow W R k) z x)) 



-- theorem LemmonScott_fc_from_axiom {R : W → W → Prop} : ∀ (h i j k : ℕ), (@hijk_axiom W R h i j k) → (@hijk_fc W R h i j k) 
-- | h i j (k+1) ax := sorry
-- | h i (j+1) 0 ax := sorry
-- | h (i+1) 0 0 ax := sorry
-- | (h+2) 0 0 0 ax := begin
-- simp[hijk_fc],
-- simp[hijk_axiom] at ax,
-- intros x y z u Rxu,
-- intros pRuy eqxz,
-- constructor,
-- swap,
-- from eq.symm eqxz,
-- constructor,
-- assumption,

-- -- have eqyx, from ax (λ u, y = u) x y Rxy (eq.refl y),
-- -- simp at eqyx,
-- -- from ⟨⟨y, eqyx⟩, eq.symm eqxz⟩,
-- end
-- | 1 0 0 0 ax := begin
-- simp[hijk_fc],
-- simp[hijk_axiom] at ax,
-- intros x y z,
-- intros Rxy eqxz,
-- have eqyx, from ax (λ u, y = u) x y Rxy (eq.refl y),
-- simp at eqyx,
-- from ⟨⟨y, eqyx⟩, eq.symm eqxz⟩,
-- end
-- | 0 0 0 0 ax := begin 
-- intros x y z,
-- simp,
-- intros eqxy eqxz,
-- from ⟨⟨x, eq.symm eqxy⟩, eq.symm eqxz⟩,
-- end

-- begin
-- unfold hijk_axiom hijk_fc,
-- intros h i j k ax x y z h,
-- cases h with pRxy pRxz,
-- end




------ next: intutitionistic logic with kripke frames??

