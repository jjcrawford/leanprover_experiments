import tactic.squeeze
import modal_logic.frame_conditions
import tactic.rcases
import tactic.tidy
-- open classical

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


-- instance : has_repr (modal W) :=
-- begin
-- constructor,

-- end


@[simp] def valuation {W : Type} (R : W → W → Prop) : W → modal W → Prop
| x (□ k) := ∀ y, (R x y) → @valuation y k
| x (◇ k) := ∃ y, (R x y) ∧ valuation y k
| x (k1 => k2) := valuation x k1 → valuation x k2
| x (neg k) := ¬ (valuation x k)
| x (k1 and k2) := valuation x k1 ∧ valuation x k2
| x (k1 or k2) := valuation x k1 ∨ valuation x k2
| x [ϕ] := ϕ x -- To evaluate quoted props at a world we just unquote them and apply them to the world

notation R `ϑ` := valuation R -- This is dumb notation, but I need to feed 'R' to it when I evaluate. Should probably replace with ⊢ or ⊧ or something but idk


namespace modal
-- Some common axioms

@[simp] theorem box_over_and {R : W → W → Prop} {k₁ k₂ : modal W} : ∀ x, R ϑ x (□ (k₁ and k₂) => (□k₁ and □k₂)) :=
λ x h, ⟨(λ y Rxy, (h y Rxy).left), λ y Rxy, (h y Rxy).right⟩

theorem k_axiom {ϕ₁ ϕ₂ : modal W} {R : W → W → Prop} : ∀ x : W, R ϑ x (□(ϕ₁ => ϕ₂) => (□ϕ₁ => □ϕ₂)) :=
λ _ DAtoB DA y hy, DAtoB y hy (DA y hy)

def refl_axiom {R : W → W → Prop} : Prop := 
∀ (ϕ : modal W) (x : W), R ϑ x (□ϕ => ϕ)

def trans_axiom {R : W → W → Prop} : Prop :=
∀ (ϕ : modal W) (x : W), R ϑ x (□ϕ => □□ϕ)

def dense_axiom {R : W → W → Prop} : Prop :=
∀ (ϕ : modal W) (x : W), R ϑ x (□□ϕ => □ϕ)

def serial_axiom {R : W → W → Prop} : Prop :=
∀ (ϕ : modal W) (x : W), R ϑ x (□ϕ => ◇ϕ)
 
def symm_axiom {R : W → W → Prop} : Prop :=
∀ (ϕ : modal W) (x : W), R ϑ x (ϕ => □◇ϕ)

def eucl_axiom {R : W → W → Prop} : Prop :=
∀ (ϕ : modal W) (x : W), R ϑ x (◇ϕ => □◇ϕ) 

def eucl_axiom_2 {R : W → W → Prop} : Prop :=     -- completely redundant, just for fun
∀ (ϕ : modal W) (x : W), R ϑ x (◇□ϕ => □ϕ)

def eq_axiom {R : W → W → Prop} : Prop := -- A better name for this? ϕ → □ϕ
∀ (ϕ : modal W) (x : W), R ϑ x (ϕ => □ϕ)

def conv_axiom {R : W → W → Prop} : Prop :=
∀ (ϕ : modal W) (x : W), R ϑ x (◇□ϕ => □◇ϕ)

def H_axiom {R : W → W → Prop} : Prop :=
∀ (ϕ₁ ϕ₂ : modal W) (x : W), R ϑ x (□(□ϕ₁ => ϕ₂) or □(□ϕ₂ => ϕ₁))

-- Proofs that axioms and their frame conditions correspond

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

section -- quarantining out the only classical result here
open classical
theorem H_axiom_from_H_fc {R : W → W → Prop} : @H_fc W R → @H_axiom W R :=
begin
intros h_fc ϕ₁ ϕ₂ x,
dsimp,
dsimp[H_fc] at h_fc,

cases em (∀ (y : W), (R x y) → (∀ (y_1 : W), (R y y_1) → (R ϑ y_1 ϕ₁)) → (R ϑ y ϕ₂)),
apply or.inl,
assumption,
apply or.inr,
intros y hxy h2,
cases em (R ϑ y ϕ₁) with H2 H2,
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
have H3 : (∀ (y_1 : W), (R y y_1) → (R ϑ y_1 ϕ₁)), 
intros w hyw,
simp[ϕ₁],
from hyw,
have H4, from H2 H3,
simp[ϕ₂] at H4,
from or.inr H4,

have H2, from H1 z hxz,
have H3 : (∀ (y_1 : W), (R z y_1) → (R ϑ y_1 ϕ₂)), 
intros w hzw,
simp[ϕ₂],
from hzw,
have H4, from H2 H3,
simp[ϕ₂] at H4,
from or.inl H4,
end



-- theorem test {R : W → W → Prop} : @refl_axiom W R → @refl_axiom2 W R :=
-- begin
--     intros ra1 ϕ x hϕ,
--     dsimp at hϕ,
--     constructor,
--     show W, from x,
--     constructor,
    
--     -- sorry,
--     -- from hϕ,
-- end


-- theorem test {R : W → W → Prop} : @refl_axiom2 W R → @refl_axiom W R :=
-- begin
--     intros ra2 ϕ x hϕ,
--     dsimp at hϕ,
--     dsimp,
--     apply hϕ,

-- end


-- def testaxiom1 {R : W → W → Prop} : Prop := 
-- ∀ (ϕ : W → Prop) (x : W), R ϑ x (◇[ϕ] => [ϕ])

-- def testaxiom2 {R : W → W → Prop} : Prop := 
-- ∀ (ϕ : W → Prop) (x : W), R ϑ x ([ϕ] => □[ϕ])

-- theorem test {R : W → W → Prop} : @testaxiom1 W R → @testaxiom2 W R :=
-- begin
--     intros ta1 ϕ x hϕ,
--     dsimp at hϕ,
--     dsimp,
--     intros y rxy,
--     apply ta1,
--     dsimp,
--     constructor,
--     constructor,
--     show W, from x,
--     show ϕ x,
--     assumption,


-- end

end modal



-- I was going to try proving the Lemmon-Scott result here but didn't end up getting around to it

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

@[simp] lemma boxpow_over_and {R : W → W → Prop} {k₁ k₂ : modal W} : ∀ x (j : ℕ), R ϑ x ((boxpow j (k₁ and k₂)) => ((boxpow j k₁) and (boxpow j k₂))) 
| x 0     := λ h, h
| x (j+1) := λ h, ⟨(λ y Rxy, (boxpow_over_and y j (h y Rxy)).left), (λ y Rxy, (boxpow_over_and y j (h y Rxy)).right)⟩

lemma and_over_boxpow {R : W → W → Prop} {k₁ k₂ : modal W} : ∀ x (j : ℕ), R ϑ x (((boxpow j k₁) and (boxpow j k₂)) => (boxpow j (k₁ and k₂))) 
| x 0       h :=  h
| x (j + 1) h := λ y Rxy, and_over_boxpow y j ⟨h.left y Rxy, h.right y Rxy⟩

@[simp] lemma exists_inside_lambda {W : Type} {P : W → W → Prop} : ∀ w, ∃ u, (λ w, P w u) w → (λ w, ∃ u, P w u) w :=
begin
intros w,
constructor,
intros h,
constructor,
from h, from w,
end

@[simp] lemma atom_and {W : Type} {R : W → W → Prop} {P₁ P₂ : W → Prop} : ∀ x, R ϑ x ([λ w, P₁ w ∧ P₂ w] => [λ w, P₁ w] and [λ w, P₂ w]) :=
λ x h12, h12

lemma and_atom {W : Type} {R : W → W → Prop} {P₁ P₂ : W → Prop} : ∀ x, R ϑ x ([λ w, P₁ w] and [λ w, P₂ w] => [λ w, P₁ w ∧ P₂ w]) :=
λ x h12, h12

lemma boxpow_subformula {W : Type} {R : W → W → Prop} {k₁ k₂ : modal W} : ∀ (j : ℕ), (∀ w , R ϑ w (k₁ => k₂)) → (∀ w, (R ϑ w (boxpow j (k₁ => k₂))))
| 0 h w       := h w
| (j + 1) h w := λ y Rwy, boxpow_subformula _ h _

@[simp] lemma k_axiompow {ϕ₁ ϕ₂ : modal W} {R : W → W → Prop} : ∀ (x : W) (j : ℕ), R ϑ x (boxpow j (ϕ₁ => ϕ₂) => ((boxpow j ϕ₁) => (boxpow j ϕ₂)))
| x 0     h h₁ := h h₁
| x (j+1) h h₁ := λ y Rxy, k_axiompow y j (h y Rxy) (h₁ y Rxy)

-- @[simp] def boxpow_valuation {W : Type} {R : W → W → Prop}  : ∀ (w : W) (k : modal W) (j : ℕ), R ϑ w (boxpow j k) → ∀ y, (relpow R j w y) → (R ϑ y k)
-- | w k 0       := by simp
-- | w k (j+1)   := begin
--     intros bp u rpwu,
--     dsimp at rpwu,
--     rcases rpwu with ⟨y, ⟨rpwy,Ryu⟩⟩,
--     dsimp at bp,
--     -- apply boxpow_valuation,
--     have H₁, from boxpow_valuation y [λ t, R w t ∧ (valuation R u k)] j,
--     dsimp at H₁,
--     have H₂ : valuation R y (boxpow j [λ (t : W), R w t ∧ valuation R u k]),

-- end

-- lemma boxrel {R : W → W → Prop} (k : modal W) : ∀ (m n : ℕ) (w : W), ( ∀ (y : W), relpow R n w y → (R ϑ y (boxpow (m+1) k))) → (∀ (y : W), relpow R (n+1) w y → (R ϑ y (boxpow (m) k)))
-- | 0 n w := begin
--     simp,
--     intros h u y rpnwy Ryu,
--     apply h,
--     from rpnwy,
--     from Ryu,
-- end
-- | (m+1) n w := begin
--     simp,
--     intros h u y rpnwy Ryu z Ruz,
--     apply h,
--     from rpnwy,
--     from Ryu,
--     from Ruz,
-- end

-- to prove w R^n y → y⊢□^(m+1)ϕ we can show w R^(n+1) z → z ⊢ □^m ϕ, looking "one step into the future"
lemma boxrel {R : W → W → Prop} (k : modal W) : ∀ (m n : ℕ) (w : W), ( ∀ (y : W), relpow R n w y → (R ϑ y (boxpow (m+1) k))) = (∀ (y : W), relpow R (n+1) w y → (R ϑ y (boxpow (m) k)))
| 0 n w := begin
    simp,
    constructor,

    intros h u y rpnwy Ryu,
    apply h,
    from rpnwy,
    from Ryu,

    intros h u rpnwu y Ruy,
    apply h,
    from rpnwu,
    from Ruy,
end
| (m+1) n w := begin
    simp,
    constructor,
    intros h u y rpnwy Ryu z Ruz,
    apply h,
    from rpnwy,
    from Ryu,
    from Ruz,

    intros h u rpnwu y Ruy z Ryz,
    apply h,
    from rpnwu,
    from Ruy,
    from Ryz,
end

-- if we can decrement m by incrementing n, we can keep doing this until m=0 
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

-- combine above two lemmas to show that  w R^m y → y⊢□^n ϕ is satisfied when w R^(m+n) z → z⊢ϕ is satisfied, looking "all the way into the future"
lemma boxrel2 {R : W → W → Prop} : ∀ (k : modal W) (m n : ℕ) (w : W), ( ∀ (y : W), relpow R n w y → (R ϑ y (boxpow (m) k))) = (∀ (z : W), relpow R (n+m) w z → (R ϑ z (boxpow (0) k)))
| k 0 n w := by refl
| k (m+1) n w := begin
    have H, from @induction_max (λ i j, (∀ (y : W), relpow R j w y → valuation R y (boxpow i k))) (λ i j : ℕ, @boxrel W R k i j w) (m+1) n,
    simp at H,
    simp,
    from H,
end

-- corollary: w⊢□^n ϕ is satisfied when w R^n z → z ⊢ϕ is satisfied
lemma boxrel3 {R : W → W → Prop} : ∀ (k : modal W) (m : ℕ) (w : W), R ϑ w (boxpow m k) = ∀ z, (relpow R m w z) → (R ϑ z k) :=
begin
    intros k m w,
    have H, from @boxrel2 W R k m 0 w,
    simp at H,
    simp,
    from H,
end

-- If ϕ is the proposition [λ u, w R^n u] then w⊢□^n ϕ is always true. 
theorem boxpow_of_relpow {R : W → W → Prop} : ∀ (w : W) (n : ℕ), (R ϑ w (boxpow n [λ u, relpow R n w u]))
| w 0     := eq.refl w
| w (n+1) := begin
    -- simp,
    have H, from @boxrel3 W R [λ (u : W), relpow R (n + 1) w u] (n+1) w,
    simp,
    simp at H,
    apply H.elim_right,
    intros y u rpnwu Ruy,
    constructor,
    constructor,
    from rpnwu,
    from Ruy,
end


@[simp] def hijk_axiom {R : W → W → Prop} (h i j k : ℕ) : Prop := 
∀ (ϕ : modal W) (x : W), R ϑ x ((diamondpow h (boxpow i ϕ)) => (boxpow j (diamondpow k ϕ)))

@[simp] def hijk_fc {R : W → W → Prop} (h i j k : ℕ) : Prop :=
∀ x y z : W, (relpow R h) x y ∧ (relpow R j) x z → ∃ u : W, (((relpow R i) y x) ∧ ((relpow R k) z x)) 


theorem LemmonScott_fc_from_axiom {R : W → W → Prop} : ∀ (h i j k : ℕ), (@hijk_axiom W R h i j k) → (@hijk_fc W R h i j k) 
-- | h i j (k+1) ax := sorry
-- | h i (j+1) 0 ax := sorry
-- | h (i+1) 0 0 ax := sorry
| 0 i 0 0 ax := begin
intros w u y eqwu,
cases eqwu with eq1 eq2,
cases eq1, cases eq2,
simp,
from ⟨w, ax [λ u, relpow R i w u] w (boxpow_of_relpow W w i)⟩,
end
| _ _ _ _ _ := sorry
-- | (h+2) 0 0 0 ax := sorry --begin
-- -- simp[hijk_fc],
-- -- simp[hijk_axiom] at ax,
-- -- intros x y z u Rxu,
-- -- intros pRuy eqxz,
-- -- constructor,
-- -- swap,
-- -- from eq.symm eqxz,
-- -- constructor,
-- -- assumption,

-- -- -- have eqyx, from ax (λ u, y = u) x y Rxy (eq.refl y),
-- -- -- simp at eqyx,
-- -- -- from ⟨⟨y, eqyx⟩, eq.symm eqxz⟩,
-- -- end
-- -- | (h+1) 0 0 0 ax := begin
-- -- intros x y z ih,
-- -- simp,

-- -- simp at ih,
-- -- rcases ih with ⟨⟨u, ⟨rxu, hh⟩⟩, h⟩,
-- -- dsimp at ax,
-- -- constructor,
-- -- -- constructor,

-- -- end
-- -- | 1 0 0 0 ax := begin
-- -- simp[hijk_fc],
-- -- simp[hijk_axiom] at ax,
-- -- intros x y z,
-- -- intros Rxy eqxz,
-- -- have eqyx, from ax (λ u, y = u) x y Rxy (eq.refl y),
-- -- simp at eqyx,
-- -- from ⟨⟨y, eqyx⟩, eq.symm eqxz⟩,
-- -- end
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

