import algebra.field
import algebra.ring
import tactic.ring
import tactic.tidy

import data.nat.prime

import init.data.nat.basic
import logic.basic

import algebra.ring

-- import tactic.fin_cases
-- import data.real.basic
-- open ring
-- open field

class are_zero_divisors {α : Type} [field α] (a x : α) : Prop :=
(anz : a ≠ 0)
(xnz : x ≠ 0)
(zd : a*x = 0)

theorem fields_have_no_zero_divisors {α : Type} [field α] : ¬ ∃ (a x : α), are_zero_divisors a x :=
begin
rintros ⟨a, ⟨x, ⟨anz, xnz, zd⟩⟩⟩,
apply @one_ne_zero α _,
rw [←zero_mul (a⁻¹ * x⁻¹), ←zd],
suffices : (a * x) * (a⁻¹ * x⁻¹) = (a/a) * (x/x),
rw[this, div_self, div_self, mul_one]; assumption,
ring,
end

-- open nat.prime
open nat


def even (n : ℤ) : Prop := ∃ k : ℤ, n = 2 * k

theorem sum_of_evens_is_even : ∀ (m n : ℤ) (em : even m) (en : even n), even (m + n)
:= λ m n ⟨km, hm⟩ ⟨kn, hn⟩, ⟨km+kn, eq.symm (eq.trans (ring.left_distrib 2 km kn) (eq.symm (congr (congr (refl has_add.add) hm) hn)))⟩

-- begin
--     constructor, -- let's see what we need to construct evenness of m+n (exists.mk)

--     -- At this point we have two goals. We have to specify what integer multiplies by 2 to get m+n,
--     -- and we also have to prove that it satisfies this property.

--     -- Let's use the show tactic to specify the integer first:
--     show ℕ, 
--     from km + kn, -- of course, it's the sum of the ks we used for m and n individually

--     -- now we have to show that it satisfies the desired property
   
--     have h1 : m + n = 2*km + 2 * kn, -- let's prove this lemma real quick
--     congr, -- which is true because the terms are respectively congruent
--     assumption, -- and we know the equalities individually
--     assumption,

--     -- by transitivity of equality, we can now rewrite our goal
--     apply eq.trans h1, -- trans rights

--     ring, -- someone made us a program that just hits these equational proofs with common simplification methods from the algebra of rings
--     -- we are done
-- end



-- mutual def even, odd
-- with even : nat → bool
-- | 0     := tt
-- | (a+1) := odd a
-- with odd : nat → bool
-- | 0     := ff
-- | (a+1) := even a


-- def odd (n : ℕ) : Prop := ∃ k : ℕ, n = 2 * k + 1
-- instance odd_decidable : decidable_pred odd 
-- | 0    := begin 

-- unfold odd,
-- constructor,
-- intros hn,
-- cases hn with k hn,
-- have h1 : 0 = 2 * 0,
-- refl,
-- rw h1 at hn,
-- simp at hn,
-- have h2 : 0 < 1,
-- simp,
-- have h3 : 0 ≥ 1,
-- have H1, from @nat.le_of_add_le_add_left,
-- -- apply nat.le_of_add_le_add_left,

--  end
-- | (succ n) := begin sorry end

-- :=
-- begin
--     unfold decidable_pred,
--     intros n,

-- end

-- theorem all_non2_primes_odd : ∀ p : ℕ, (prime p) → (p≠2) → (odd p) :=
-- begin
--     intros p,
--     intros prime_p,
--     intros pneq2,

--     cases prime_p with pgeq2 ph,
    

--     -- induction p,
--     constructor,


-- end


-- theorem t {p : ℕ} : prime p :=
-- begin

-- end

-- inductive logical_and {A B : Prop} 
-- (A → B → logical_and)

theorem and_commutative {A B : Prop} : (A ∧ B) → (B ∧ A) :=
begin
intros h_A_and_B, -- it's a function, so lets suppose we have a proof object of this type
cases h_A_and_B with h_A h_B, -- unfold the definition of A and B
constructor, -- unfold the definition of "and" in the goal so we can see what we really need to prove
from h_B, -- provide our proof of B
from h_A -- provide our proof of A
end

theorem and_commutative2 {A B : Prop} : (A ∧ B) → (B ∧ A) :=
λ h_A_and_B, @and.rec_on A B (B ∧ A) h_A_and_B (λ h_A h_B, ⟨h_B, h_A⟩)


theorem and_commutative3 {A B : Prop} : (A ∧ B) → (B ∧ A) :=
λ ⟨h_A, h_B⟩, ⟨h_B, h_A⟩ -- pattern matching in our lambda

theorem and_commutative4 {A B : Prop} : (A ∧ B) → (B ∧ A)
| ⟨h_A, h_B⟩ := ⟨h_B, h_A⟩ -- haskellier pattern matching

-- here the ⟨ ⟩ brackets are notation for 'constructor' like above. this is actually just a function and.mk defined as part of the inductive definition of 'and'

-- theorem all_non2_primes_odd : ∀ p : ℕ, (prime p) → (p≠2) → (odd p)
-- open real
-- noncomputable def phi := (1 + sqrt 5) / 2
-- lemma phi_squared : phi ^ 2 = phi + 1 :=
-- by rw [phi, div_pow (_:ℝ) two_ne_zero, pow_two, add_mul_self_eq,
--   mul_self_sqrt (show (0:ℝ) ≤ 5, by norm_num)]; ring

-- import data.nat.prime
-- variable (ℝ : Type)
-- variable [decidable_linear_ordered_comm_group ℝ]

-- open classical

-- theorem all_subsequences_of_a_sequence_which_converges_to_zero_converge_to_zero (seq : ℕ → ℝ) (subseq : ℕ → ℕ) (subseq_geq : (∀ n : ℕ, subseq n ≥ n)) : 
-- (∀ (ε : ℝ), ∃ (N : ℕ), ∀ (n > N), abs (seq n) < ε) → (∀ (ε : ℝ), ∃ (N : ℕ), ∀ (n > N), abs (seq (subseq n)) < ε)  :=
-- begin
-- intro P,
-- intro ε,
-- have H, from P ε,
-- choose N hN using H,

-- constructor,
-- swap,

-- from N,


-- intros n hn,
-- have H1, from hN (subseq n),

-- apply H1,

-- apply lt_of_lt_of_le,
-- from hn,
-- apply subseq_geq,

-- end

-- theorem stackexchange : 
-- (∀ (n > 1), ∃ (p : ℕ), (prime p) ∧ (n < p) ∧ (p < 2*n)) → 


-- theorem q4 (α : Type) (X Y : α) : ((λ (f : α → α), (λ (x : α), f (f x))) = (λ f, (λ x, f x))) → X = Y := 
-- begin
--     intros,
--     have H1 : (λ (f : α → α) (x : α), f (f x)) (λ ω, X) = λ (f : α → α) (x : α), f x (λ ω, X),

-- end



-- inductive expression
-- | quoted : string → expression
-- | apply : expression → expression
-- | lambda : string → expression → expression


-- theorem test {α : Type} {P : α → Prop} : (∃ (a : α), ¬ P a) → (¬ ∀ (a : α), P a) :=
-- λ h nh, @Exists.cases_on α (λ x, ¬ P x) false h (λ a nha, nha (nh a))

-- theorem thrm1 {A B : Type} {P : B → A → Prop} : ∀ (b:B), ∀ (a:A), (P b a) → ∃ (f:B → A), (f b = a) ∧ ∀ (bb:B), P bb (f bb) := 
-- begin
--     intros b a Pab,
--     constructor,
--     constructor,
--     show B → A,
--     intros bb,
-- end

-- theorem thrm1 {A B : Type} {P : B → A → Prop} : (∀ (b : B), ∀ (a : A), (P b a)) → (∀ (a : A) (b : B), ∃ (f:B → A), (f b = a) ∧ ∀ (bb:B), P bb (f bb)) := 
-- begin
--     intros b a bb,
--     have f : B → A,
--     intros bbb,
--     have H1, from b bbb,
    

--     constructor,
--     constructor,
--     show B → A,
--     intros bb,
-- end

--     -- λ b:B, λ a:A, 
--     -- assume h: P b a, 
-- -- 
-- -- sorry