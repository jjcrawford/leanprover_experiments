import modal_logic.basic
import modal_logic.general_axiom
import init.data.list.basic

variable {atm : Type}
open list




def pv_in : (@modal atm) → list atm 
| #[p] := [p]
| not ψ := pv_in ψ
| (ψ₁ and ψ₂) := (pv_in ψ₁) ++ (pv_in ψ₂)
| (ψ₁ or ψ₂) := (pv_in ψ₁) ++ (pv_in ψ₂)
| (ψ₁ => ψ₂) := (pv_in ψ₁) ++ (pv_in ψ₂)
| □ψ := pv_in ψ
| ◇ψ := pv_in ψ

-- pv_in_modal
def pv_in_modal (ϕ : @modal atm) (p : atm) : Prop := p ∈ (pv_in ϕ)

-- at_pv
def at_pv : list atm → ℕ → (option atm)
| list.nil i        := option.none
| (cons q l') 0     := q
| (cons q l') (i+1) := at_pv l' i


def is_neg_pre : (@modal atm) → ℕ → bool
| #[p] i := false
| (not p) i := ¬(is_neg_pre p i)
| (ψ₁ and ψ₂) i := if i ≤ (length (pv_in ψ₁)) then is_neg_pre ψ₁ i
                    else is_neg_pre ψ₂ (i-(length (pv_in ψ₁)))
| (ψ₁ or ψ₂) i := if i ≤ (length (pv_in ψ₁)) then is_neg_pre ψ₁ i
                    else is_neg_pre ψ₂ (i-(length (pv_in ψ₁)))
| (ψ₁ => ψ₂) i := if i ≤ (length (pv_in ψ₁)) then ¬(is_neg_pre ψ₁ i)
                    else is_neg_pre ψ₂ (i-(length (pv_in ψ₁)))
| (□ψ) i := is_neg_pre ψ i
| (◇ψ) i := is_neg_pre ψ i


-- occ_in_modal
def occ_in_modal (ϕ : @modal atm) (i : ℕ) : Prop :=
(i < (length (pv_in ϕ)))

inductive is_neg (ϕ : @modal atm) (i : ℕ) : Prop
| occ_neg : occ_in_modal ϕ i -> is_neg_pre ϕ i -> is_neg.

-- is_pos
def is_pos_pre : (@modal atm) → ℕ → bool
| #[p] i := 1 = i
| (not ψ) i := ¬(is_pos_pre ψ i)
| (ψ₁ and ψ₂) i := if i ≤ (length (pv_in ψ₁)) then is_pos_pre ψ₁ i
                    else is_pos_pre ψ₂ (i - (length (pv_in ψ₂)))
| (ψ₁ or ψ₂) i := if i ≤ (length (pv_in ψ₁)) then is_pos_pre ψ₁ i
                    else is_pos_pre ψ₂ (i-(length (pv_in ψ₁)))
| (ψ₁ => ψ₂) i := if i ≤ (length (pv_in ψ₁)) then ¬ (is_pos_pre ψ₁ i)
                    else is_pos_pre ψ₂ (i-(length (pv_in ψ₁)))
| (□ψ) i := is_pos_pre ψ i
| (◇ψ) i := is_pos_pre ψ i

inductive is_pos (ϕ : @modal atm) (i : ℕ) : Prop
| occ_pos : occ_in_modal ϕ i → (is_pos_pre ϕ i) → is_pos


-- p_is_pos
def p_is_pos (ϕ : @modal atm) (p : atm) : Prop :=
pv_in_modal ϕ p ∧ (∀ (i : ℕ), occ_in_modal ϕ i → (some p) = at_pv (pv_in ϕ) i → is_pos ϕ i)

def p_is_neg (ϕ : @modal atm) (p : atm) : Prop :=
pv_in_modal ϕ p ∧ (∀ (i : ℕ), occ_in_modal ϕ i → (some p) = at_pv (pv_in ϕ) i → is_neg ϕ i)


--pos
def spos (ϕ : @modal atm) : Prop :=
∀ p, pv_in_modal ϕ p → p_is_pos ϕ p

def sneg (ϕ : @modal atm) : Prop :=
∀ p, pv_in_modal ϕ p → p_is_neg ϕ p

def uniform (ϕ : @modal atm) : Prop :=
∀ p, pv_in_modal ϕ p → p_is_pos ϕ p ∨ p_is_neg ϕ p

-- vsSahlq_setup

inductive vsSahlq_ante : (@modal atm) → Prop
| vsSahlq_ante_atom : Π (p : atm), vsSahlq_ante #[p]
| vsSahlq_ante_mconj : Π {ψ₁ ψ₂ : @modal atm}, vsSahlq_ante ψ₁ → vsSahlq_ante ψ₂ → vsSahlq_ante (ψ₁ and ψ₂)
| vsSahlq_ante_dia : Π {ψ : @modal atm}, vsSahlq_ante ψ → vsSahlq_ante (◇ψ)


inductive vsSahlq : (@modal atm) → Prop
| vsSahlq_y : Π {ϕ₁ ϕ₂ : @modal atm}, vsSahlq_ante ϕ₁ → spos ϕ₂ → vsSahlq (ϕ₁ => ϕ₂)

-- def corresponds (ϕ : @modal atm) (α : SecOrder)

lemma vsSahlq_ante_dec : ∀ (ϕ : @modal atm), decidable (vsSahlq_ante ϕ) :=
begin -- this can probably afford to be optimised, but whatever
    intros ϕ,
    induction ϕ with ϕ ϕ_ih; 
    try {solve1 {left, intros h, cases h}}; 
    try {solve1 {right;constructor;assumption}};
    try {try {cases ϕ_ih}; try {cases ϕ_ih_a}; try{cases ϕ_ih_a_1}};
    try {solve1 {left, intros h, cases h; contradiction}}; 
    try {solve1 {right;constructor;assumption}},
end

lemma vsSahlq_ex : ∀ (ϕ : @modal atm), vsSahlq ϕ → ∃ (ϕ₁ ϕ₂ : @modal atm), vsSahlq_ante ϕ₁ ∧ spos ϕ₂ :=
by rintros ϕ ⟨ϕ₁, ϕ₂, anteϕ₁, pϕ₂⟩; from ⟨ϕ₁, ⟨ϕ₂, ⟨anteϕ₁, pϕ₂⟩⟩⟩

lemma vsSahlq_ante_mconj_rev : ∀ (ϕ₁ ϕ₂ : @modal atm), vsSahlq_ante (ϕ₁ and ϕ₂) → (vsSahlq_ante ϕ₁ ∧ vsSahlq_ante ϕ₂) :=
begin
    rintros ϕ₁ ϕ₂ h, 
    cases h with _ _ _ h₁ h₂,
    from ⟨h₁, h₂⟩,
end

-- lemma vsSahlq_ante_conjSO_exFO_relatSO: ∀ (ϕ : @modal atm) x, vsSahlq_ante ϕ → conjSO_exFO_relatSO (ST ϕ x) :=
-- begin

-- end