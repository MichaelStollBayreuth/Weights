import Weights.Uniqueness

namespace Weight

/-!
## Basic Intervals

We define *(feasible) basic intervals* and derive the relevant properties.
-/

/-- A *basic interval* is an interval `[a₁/b₁, a₂/b₂]` whose endpoints are nonnegative
rational numbers (or `∞ = 1/0`) such that `a₂ b₁ - a₁ b₂ = 1`.
Such an interval can be obtained by starting from `[0/1, 1/0]` and successively splitting
an interval `[a₁/b₁, a₂/b₂]` into the two intervals `[a₁/b₁, (a₁+a₂)/(b₁+b₂)]` and
`[(a₁+a₂)/(b₁+b₂), a₂/b₂]`-/
inductive BasicInterval
| base : BasicInterval
| left (_ : BasicInterval) : BasicInterval
| right (_ : BasicInterval) : BasicInterval

namespace BasicInterval

/-! Compute the endpoint data and prove the relation. -/

/-- Extract numerators and denominators of the endpoints. -/
def data : BasicInterval → (ℕ × ℕ) × (ℕ × ℕ)
| base     => ((0, 1), (1, 0))
| left I'  => let ((a₁, b₁), (a₂, b₂)) := I'.data
              ((a₁, b₁), (a₁ + a₂, b₁ + b₂))
| right I' => let ((a₁, b₁), (a₂, b₂)) := I'.data
              ((a₁ + a₂, b₁ + b₂), (a₂, b₂))

/-- The numerator of the left endpoint -/
def a₁ (I : BasicInterval) : ℕ := I.data.1.1

/-- The denominator of the left endpoint -/
def b₁ (I : BasicInterval) : ℕ := I.data.1.2

/-- The numerator of the right endpoint -/
def a₂ (I : BasicInterval) : ℕ := I.data.2.1

/-- The denominator of the right endpoint -/
def b₂ (I : BasicInterval) : ℕ := I.data.2.2

-- attribute [pp_dot] a₁ b₁ a₂ b₂

-- Boilerplate
@[simp] lemma base_a₁ : base.a₁ = 0 := rfl

@[simp] lemma base_b₁ : base.b₁ = 1 := rfl

@[simp] lemma base_a₂ : base.a₂ = 1 := rfl

@[simp] lemma base_b₂ : base.b₂ = 0 := rfl

@[simp] lemma left_a₁ (I : BasicInterval) : (left I).a₁ = I.a₁ := rfl

@[simp] lemma left_b₁ (I : BasicInterval) : (left I).b₁ = I.b₁ := rfl

@[simp] lemma left_a₂ (I : BasicInterval) : (left I).a₂ = I.a₁ + I.a₂ := rfl

@[simp] lemma left_b₂ (I : BasicInterval) : (left I).b₂ = I.b₁ + I.b₂ := rfl

@[simp] lemma right_a₁ (I : BasicInterval) : (right I).a₁ = I.a₁ + I.a₂ := rfl

@[simp] lemma right_b₁ (I : BasicInterval) : (right I).b₁ = I.b₁ + I.b₂ := rfl

@[simp] lemma right_a₂ (I : BasicInterval) : (right I).a₂ = I.a₂ := rfl

@[simp] lemma right_b₂ (I : BasicInterval) : (right I).b₂ = I.b₂ := rfl


lemma rel : (I : BasicInterval) → I.a₂ * I.b₁ = I.a₁ * I.b₂ + 1
| base     => by simp
| left I'  => by simp [add_mul, mul_add, I'.rel, add_assoc]
| right I' => by simp [add_mul, mul_add, I'.rel, add_assoc, add_comm]

lemma b₁_pos : (I : BasicInterval) → 0 < I.b₁
| base     => by simp
| left I'  => by simp [I'.b₁_pos]
| right I' => by simp [I'.b₁_pos]

lemma a₂_pos : (I : BasicInterval) → 0 < I.a₂
| base     => by simp
| left I'  => by simp [I'.a₂_pos]
| right I' => by simp [I'.a₂_pos]

lemma coprime (I : BasicInterval) : Nat.Coprime (I.a₂ * I.b₁) (I.a₁ * I.b₂) := by
  rw [Nat.Coprime, Nat.gcd_eq_iff]
  simp? says simp only [isUnit_one, IsUnit.dvd, Nat.isUnit_iff, Nat.dvd_one, true_and]
  intros c h₁ h₂
  rw [I.rel] at h₁
  exact Nat.dvd_one.mp <| (Nat.dvd_add_right h₂).mp h₁

lemma coprime₁ (I : BasicInterval) : I.a₁.Coprime I.b₁ :=
  (Nat.Coprime.coprime_mul_right_right <| Nat.Coprime.coprime_mul_left I.coprime).symm

lemma coprime₂ (I : BasicInterval) : I.a₂.Coprime I.b₂ :=
  Nat.Coprime.coprime_mul_right (k := I.b₁) <| Nat.Coprime.coprime_mul_left_right I.coprime

/-- A fraction `a/b` lies in the basic interval `I`. -/
def mem (a b : ℕ) (I : BasicInterval) : Prop := b * I.a₁ ≤ a * I.b₁ ∧ a * I.b₂ ≤ b * I.a₂

lemma mem_of_proportional {I : BasicInterval} {a b g : ℕ} (hg : 0 < g) (h : mem (a * g) (b * g) I) :
    mem a b I := by
  obtain ⟨h₁, h₂⟩ := h
  simp_rw [mul_comm _ g, mul_assoc] at h₁ h₂
  exact ⟨Nat.le_of_mul_le_mul_left h₁ hg, Nat.le_of_mul_le_mul_left h₂ hg⟩

/-- A fraction `a/b` lies in the interior of the basic interval `I`. -/
def mem_interior (a b : ℕ) (I : BasicInterval) : Prop := b * I.a₁ < a * I.b₁ ∧ a * I.b₂ < b * I.a₂

lemma eq_or_eq_or_mem_interior_of_mem {a b : ℕ} {I : BasicInterval} (h : mem a b I) :
    a * I.b₁ = b * I.a₁ ∨ a * I.b₂ = b * I.a₂ ∨ mem_interior a b I := by
  obtain ⟨h₁, h₂⟩ := h
  cases' h₁.eq_or_lt with H₁ H₁
  · exact Or.inl H₁.symm
  cases' h₂.eq_or_lt with H₂ H₂
  · exact Or.inr <| Or.inl H₂
  exact Or.inr <| Or.inr ⟨H₁, H₂⟩

lemma mem_of_mem_interior {a b : ℕ} {I : BasicInterval} (h : mem_interior a b I) : mem a b I := by
  simp only [mem, mem_interior] at h ⊢
  constructor <;> linarith

@[simp]
lemma mem_base (a b : ℕ) : mem a b base := by simp [mem]

lemma mem_of_mem_left {a b : ℕ} (I : BasicInterval) (h : mem a b I.left) : mem a b I := by
  obtain ⟨h₁, h₂⟩ := h
  simp at h₁ h₂
  exact ⟨h₁, by linarith⟩

lemma mem_of_mem_right {a b : ℕ} (I : BasicInterval) (h : mem a b I.right) : mem a b I := by
  obtain ⟨h₁, h₂⟩ := h
  simp at h₁ h₂
  exact ⟨by linarith, h₂⟩

lemma mem_left_or_mem_right {a b : ℕ} (I : BasicInterval) (h : mem a b I) :
    mem a b I.left ∨ mem a b I.right := by
  by_cases hl : mem a b I.left
  · exact Or.inl hl
  · unfold mem at h hl ⊢
    rw [@not_and_or] at hl
    cases' hl with hl hl <;> push_neg at hl <;> simp at hl ⊢
    · exact Or.inl ⟨h.1, by linarith⟩
    · refine Or.inr ⟨hl.le, h.2⟩

/-- A fraction `a/b` that lies in a basic interval `[a₁/b₁, a₂/b₂]` satisfies
`a = k₁ a₁ + k₂ a₂` and `b = k₁ b₁ + k₂ b₂` for some natural numbers `k₁` and `k₂`. -/
lemma exists_of_mem {a b : ℕ} {I : BasicInterval} (h : mem a b I) :
    ∃ k₁ k₂ : ℕ, a = k₁ * I.a₁ + k₂ * I.a₂ ∧ b = k₁ * I.b₁ + k₂ * I.b₂ := by
  induction I with
  | base       => simp
  | left I ih  =>
    obtain ⟨k₁', k₂, H₁, H₂⟩ := ih (mem_of_mem_left I h)
    simp only [left_a₁, left_a₂, left_b₁, left_b₂]
    have ⟨k₁, hk⟩ : ∃ k, k₁' = k + k₂ := by
      rw [← le_iff_exists_add']
      obtain ⟨_, h₂⟩ := h
      simp only [H₁, left_b₂, mul_add, add_mul, H₂, left_a₂] at h₂
      have rel := I.rel
      zify at h₂ rel ⊢
      rw [← sub_nonneg] at h₂ ⊢
      convert h₂ using 1
      linear_combination (k₂ - k₁') * rel
    rw [hk] at H₁ H₂
    refine ⟨k₁, k₂, ?_, ?_⟩ <;> linarith
  | right I ih =>
    obtain ⟨k₁, k₂', H₁, H₂⟩ := ih (mem_of_mem_right I h)
    simp only [right_a₁, right_a₂, right_b₁, right_b₂]
    have ⟨k₂, hk⟩ : ∃ k, k₂' = k + k₁ := by
      rw [← le_iff_exists_add']
      obtain ⟨h₁, _⟩ := h
      simp only [H₂, right_a₁, mul_add, add_mul, H₁, right_b₁] at h₁
      have rel := I.rel
      zify at h₁ rel ⊢
      rw [← sub_nonneg] at h₁ ⊢
      convert h₁ using 1
      linear_combination (k₁ - k₂') * rel
    rw [hk] at H₁ H₂
    refine ⟨k₁, k₂, ?_, ?_⟩ <;> linarith

/-- A fraction `a/b` that lies in the interior of a basic interval `[a₁/b₁, a₂/b₂]` satisfies
`a = k₁ a₁ + k₂ a₂` and `b = k₁ b₁ + k₂ b₂` for some positive natural numbers `k₁` and `k₂`. -/
lemma exists_of_mem_interior {a b : ℕ} {I : BasicInterval} (h : mem_interior a b I) :
    ∃ k₁ k₂ : ℕ, 0 < k₁ ∧ 0 < k₂ ∧ a = k₁ * I.a₁ + k₂ * I.a₂ ∧ b = k₁ * I.b₁ + k₂ * I.b₂ := by
  obtain ⟨k₁, k₂, h₁, h₂⟩ := exists_of_mem (mem_of_mem_interior h)
  simp only [mem_interior] at h
  refine ⟨k₁, k₂, Nat.pos_of_ne_zero ?_, Nat.pos_of_ne_zero ?_, h₁, h₂⟩
  · rintro rfl
    simp only [zero_mul, zero_add] at h₁ h₂
    replace h := h.2
    simp only [h₁, mul_assoc, h₂, mul_comm I.a₂] at h
    exact lt_irrefl _ h
  · rintro rfl
    simp only [zero_mul, add_zero] at h₁ h₂
    replace h := h.1
    simp only [h₁, mul_assoc, h₂, mul_comm I.a₁] at h
    exact lt_irrefl _ h

/-- A basic interval is *feasible* if it is minimal such that `a₁+b₁, a₂+b₂ ≤ d`. -/
def feasible (d : ℕ) (I : BasicInterval) : Prop :=
  I.a₁ + I.b₁ ≤ d ∧ I.a₂ + I.b₂ ≤ d ∧ d < I.a₁ + I.a₂ + I.b₁ + I.b₂

lemma feasible_base : base.feasible 1 := by simp [feasible]

lemma feasible_left_or_right {d : ℕ} {I : BasicInterval} (h : I.feasible d) :
    I.feasible d.succ ∨ (I.left.feasible d.succ ∧ I.right.feasible d.succ) := by
  by_cases h' : I.feasible d.succ
  · exact Or.inl h'
  · simp only [feasible] at h h' ⊢
    simp only [not_and_or, not_le, not_lt] at h'
    rcases h' with _ | _ | _ <;> try exfalso; linarith
    refine Or.inr ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩ <;> simp <;> linarith

/-- Every fraction `a/b` is contained in some feasible basic interval. -/
lemma mem_feasible (d a b : ℕ) [NeZero d] : ∃ (I : BasicInterval), I.feasible d ∧ mem a b I := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne d)
  induction' n with n ih
  · exact ⟨base, feasible_base, mem_base _ _⟩
  · obtain ⟨I', hf, hm⟩ := ih
    cases feasible_left_or_right hf with
    | inl h => exact ⟨I', h, hm⟩
    | inr h =>
      rcases mem_left_or_mem_right I' hm with hm | hm
      · exact ⟨I'.left, h.1, hm⟩
      · exact ⟨I'.right, h.2, hm⟩

/-- If `a/b` is in the interior of a feasible interval, then `a + b > d`. -/
lemma gt_of_mem_interior_feasible {a b d : ℕ} {I : BasicInterval}
    (hI : I.feasible d) (hab : mem_interior a b I) : d < a + b := by
  obtain ⟨k₁, k₂, hk₁, hk₂, h₁, h₂⟩ := exists_of_mem_interior hab
  calc
    d < I.a₁ + I.a₂ + I.b₁ + I.b₂                       := hI.2.2
    _ = I.a₁ + I.b₁ + (I.a₂ + I.b₂)                     := by abel
    _ ≤ k₁ * (I.a₁ + I.b₁) + k₂ * (I.a₂ + I.b₂)         :=
      Nat.add_le_add (Nat.le_mul_of_pos_left _ hk₁) (Nat.le_mul_of_pos_left _ hk₂)
    _ = k₁ * I.a₁ + k₂ * I.a₂ + (k₁ * I.b₁ + k₂ * I.b₂) := by ring
    _ = a + b                                           := by rw [h₁, h₂]

end BasicInterval
