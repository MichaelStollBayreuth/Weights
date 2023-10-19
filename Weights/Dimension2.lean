import Weights.Uniqueness

namespace Weight

/-!
## Dimension 2

We attempt a formalization of Theorem 1.6 in the paper, which says that in the case `n = 2`,
the weights in a minimal complete set of weight vectors have entries bounded by `d`.
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

/- structure BasicInterval where
  a₁ : ℕ
  b₁ : ℕ
  a₂ : ℕ
  b₂ : ℕ
  rel : a₂ * b₁ = a₁ * b₂ + 1 -/

namespace BasicInterval

/-! Compute the endpoint data and prove the relation. -/
def data : BasicInterval → (ℕ × ℕ) × (ℕ × ℕ)
| base     => ((0, 1), (1, 0))
| left I'  => let ((a₁, b₁), (a₂, b₂)) := I'.data
              ((a₁, b₁), (a₁ + a₂, b₁ + b₂))
| right I' => let ((a₁, b₁), (a₂, b₂)) := I'.data
              ((a₁ + a₂, b₁ + b₂), (a₂, b₂))

def a₁ (I : BasicInterval) : ℕ := I.data.1.1

def b₁ (I : BasicInterval) : ℕ := I.data.1.2

def a₂ (I : BasicInterval) : ℕ := I.data.2.1

def b₂ (I : BasicInterval) : ℕ := I.data.2.2

attribute [pp_dot] a₁ b₁ a₂ b₂

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


/-- A fraction `a/b` lies in the basic interval `I`. -/
def mem (a b : ℕ) (I : BasicInterval) : Prop := b * I.a₁ ≤ a * I.b₁ ∧ a * I.b₂ ≤ b * I.a₂

/-- A fraction `a/b` lies in the interior of the basic interval `I`. -/
def mem_interior (a b : ℕ) (I : BasicInterval) : Prop := b * I.a₁ < a * I.b₁ ∧ a * I.b₂ < b * I.a₂

lemma mem_of_mem_interior {a b : ℕ} {I : BasicInterval} (h : mem_interior a b I) : mem a b I := by
  simp only [mem, mem_interior] at h ⊢
  constructor <;> linarith

@[simp]
lemma mem_base (a b : ℕ) : mem a b base := by simp [mem]

lemma mem_of_mem_left {a b : ℕ} (I : BasicInterval) (h : mem a b I.left) : mem a b I := by
  obtain ⟨h₁, h₂⟩ := h
  simp at h₁ h₂
  exact ⟨h₁, by linarith⟩
  done

lemma mem_of_mem_right {a b : ℕ} (I : BasicInterval) (h : mem a b I.right) : mem a b I := by
  obtain ⟨h₁, h₂⟩ := h
  simp at h₁ h₂
  exact ⟨by linarith, h₂⟩
  done

lemma mem_left_or_mem_right {a b : ℕ} (I : BasicInterval) (h : mem a b I) :
    mem a b I.left ∨ mem a b I.right := by
  by_cases hl : mem a b I.left
  · exact Or.inl hl
    done
  · unfold mem at h hl ⊢
    rw [@not_and_or] at hl
    cases' hl with hl hl <;> push_neg at hl <;> simp at hl ⊢
    · exact Or.inl ⟨h.1, by linarith⟩
      done
    · refine Or.inr ⟨hl.le, h.2⟩
      done
    

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
      done
    rw [hk] at H₁ H₂
    refine ⟨k₁, k₂, ?_, ?_⟩ <;> linarith
    done
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
      done
    rw [hk] at H₁ H₂
    refine ⟨k₁, k₂, ?_, ?_⟩ <;> linarith
    done

/-- A fraction `a/b` that lies in a basic interval `[a₁/b₁, a₂/b₂]` satisfies
`a = k₁ a₁ + k₂ a₂` and `b = k₁ b₁ + k₂ b₂` for some positive natural numbers `k₁` and `k₂`. -/
lemma exists_of_mem_interior {a b : ℕ} {I : BasicInterval}  (h : mem_interior a b I) :
    ∃ k₁ k₂ : ℕ, 0 < k₁ ∧ 0 < k₂ ∧ a = k₁ * I.a₁ + k₂ * I.a₂ ∧ b = k₁ * I.b₁ + k₂ * I.b₂ := by
  obtain ⟨k₁, k₂, h₁, h₂⟩ := exists_of_mem (mem_of_mem_interior h)
  simp only [mem_interior] at h
  refine ⟨k₁, k₂, Nat.pos_of_ne_zero ?_, Nat.pos_of_ne_zero ?_, h₁, h₂⟩
  · rintro rfl
    simp only [zero_mul, zero_add] at h₁ h₂
    replace h := h.2
    simp only [h₁, mul_assoc, h₂, mul_comm I.a₂] at h
    exact lt_irrefl _ h
    done
  · rintro rfl
    simp only [zero_mul, add_zero] at h₁ h₂ 
    replace h := h.1
    simp only [h₁, mul_assoc, h₂, mul_comm I.a₁] at h
    exact lt_irrefl _ h
    done

/-- A basic interval is *feasible* if it is minimal such that `a₁+b₁, a₂+b₂ ≤ d`. -/
def feasible (d : ℕ) (I : BasicInterval) : Prop :=
  I.a₁ + I.b₁ ≤ d ∧ I.a₂ + I.b₂ ≤ d ∧ d < I.a₁ + I.a₂ + I.b₁ + I.b₂

lemma feasible_base : base.feasible 1 := by simp only [feasible, and_self]

lemma feasible_left_or_right {d : ℕ} [NeZero d] {I : BasicInterval} (h : I.feasible d) :
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
      Nat.add_le_add (Nat.le_mul_of_pos_left hk₁) (Nat.le_mul_of_pos_left hk₂)
    _ = k₁ * I.a₁ + k₂ * I.a₂ + (k₁ * I.b₁ + k₂ * I.b₂) := by ring
    _ = a + b                                           := by rw [h₁, h₂]
  done

end BasicInterval

/-- The normalized weight vector of dimension `n = 2` associated to a fraction `a/b` -/
def of_fraction (d a b : ℕ) : Weight 2 d := ![0, b, a + b]

lemma pair'_of_fraction (d a b : ℕ) (z : Fin (Nat.succ 2) → ℤ) :
    pair' (of_fraction d a b ) z = a * z 2 + b * (z 1 + z 2) := by
  simp only [of_fraction, pair']
  rw [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  rw [Matrix.head_cons, Matrix.tail_cons, Matrix.head_cons]
  push_cast
  ring
  done

lemma pair'_of_fraction_add (d a₁ b₁ a₂ b₂ : ℕ) :
    pair' (of_fraction d (a₁ + a₂) (b₁ + b₂)) =
      pair' (of_fraction d a₁ b₁) + pair' (of_fraction d a₂ b₂) := by
  ext z
  simp_rw [Pi.add_apply, pair'_of_fraction]
  push_cast
  ring
  done

lemma pair'_of_fraction_mul (d a b k : ℕ) (z : Fin 3 → ℤ) :
    pair' (of_fraction d (k * a) (k * b)) z = k * pair' (of_fraction d a b) z := by
  simp_rw [pair'_of_fraction]
  push_cast
  ring
  done


/-- The fraction `a/b`  is an element of `S_≤`. -/
def mem_S_le (d : ℕ) (a b : ℤ): Prop :=
  0 < b ∧
  ∃ (i₁ i₂ : ℕ), 3 * i₁ + 3 * i₂ ≤ 2 * d ∧ d < 3 * i₂ ∧
                 a * (3 * i₂ - d) = b * (2 * d - 3 * i₁ - 3 * i₂)

/-- The fraction `a/b` is an element of `S_≥`. -/
def mem_S_ge (d : ℕ) (a b : ℤ): Prop :=
  0 < a ∧
  ∃ (i₁ i₂ : ℕ), i₁ + i₂ ≤ d ∧ 2 * d < 3 * i₁ + 3 * i₂ ∧ 3 * i₂ ≤ d ∧
                 a * (3 * i₂ - d) = b * (2 * d - 3 * i₁ - 3 * i₂)

open BasicInterval

/-- If `I = [a₁/b₁, a₂/b₂]` is a basic interval such that `I ∩ S_≤ ⊆ {a_2/b_2}`,
then the weight vector associated to any fraction in the interior of `I` is dominated
by the weight vector associated to the left endpoint of `I`. -/
lemma dom_of_mem_interior_left (d : ℕ) [NeZero d] {a b : ℕ} {I : BasicInterval} (hm : mem_interior a b I)
    (hc : a.coprime b) (h : ∀ (a' b' : ℕ), mem_S_le d a' b' → mem a' b' I → a' * I.b₂ = b' * I.a₂) :
    of_fraction d I.a₁ I.b₁ ≤d of_fraction d a b := by
  obtain ⟨k₁, k₂, hk₁, hk₂, h₁, h₂⟩ := exists_of_mem_interior hm
  apply dom_of_pair_le
  intro i hi -- `hi : ⟨vᵢ, w₋⟩ ≥ 0`
  have hi' : 0 ≤ pair' (of_fraction d I.a₂ I.b₂) (v i) -- `⟨vᵢ, w₊⟩ ≥ 0`
  · simp only [v, Nat.cast_ofNat, pair'_of_fraction] at hi ⊢
    norm_num at hi ⊢
    set ai : ℤ := d - 3 * (i.val 1) + (d - 3 * (i.val 2)) with hai_def
    set bi : ℤ := d - 3 * (i.val 2) with hbi_def
    cases' le_or_lt 0 bi with hbi hbi
    · refine (zero_le_mul_right (Int.ofNat_pos.mpr I.b₁_pos)).mp ?_
      calc
        (0 : ℤ)
          ≤ (I.a₁ * bi + I.b₁ * ai) * I.b₂           := Int.mul_nonneg hi (Int.ofNat_nonneg I.b₂)
        _ = I.a₁ * I.b₂ * bi + I.b₁ * I.b₂ * ai      := by ring
        _ = I.a₂ * I.b₁ * bi + I.b₁ * I.b₂ * ai - bi := by norm_cast; rw [I.rel]; push_cast; ring
        _ = (I.a₂ * bi + I.b₂ * ai) * I.b₁ - bi      := by ring
        _ ≤ _                                        := Int.sub_le_self _ hbi
      done
    · have hai : 0 ≤ ai
      · by_contra hai
        have H₁ : I.a₁ * bi ≤ 0 := Int.mul_nonpos_of_nonneg_of_nonpos (Int.ofNat_nonneg I.a₁) hbi.le
        have H₂ : I.b₁ * ai < 0 :=
          Int.mul_neg_of_pos_of_neg (Int.ofNat_pos.mpr I.b₁_pos) (Int.not_le.mp hai)
        linarith        
        done
      have memS : mem_S_le d ai (-bi) :=
        ⟨Int.neg_pos_of_neg hbi, i.val 1, i.val 2, by linarith, by linarith, by ring⟩
      have Hai : ai.toNat = ai := Int.toNat_of_nonneg hai
      have Hbi : (-bi).toNat = -bi := Int.toNat_of_nonneg (Int.neg_nonneg_of_nonpos hbi.le)
      specialize h ai.toNat (-bi).toNat
      rw [Hai, Hbi] at h
      specialize h memS
      
      sorry
      done
  calc
    _ = 1 * pair' (of_fraction d I.a₁ I.b₁) (v i) + 0 * pair' (of_fraction d I.a₂ I.b₂) (v i) := by
        rw [one_mul, zero_mul, add_zero]
    _ ≤ k₁ * pair' (of_fraction d I.a₁ I.b₁) (v i) + k₂ * pair' (of_fraction d I.a₂ I.b₂) (v i) :=
        add_le_add (Int.mul_le_mul_of_nonneg_right (by exact_mod_cast hk₁) hi)
                   (Int.mul_le_mul_of_nonneg_right (by exact_mod_cast hk₂.le) hi')
    _ = _ := by 
        rw [h₁, h₂, pair'_of_fraction_add, Pi.add_apply, pair'_of_fraction_mul, pair'_of_fraction_mul]
  done

end Weight

#check Weight

example (a b : ℤ) (ha : 0 ≤ a) (hb : b ≤ 0) : a * b ≤ 0 := by exact Int.mul_nonpos_of_nonneg_of_nonpos ha hb
example (n : ℕ) (h : 0 < n) : (0 : ℤ) < n := by exact Iff.mpr Int.ofNat_pos h
example (n : ℕ) : 0 ≤ (n : ℤ) := by exact Int.ofNat_nonneg n
example (a : ℤ) (h : ¬ 0 ≤ a) : a < 0 := by exact Iff.mp Int.not_le h
example (a b : ℤ) (h : 0 ≤ b) : a - b ≤ a := by exact Int.sub_le_self a h
example (a : ℤ) (h : a < 0) : 0 ≤ -a := by exact Int.neg_nonneg_of_nonpos h.le