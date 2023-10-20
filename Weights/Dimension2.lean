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
  done 

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
  done  

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
def mem_S_le (d : ℕ) (a b : ℤ) : Prop :=
  0 < b ∧
  ∃ (i₁ i₂ : ℕ), 3 * i₁ + 3 * i₂ ≤ 2 * d ∧ d < 3 * i₂ ∧
                 a * (3 * i₂ - d) = b * (2 * d - 3 * i₁ - 3 * i₂)

/-- The fraction `a/b` is an element of `S_≥`. -/
def mem_S_ge (d : ℕ) (a b : ℤ) : Prop :=
  0 < a ∧
  ∃ (i₁ i₂ : ℕ), i₁ + i₂ ≤ d ∧ 2 * d < 3 * i₁ + 3 * i₂ ∧ 3 * i₂ ≤ d ∧
                 a * (3 * i₂ - d) = b * (2 * d - 3 * i₁ - 3 * i₂)

lemma mem_S_le_of_proportional {d : ℕ} {a b g : ℤ} (hg : 0 < g) (h : mem_S_le d (a * g) (b * g)) :
    mem_S_le d a b := by
  obtain ⟨h₁, i₁, i₂, h₂, h₃, h₄⟩ := h
  simp_rw [mul_comm _ g, mul_assoc] at h₄
  exact ⟨(zero_lt_mul_right hg).mp h₁, i₁, i₂, h₂, h₃, Int.eq_of_mul_eq_mul_left hg.ne' h₄⟩

lemma mem_S_ge_of_proportional {d : ℕ} {a b g : ℤ} (hg : 0 < g) (h : mem_S_ge d (a * g) (b * g)) :
    mem_S_ge d a b := by
  obtain ⟨h₁, i₁, i₂, h', h₂, h₃, h₄⟩ := h
  simp_rw [mul_comm _ g, mul_assoc] at h₄
  exact ⟨(zero_lt_mul_right hg).mp h₁, i₁, i₂, h', h₂, h₃, Int.eq_of_mul_eq_mul_left hg.ne' h₄⟩

open BasicInterval

/-- If `I = [a₁/b₁, a₂/b₂]` is a basic interval such that `I ∩ S_≤ ⊆ {a₂/b₂}`,
then the weight vector associated to any fraction in the interior of `I` is dominated
by the weight vector associated to the left endpoint of `I`. -/
lemma dom_of_mem_interior_left (d : ℕ) [NeZero d] {a b : ℕ} {I : BasicInterval} (hm : mem_interior a b I)
    (h : ∀ (a' b' : ℕ), mem_S_le d a' b' → mem a' b' I → a' * I.b₂ = b' * I.a₂) :
    of_fraction d I.a₁ I.b₁ ≤d of_fraction d a b := by
  obtain ⟨k₁, k₂, hk₁, hk₂, h₁, h₂⟩ := exists_of_mem_interior hm
  apply dom_of_pair_le
  intro i hi -- `hi : ⟨vᵢ, w₋⟩ ≥ 0`
  have hi' : 0 ≤ pair' (of_fraction d I.a₂ I.b₂) (v i) -- `⟨vᵢ, w₊⟩ ≥ 0`
  · simp only [v, Nat.cast_ofNat, pair'_of_fraction] at hi ⊢
    norm_num at hi ⊢
    set bi : ℤ := d - 3 * (i.val 2) with hbi_def
    set ai : ℤ := d - 3 * (i.val 1) + (d - 3 * (i.val 2)) with hai_def
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
      by_contra H
      have hmem : mem ai.toNat (-bi).toNat I
      · refine ⟨?_, ?_⟩ <;> { zify; rw [Hai, Hbi]; linarith }
        done
      specialize h ai.toNat (-bi).toNat
      rw [Hai, Hbi] at h
      specialize h memS hmem
      zify at h; rw [Hai, Hbi] at h
      linarith
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

/-- If `I = [a₁/b₁, a₂/b₂]` is a basic interval such that `I ∩ S_≥ ⊆ {a₁/b₁}`,
then the weight vector associated to any fraction in the interior of `I` is dominated
by the weight vector associated to the right endpoint of `I`. -/
lemma dom_of_mem_interior_right (d : ℕ) [NeZero d] {a b : ℕ} {I : BasicInterval} (hm : mem_interior a b I)
    (h : ∀ (a' b' : ℕ), mem_S_ge d a' b' → mem a' b' I → a' * I.b₁ = b' * I.a₁) :
    of_fraction d I.a₂ I.b₂ ≤d of_fraction d a b := by
  obtain ⟨k₁, k₂, hk₁, hk₂, h₁, h₂⟩ := exists_of_mem_interior hm
  apply dom_of_pair_le
  intro i hi -- `hi : ⟨vᵢ, w₊⟩ ≥ 0`
  have hi' : 0 ≤ pair' (of_fraction d I.a₁ I.b₁) (v i) -- `⟨vᵢ, w₋⟩ ≥ 0`
  · simp only [v, Nat.cast_ofNat, pair'_of_fraction] at hi ⊢
    norm_num at hi ⊢
    set bi : ℤ := d - 3 * (i.val 2) with hbi_def
    set ai : ℤ := d - 3 * (i.val 1) + (d - 3 * (i.val 2)) with hai_def
    cases' le_or_lt 0 ai with hai hai
    · refine (zero_le_mul_right (Int.ofNat_pos.mpr I.a₂_pos)).mp ?_
      calc
        (0 : ℤ)
          ≤ (I.a₂ * bi + I.b₂ * ai) * I.a₁           := Int.mul_nonneg hi (Int.ofNat_nonneg I.a₁)
        _ = I.a₁ * I.a₂ * bi + I.a₁ * I.b₂ * ai      := by ring
        _ = I.a₁ * I.a₂ * bi + I.a₂ * I.b₁ * ai - ai := by norm_cast; rw [I.rel]; push_cast; ring
        _ = (I.a₁ * bi + I.b₁ * ai) * I.a₂ - ai      := by ring
        _ ≤ _                                        := Int.sub_le_self _ hai
      done
    · have hbi : 0 ≤ bi
      · by_contra hbi
        have H₁ : I.b₂ * ai ≤ 0 := Int.mul_nonpos_of_nonneg_of_nonpos (Int.ofNat_nonneg I.b₂) hai.le
        have H₂ : I.a₂ * bi < 0 :=
          Int.mul_neg_of_pos_of_neg (Int.ofNat_pos.mpr I.a₂_pos) (Int.not_le.mp hbi)
        linarith        
        done
      have memS : mem_S_ge d (-ai) bi
      · refine ⟨Int.neg_pos_of_neg hai, i.val 1, i.val 2, ?_, by linarith, by linarith, by ring⟩
        have : i.val.sum = d := i.prop
        have HH : i.val.sum = i.val 0 + (i.val 1 + i.val 2)
        · rw [Weight.sum, Fin.sum_univ_three, add_assoc]
        linarith
        done
      have Hbi : bi.toNat = bi := Int.toNat_of_nonneg hbi
      have Hai : (-ai).toNat = -ai := Int.toNat_of_nonneg (Int.neg_nonneg_of_nonpos hai.le)
      by_contra H
      have hmem : mem (-ai).toNat bi.toNat I
      · refine ⟨?_, ?_⟩ <;> { zify; rw [Hai, Hbi]; linarith }
        done
      specialize h (-ai).toNat bi.toNat
      rw [Hai, Hbi] at h
      specialize h memS hmem
      zify at h; rw [Hai, Hbi] at h
      linarith
      done
  calc
    _ = 0 * pair' (of_fraction d I.a₁ I.b₁) (v i) + 1 * pair' (of_fraction d I.a₂ I.b₂) (v i) := by
        rw [one_mul, zero_mul, zero_add]
    _ ≤ k₁ * pair' (of_fraction d I.a₁ I.b₁) (v i) + k₂ * pair' (of_fraction d I.a₂ I.b₂) (v i) :=
        add_le_add (Int.mul_le_mul_of_nonneg_right (by exact_mod_cast hk₁.le) hi')
                   (Int.mul_le_mul_of_nonneg_right (by exact_mod_cast hk₂) hi)
    _ = _ := by 
        rw [h₁, h₂, pair'_of_fraction_add, Pi.add_apply, pair'_of_fraction_mul, pair'_of_fraction_mul]
  done

/-- Helper lemma that might go into Mathlib -/
lemma proportional {a b c d : ℕ} (h : a * d = b * c) (h' : Nat.Coprime a b) :
    ∃ m, c = m * a ∧ d = m * b := by
  obtain ⟨c₁, rfl⟩ := (Nat.Coprime.dvd_mul_left h').mp <| Dvd.intro d h
  obtain ⟨d₁, rfl⟩ := (Nat.Coprime.dvd_mul_left h'.symm).mp <| Dvd.intro _ h.symm
  cases' eq_or_ne (a * b) 0 with H H
  · rcases Nat.mul_eq_zero.mp H with rfl | rfl
    · obtain rfl : b = 1 := h'
      exact ⟨d₁, by simp⟩
    · obtain rfl : a = 1 := h'.symm
      exact ⟨c₁, by simp⟩
  · rw [← mul_assoc, ← mul_assoc, mul_comm b] at h
    obtain rfl := mul_left_cancel₀ H h
    exact ⟨d₁, by simp [mul_comm d₁]⟩

lemma dom_of_proportional (d : ℕ) [NeZero d] {a b a' b' : ℕ} (hab : a ≠ 0 ∨ b ≠ 0) (hc : a'.Coprime b')
    (h : a' * b = b' * a) :
    of_fraction d a' b' ≤d of_fraction d a b := by
  obtain ⟨m, ha, hb⟩ := proportional h hc
  have hmz : m ≠ 0
  · rcases hab with haz | hbz
    · rw [ha] at haz
      exact left_ne_zero_of_mul haz
    · rw [hb] at hbz
      exact left_ne_zero_of_mul hbz
  have hm : (1 : ℤ) ≤ m := Int.toNat_le.mp <| Nat.one_le_iff_ne_zero.mpr hmz
  apply dom_of_pair_le
  intro i hi
  simp_rw [pair'_of_fraction] at hi ⊢
  rw [ha, hb, Nat.cast_mul, Nat.cast_mul, mul_assoc, mul_assoc, ← mul_add]
  generalize ↑a' * v i 2 + ↑b' * (v i 1 + v i 2) = x at hi ⊢ 
  nlinarith only [hi, hm]
  done

/-- Lemma 4.1. If `I = [a₁/b₁, a₂/b₂]` is a basic interval such that
`I ∩ S_≤ ⊆ {a₂/b₂}` or `I ∩ S_≥ ⊆ {a₁/b₁}`, then the weight vector associated to any fraction
in `I` is dominated by the weight vector associated to one endpoint of `I`.-/
lemma dom_of_mem (d : ℕ) [NeZero d] {a b : ℕ} {I : BasicInterval} (hab : a ≠ 0 ∨ b ≠ 0) (hm : mem a b I)
    (h : (∀ (a' b' : ℕ), mem_S_le d a' b' → mem a' b' I → a' * I.b₂ = b' * I.a₂) ∨
         ∀ (a' b' : ℕ), mem_S_ge d a' b' → mem a' b' I → a' * I.b₁ = b' * I.a₁) :
    of_fraction d I.a₁ I.b₁ ≤d of_fraction d a b ∨ of_fraction d I.a₂ I.b₂ ≤d of_fraction d a b := by
  have help : ∀ {a b c d : ℕ}, a * b = c * d → d * c = b * a
  · intro a b c d hyp
    rw [mul_comm b, mul_comm d, hyp]
    done
  rcases eq_or_eq_or_mem_interior_of_mem hm with H | H | H
  · exact Or.inl <| dom_of_proportional d hab I.coprime₁ <| help H 
  · exact Or.inr <| dom_of_proportional d hab I.coprime₂ <| help H
  · rcases h with h | h
    · exact Or.inl <| dom_of_mem_interior_left d H h
    · exact Or.inr <| dom_of_mem_interior_right d H h
  done

/-- It is sufficient to require the condition for coprime pairs. -/
lemma condition_iff_weaker_le (d : ℕ) [NeZero d] (I : BasicInterval) :
    (∀ (a b : ℕ), Nat.Coprime a b → mem_S_le d a b → mem a b I → a * I.b₂ = b * I.a₂) ↔
      ∀ (a b : ℕ), mem_S_le d a b → mem a b I → a * I.b₂ = b * I.a₂ := by
  refine ⟨fun H a b h₁ h₂ ↦ ?_, fun H a b _ ↦ H a b⟩
  cases' Nat.eq_zero_or_pos (Nat.gcd a b) with h₀ h₀
  · obtain ⟨rfl, rfl⟩ := Nat.gcd_eq_zero_iff.mp h₀
    simp only [zero_mul]
    done
  obtain ⟨g, a', b', hg₁, hcop, rfl, rfl⟩ := Nat.exists_coprime' h₀; clear h₀
  have H₁ : mem_S_le d a' b' := sorry
  have H₂ : mem a' b' I := sorry
  simp_rw [mul_comm _ g, mul_assoc]
  congr 1
  exact H a' b' hcop H₁ H₂

lemma condition_iff_weaker_ge (d : ℕ) [NeZero d] (I : BasicInterval) :
    (∀ (a b : ℕ), Nat.Coprime a b → mem_S_ge d a b → mem a b I → a * I.b₁ = b * I.a₁) ↔
      ∀ (a b : ℕ), mem_S_ge d a b → mem a b I → a * I.b₁ = b * I.a₁ := by
  refine ⟨?_, fun H a b _ ↦ H a b⟩  
  sorry
  done


/-- A feasible basic interval `I = [a₁/b₁, a₂/b₂]` satisfies the condition
`I ∩ S_≤ ⊆ {a₂/b₂}` or `I ∩ S_≥ ⊆ {a₁/b₁}`. -/
lemma condition_of_feasible {d : ℕ} [NeZero d] {I : BasicInterval} (hI : I.feasible d) :
    (∀ (a' b' : ℕ), mem_S_le d a' b' → mem a' b' I → a' * I.b₂ = b' * I.a₂) ∨
    ∀ (a' b' : ℕ), mem_S_ge d a' b' → mem a' b' I → a' * I.b₁ = b' * I.a₁ := by
  rw [← condition_iff_weaker_le, ← condition_iff_weaker_ge]
  by_cases hd : 3 ∣ d
  · -- case `d` is divisble by 3
    obtain ⟨δ, rfl⟩ := hd
    by_contra' H
    obtain ⟨⟨s₁, t₁, hcop₁, hSle, hmem₁, hne₁⟩, ⟨s₂, t₂, hcop₂, hSge, hmem₂, hne₂⟩⟩ := H
    unfold mem_S_le at hSle
    unfold mem at hmem₁
    unfold feasible at hI
    done
  sorry
  done

#check Nat.exists_coprime
#check Nat.exists_coprime'
/-- Every weight vector `[0, b, a+b]` is dominated by a weight vector `[0, t, s+t]` with `s + t ≤ d`. -/
theorem dom_by_max_le_d (d : ℕ) [NeZero d] (a b : ℕ) :
    ∃ s t : ℕ, s + t ≤ d ∧ of_fraction d s t ≤d of_fraction d a b := by
  cases' le_or_lt (a + b) d with h h
  · -- case `a + b ≤ d`: vector dominates itself
    exact ⟨a, b, h, Eq.le rfl⟩
  · -- case `a + b > d`. Get feasible interval that contains `a/b`.
    obtain ⟨I, hI, hIab⟩ := mem_feasible d a b
    have hab : a ≠ 0 ∨ b ≠ 0 := by by_contra' hab; linarith
    cases' dom_of_mem d hab hIab (condition_of_feasible hI) with H H
    · exact ⟨I.a₁, I.b₁, hI.1, H⟩
    · exact ⟨I.a₂, I.b₂, hI.2.1, H⟩

end Weight
