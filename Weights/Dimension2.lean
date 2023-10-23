import Weights.Uniqueness
import Weights.BasicInterval

namespace Weight

/-!
## Dimension 2

We attempt a formalization of Theorem 1.6 in the paper, which says that in the case `n = 2`,
the weights in a minimal complete set of weight vectors have entries bounded by `d`.
-/

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

/-- Every normalized weight vector for dimension 2 is of the form `of_fraction a b`. -/
lemma ex_of_fraction {d : ℕ} [NeZero d] {w : Weight 2 d} (h : w.normalized) :
    ∃ a b, w = of_fraction d a b := by
  refine ⟨w 2 - w 1, w 1, ?_⟩
  ext i
  fin_cases i
  · simp [of_fraction, h.1]
  · simp [of_fraction]
  · change w 2 = w 2 - w 1 + w 1
    have := h.2 (by norm_num : (1 : Fin 3) ≤ 2)
    exact Nat.eq_add_of_sub_eq this rfl
  done

/-- Every vector of the form `of_fraction d a b` is normalized. -/
lemma normalized_of_of_fraction (d : ℕ) [NeZero d] (a b : ℕ) : (of_fraction d a b).normalized := by
  refine ⟨?_, ?_⟩
  · simp [of_fraction]
  · have help : ∀ i j : Fin 3, i ≤ j → i = 0 ∨ (i = 1 ∧ (j = 1 ∨ j = 2)) ∨ (i = 2 ∧ j = 2) := by decide
    intro i j hij
    rcases help i j hij with rfl | ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl⟩
    · simp [of_fraction]
    · exact le_rfl
    · simp [of_fraction]
    · exact le_rfl
  done

/-- The entries of `of_fraction d a b` are bounded by `a+b`. -/
lemma of_fraction_le (d : ℕ) [NeZero d] (a b : ℕ) (i : Fin 3) : of_fraction d a b i ≤ a + b :=
  (normalized_of_of_fraction d a b).2 <| Fin.le_val_last i

/-- A useful combination of tactics: apply map to `ℤ3ℤ` to rel and simplify. / -/
macro "reduce_mod_3" t:term : tactic => `(tactic|(
  apply_fun (fun z ↦ (z : ZMod 3)) at $t:term
  push_cast at $t:term
  have H₁ : (3 : ZMod 3) = 0 := rfl
  have H₂ : (2 : ZMod 3) = -1 := rfl
  simp [H₁, H₂] at $t:term
  try assumption))

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

lemma mem_S_le_of_proportional {d g : ℕ} {a b : ℤ} (hg : 0 < g) (h : mem_S_le d (a * g) (b * g)) :
    mem_S_le d a b := by
  obtain ⟨h₁, i₁, i₂, h₂, h₃, h₄⟩ := h
  simp_rw [mul_comm _ (g : ℤ), mul_assoc] at h₄
  replace hg : (0 : ℤ) < g := Nat.cast_pos.mpr hg
  exact ⟨(zero_lt_mul_right hg).mp h₁, i₁, i₂, h₂, h₃, Int.eq_of_mul_eq_mul_left hg.ne' h₄⟩

lemma mem_S_ge_of_proportional {d g : ℕ} {a b : ℤ} (hg : 0 < g) (h : mem_S_ge d (a * g) (b * g)) :
    mem_S_ge d a b := by
  obtain ⟨h₁, i₁, i₂, h', h₂, h₃, h₄⟩ := h
  simp_rw [mul_comm _ (g : ℤ), mul_assoc] at h₄
  replace hg : (0 : ℤ) < g := Nat.cast_pos.mpr hg
  exact ⟨(zero_lt_mul_right hg).mp h₁, i₁, i₂, h', h₂, h₃, Int.eq_of_mul_eq_mul_left hg.ne' h₄⟩


lemma not_eq_neg_self {d : ℕ} (hd : (d : ZMod 3) ≠ 0) : (-d : ZMod 3) ≠ d := by
  have hch : ringChar (ZMod 3) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; norm_num
  exact mt (Ring.eq_self_iff_eq_zero_of_char_ne_two hch).mp hd

lemma eq_mod_3_of_rel {d a b i₁ i₂ : ℕ} (hd : (d : ZMod 3) ≠ 0)
    (rel : (a : ℤ) * (3 * i₂ - d) = b * (2 * d - 3 * i₁ - 3 * i₂)) :
    (a : ZMod 3) = b := by
  reduce_mod_3 rel
  exact rel.resolve_right hd

lemma eq_or_eq_neg_in_zmod_3 {d a b : ℕ} (hd : (d : ZMod 3) ≠ 0) (hcop : Nat.Coprime a b)
    (hab : (a : ZMod 3) = b) :
    (a : ZMod 3) = d ∨ (a : ZMod 3) = -d := by
  have hdd := not_eq_neg_self hd
  by_contra' H
  have help : ∀ {a d : ZMod 3}, -d ≠ d → (a ≠ d ∧ a ≠ -d) → a = 0 := by decide
  have ha₀ := (ZMod.nat_cast_zmod_eq_zero_iff_dvd a 3).mp <| help hdd H
  have hb₀ := (ZMod.nat_cast_zmod_eq_zero_iff_dvd b 3).mp <| (help hdd H ▸ hab).symm
  exact Nat.Prime.not_coprime_iff_dvd.mpr ⟨3, Nat.prime_three, ha₀, hb₀⟩ hcop 


/-- If `d = 3*δ` is divisble by `3` and `a/b ∈ S_≤` in lowest terms, then `a + b ≤ δ`. -/
lemma add_le_delta_of_mem_S_le {δ a b : ℕ} (hcop : Nat.Coprime a b) (hSle : mem_S_le (3 * δ) a b) :
    a + b ≤ δ := by
  obtain ⟨_, i₁, i₂, hi₁, hi₂, hSle⟩ := hSle
  rw [← mul_add, ← mul_assoc, mul_comm 2, mul_assoc] at hi₁
  replace hi₁ := (mul_le_mul_left (by norm_num)).mp hi₁ -- `i₁ + i₂ ≤ 2 * δ`
  replace hi₂ := (mul_lt_mul_left (by norm_num)).mp hi₂ -- `δ < i₂`
  obtain ⟨x₁, Hx₁⟩ : ∃ x : ℕ, (x : ℤ) = 2 * δ - i₁ - i₂ :=
    ⟨2 * δ - i₁ -i₂, by rw [Nat.sub_sub, Int.sub_sub]; norm_cast⟩
  obtain ⟨x₂, Hx₂, Hx₂'⟩ : ∃ x : ℕ, (x : ℤ) = i₂ - δ ∧ 0 < x :=
    ⟨i₂ - δ, by have := hi₂.le; norm_cast, Nat.sub_pos_of_lt hi₂⟩
  have hx : x₁ + x₂ ≤ δ := by linarith
  push_cast at hSle
  rw [(by rw [Hx₂]; ring : (a : ℤ) * (3 * i₂ - 3 * δ) = 3 * (a * x₂)),
      (by rw [Hx₁]; ring : (b : ℤ) * (2 * (3 * δ) - 3 * i₁ - 3 * i₂) = 3 * (b * x₁))] at hSle
  replace hSle := mul_left_cancel₀ (by norm_num) hSle
  norm_cast at hSle -- `a * x₂ = b * x₁`
  have ha : a ≤ x₁
  · cases' eq_or_ne x₁ 0 with H H
    · simp only [H, mul_zero, mul_eq_zero] at hSle
      -- `hSle : a = 0 ∨ x₂ = 0`
      rcases hSle with rfl | rfl
      · exact Nat.zero_le _
      · exact False.elim <| Nat.lt_irrefl _ Hx₂'
    exact Nat.le_of_dvd (Nat.pos_of_ne_zero H) <| hcop.dvd_of_dvd_mul_left <| Dvd.intro (Int.toNat x₂) hSle
  have hb : b ≤ x₂ :=
    Nat.le_of_dvd Hx₂' <| hcop.symm.dvd_of_dvd_mul_left <| Dvd.intro (Int.toNat x₁) hSle.symm
  linarith
  done

/-- If `d` is not divisible by `3` and `a/b ∈ S_≤` in lowest terms,
then either `a ≡ b ≡ -d mod 3` and `a + b ≤ d` or `a ≡ b ≡ d mod 3` and `a + b ≤ d/2`. -/
lemma add_le_of_mem_S_le {d a b : ℕ} (hd : (d : ZMod 3) ≠ 0) (hcop : Nat.Coprime a b) (hSle : mem_S_le d a b) :
    (a : ZMod 3) = b ∧ ((a : ZMod 3) = -d ∧ a + b ≤ d ∨ (a : ZMod 3) = d ∧ a + b ≤ d / 2) := by
  obtain ⟨_, i₁, i₂, hi₁, hi₂, hSle⟩ := hSle
  have hab := eq_mod_3_of_rel hd hSle -- `a = b` in `ℤ/3ℤ`
  refine ⟨hab, ?_⟩
  obtain ⟨x₁, Hx₁⟩ : ∃ x : ℕ, (x : ℤ) = 2 * d - 3 * i₁ - 3 * i₂ :=
    ⟨2 * d - 3 * i₁ - 3 * i₂, by rw [Nat.sub_sub, Int.sub_sub]; norm_cast⟩
  obtain ⟨x₂, Hx₂, Hx₂'⟩ : ∃ x : ℕ, (x : ℤ) = 3 * i₂ - d ∧ 0 < x :=
    ⟨3 * i₂ - d, by have := hi₂.le; norm_cast, Nat.sub_pos_of_lt hi₂⟩
  have hx : x₁ + x₂ ≤ d := by linarith
  rw [(by rw [Hx₂] : (a : ℤ) * (3 * i₂ - d) = a * x₂),
      (by rw [Hx₁] : (b : ℤ) * (2 * d - 3 * i₁ - 3 * i₂) = b * x₁)] at hSle
  norm_cast at hSle -- `a * x₂ = b * x₁`
  obtain ⟨m, hm₁, hm₂⟩ := proportional hSle hcop
  rw [hm₁, hm₂, ← mul_add] at hx
  have hm₀ : 0 < m :=
    (Nat.eq_zero_or_pos m).resolve_left (by rintro rfl; linarith only [Hx₂', hm₂])
  rcases eq_or_eq_neg_in_zmod_3 hd hcop hab with had | had -- `a = d ∨ a = -d` in `ℤ/3ℤ`
  · refine Or.inr ⟨had, ?_⟩
    have hm : 2 ≤ m
    · by_contra' H
      obtain rfl : m = 1 := by linarith
      have hx₁' : (x₁ : ZMod 3) = -d := by reduce_mod_3 Hx₁
      rw [hm₁, one_mul, had, eq_comm] at hx₁'
      exact not_eq_neg_self hd hx₁'
    have : (a + b : ℤ) * 2 ≤ d := by
      exact_mod_cast mul_comm 2 _ ▸ (Nat.mul_le_mul_right (a + b) hm).trans hx
    exact Nat.le_div_two_iff_mul_two_le.mpr this
  · exact Or.inl ⟨had, (Nat.le_mul_of_pos_left hm₀).trans hx⟩

/-- If `d = 3*δ` is divisble by `3` and `a/b ∈ S_≥` in lowest terms, then `a ≤ δ` and `b ≤ δ`. -/
lemma le_delta_of_mem_S_ge {δ a b : ℕ} (hcop : Nat.Coprime a b) (hSge : mem_S_ge (3 * δ) a b) :
    a ≤ δ ∧ b ≤ δ := by
  obtain ⟨_, i₁, i₂, hi₀, hi₁, hi₂, hSge⟩ := hSge
  rw [← mul_add, ← mul_assoc, mul_comm 2, mul_assoc] at hi₁
  replace hi₁ := (mul_lt_mul_left (by norm_num)).mp hi₁
  replace hi₂ := (mul_le_mul_left (by norm_num)).mp hi₂
  obtain ⟨x₁, Hx₁, Hx₁'⟩ : ∃ x : ℕ, (x : ℤ) = i₁ + i₂ - 2 * δ ∧ 0 < x:=
    ⟨i₁ + i₂ - 2 * δ, by have := hi₁.le; norm_cast, Nat.sub_pos_of_lt hi₁⟩
  obtain ⟨x₂, Hx₂⟩ : ∃ x : ℕ, (x : ℤ) = δ - i₂ := ⟨δ - i₂, by norm_cast⟩
  have hx₁ : x₁ ≤ δ := by linarith
  have hx₂ : x₂ ≤ δ := by linarith
  push_cast at hSge
  rw [(by rw [Hx₂]; ring : (a : ℤ) * (3 * i₂ - 3 * δ) = (-3) * (a * x₂)),
      (by rw [Hx₁]; ring : (b : ℤ) * (2 * (3 * δ) - 3 * i₁ - 3 * i₂) = (-3) * (b * x₁))] at hSge
  replace hSge := mul_left_cancel₀ (by norm_num) hSge
  norm_cast at hSge
  have ha : a ≤ x₁ := Nat.le_of_dvd Hx₁' <| hcop.dvd_of_dvd_mul_left <| Dvd.intro x₂ hSge
  have hb : b ≤ x₂
  · cases' eq_or_ne x₂ 0 with H H
    · simp only [H, mul_zero, zero_eq_mul] at hSge 
      -- `hSge : b = 0 ∨ x₁ = 0`
      rcases hSge with rfl | rfl
      · exact Nat.zero_le _
      · exact False.elim <| Nat.lt_irrefl _ Hx₁'
    exact Nat.le_of_dvd (Nat.pos_of_ne_zero H) <| hcop.symm.dvd_of_dvd_mul_left <| Dvd.intro x₁ hSge.symm
  exact ⟨ha.trans hx₁, hb.trans hx₂⟩

/-- If `d` is not divisible by `3` and `a/b ∈ S_≥` in lowest terms,
then either `a ≡ b ≡ d mod 3` and `a, b ≤ d` or `a ≡ b ≡ -d mod 3` and `a, b ≤ d/2`. -/
lemma le_of_mem_S_ge {d a b : ℕ} (hd : (d : ZMod 3) ≠ 0) (hcop : Nat.Coprime a b) (hSge : mem_S_ge d a b) :
    (a : ZMod 3) = b ∧ ((a : ZMod 3) = d ∧ a ≤ d ∧ b ≤ d ∨ (a : ZMod 3) = -d ∧ a ≤ d / 2 ∧ b ≤ d / 2) := by
  obtain ⟨_, i₁, i₂, hi₀, hi₁, hi₂, hSge⟩ := hSge
  have hab := eq_mod_3_of_rel hd hSge -- `a = b` in `ℤ/3ℤ`
  refine ⟨hab, ?_⟩
  obtain ⟨x₁, Hx₁, Hx₁'⟩ : ∃ x : ℕ, (x : ℤ) = 3 * i₁ + 3 * i₂ - 2 * d ∧ 0 < x :=
    ⟨3 * i₁ + 3 * i₂ - 2 * d, by have := hi₁.le; norm_cast, Nat.sub_pos_of_lt hi₁⟩
  obtain ⟨x₂, Hx₂⟩ : ∃ x : ℕ, (x : ℤ) = d - 3 * i₂ := ⟨d - 3 * i₂, by norm_cast⟩
  have hx₁ : x₁ ≤ d := by linarith
  have hx₂ : x₂ ≤ d := by linarith
  apply_fun (- ·) at hSge
  rw [(by rw [Hx₂]; ring : -((a : ℤ) * (3 * i₂ - d)) = a * x₂),
      (by rw [Hx₁]; ring : -((b : ℤ) * (2 * d - 3 * i₁ - 3 * i₂)) = b * x₁)] at hSge
  norm_cast at hSge -- `a * x₂ = b * x₁`
  obtain ⟨m, hm₁, hm₂⟩ := proportional hSge hcop
  rw [hm₁] at hx₁
  rw [hm₂] at hx₂
  have hm₀ : 0 < m :=
    (Nat.eq_zero_or_pos m).resolve_left (by rintro rfl; linarith only [Hx₁', hm₁])
  rcases eq_or_eq_neg_in_zmod_3 hd hcop hab with had | had -- `a = d ∨ a = -d` in `ℤ/3ℤ`
  · exact Or.inl ⟨had, (Nat.le_mul_of_pos_left hm₀).trans hx₁, (Nat.le_mul_of_pos_left hm₀).trans hx₂⟩
  · have hm : 2 ≤ m
    · by_contra' H
      obtain rfl : m = 1 := by linarith
      have hx₁' : (x₁ : ZMod 3) = d := by reduce_mod_3 Hx₁
      rw [hm₁, one_mul, had] at hx₁'
      exact not_eq_neg_self hd hx₁'
    have Ha : (a : ℤ) * 2 ≤ d := by exact_mod_cast mul_comm 2 a ▸ (Nat.mul_le_mul_right a hm).trans hx₁
    have Hb : (b : ℤ) * 2 ≤ d := by exact_mod_cast mul_comm 2 b ▸ (Nat.mul_le_mul_right b hm).trans hx₂
    exact Or.inr ⟨had, Nat.le_div_two_iff_mul_two_le.mpr Ha, Nat.le_div_two_iff_mul_two_le.mpr Hb⟩


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
      · constructor <;> { zify; rw [Hai, Hbi]; linarith }
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
      · constructor <;> { zify; rw [Hai, Hbi]; linarith }
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

lemma dom_of_proportional (d : ℕ) [NeZero d] {a b a' b' : ℕ} (hab : a ≠ 0 ∨ b ≠ 0) (hc : a'.Coprime b')
    (h : a' * b = b' * a) :
    of_fraction d a' b' ≤d of_fraction d a b := by
  obtain ⟨m, ha, hb⟩ := proportional h hc
  have hmz : m ≠ 0 :=
    hab.elim (fun haz ↦ left_ne_zero_of_mul <| ha ▸ haz) (fun hbz ↦ left_ne_zero_of_mul <| hb ▸ hbz)
  have hm : (1 : ℤ) ≤ m := Int.toNat_le.mp <| Nat.one_le_iff_ne_zero.mpr hmz
  apply dom_of_pair_le
  intro i hi
  simp_rw [pair'_of_fraction] at hi ⊢
  rw [ha, hb, Nat.cast_mul, Nat.cast_mul, mul_assoc, mul_assoc, ← mul_add]
  nlinarith only [hi, hm]
  done

/-- Lemma 4.1. If `I = [a₁/b₁, a₂/b₂]` is a basic interval such that
`I ∩ S_≤ ⊆ {a₂/b₂}` or `I ∩ S_≥ ⊆ {a₁/b₁}`, then the weight vector associated to any fraction
in `I` is dominated by the weight vector associated to one endpoint of `I`.-/
lemma dom_of_mem (d : ℕ) [NeZero d] {a b : ℕ} {I : BasicInterval} (hab : a ≠ 0 ∨ b ≠ 0) (hm : mem a b I)
    (h : (∀ (a' b' : ℕ), mem_S_le d a' b' → mem a' b' I → a' * I.b₂ = b' * I.a₂) ∨
         ∀ (a' b' : ℕ), mem_S_ge d a' b' → mem a' b' I → a' * I.b₁ = b' * I.a₁) :
    of_fraction d I.a₁ I.b₁ ≤d of_fraction d a b ∨ of_fraction d I.a₂ I.b₂ ≤d of_fraction d a b := by
  have help {a b c d : ℕ} (hyp : a * b = c * d) : d * c = b * a
  · rw [mul_comm b, mul_comm d, hyp]
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
  have H₁ : mem_S_le d a' b'
  · push_cast at h₁
    exact mem_S_le_of_proportional hg₁ h₁
  have H₂ : mem a' b' I := mem_of_proportional hg₁ h₂
  simp_rw [mul_comm _ g, mul_assoc]
  exact congrArg (g * ·) (H a' b' hcop H₁ H₂)

lemma condition_iff_weaker_ge (d : ℕ) [NeZero d] (I : BasicInterval) :
    (∀ (a b : ℕ), Nat.Coprime a b → mem_S_ge d a b → mem a b I → a * I.b₁ = b * I.a₁) ↔
      ∀ (a b : ℕ), mem_S_ge d a b → mem a b I → a * I.b₁ = b * I.a₁ := by
  refine ⟨fun H a b h₁ h₂ ↦ ?_, fun H a b _ ↦ H a b⟩
  cases' Nat.eq_zero_or_pos (Nat.gcd a b) with h₀ h₀
  · obtain ⟨rfl, rfl⟩ := Nat.gcd_eq_zero_iff.mp h₀
    simp only [zero_mul]
    done
  obtain ⟨g, a', b', hg₁, hcop, rfl, rfl⟩ := Nat.exists_coprime' h₀; clear h₀
  have H₁ : mem_S_ge d a' b'
  · push_cast at h₁
    exact mem_S_ge_of_proportional hg₁ h₁
  have H₂ : mem a' b' I := mem_of_proportional hg₁ h₂
  simp_rw [mul_comm _ g, mul_assoc]
  exact congrArg (g * ·) (H a' b' hcop H₁ H₂)

lemma eq_left_of_add_le {d a b : ℕ} [NeZero d] {I : BasicInterval} (hI : I.feasible d)
    (hcop : Nat.Coprime a b) (hmem : mem a b I) (hbd : a + b ≤ d) (hne : a * I.b₂ ≠ b * I.a₂) :
    a = I.a₁ ∧ b = I.b₁ := by
  refine eq_and_eq_of_coprime_coprime_mul_eq_mul hcop I.coprime₁ ?_
  rcases eq_or_eq_or_mem_interior_of_mem hmem with left | right | interior
  · exact left
  · contradiction
  · linarith [gt_of_mem_interior_feasible hI interior]
  done

lemma eq_right_of_add_le {d a b : ℕ} [NeZero d] {I : BasicInterval} (hI : I.feasible d)
    (hcop : Nat.Coprime a b) (hmem : mem a b I) (hbd : a + b ≤ d) (hne : a * I.b₁ ≠ b * I.a₁) :
    a = I.a₂ ∧ b = I.b₂ := by
  refine eq_and_eq_of_coprime_coprime_mul_eq_mul hcop I.coprime₂ ?_
  rcases eq_or_eq_or_mem_interior_of_mem hmem with left | right | interior
  · contradiction
  · exact right
  · linarith [gt_of_mem_interior_feasible hI interior]
  done

/-- A feasible basic interval `I = [a₁/b₁, a₂/b₂]` satisfies the condition
`I ∩ S_≤ ⊆ {a₂/b₂}` or `I ∩ S_≥ ⊆ {a₁/b₁}`. -/
lemma condition_of_feasible {d : ℕ} [NeZero d] {I : BasicInterval} (hI : I.feasible d) :
    (∀ (a' b' : ℕ), mem_S_le d a' b' → mem a' b' I → a' * I.b₂ = b' * I.a₂) ∨
    ∀ (a' b' : ℕ), mem_S_ge d a' b' → mem a' b' I → a' * I.b₁ = b' * I.a₁ := by
  rw [← condition_iff_weaker_le, ← condition_iff_weaker_ge]
  by_contra' H
  obtain ⟨⟨s₁, t₁, hcop₁, hSle, hmem₁, hne₁⟩, ⟨s₂, t₂, hcop₂, hSge, hmem₂, hne₂⟩⟩ := H
  cases' eq_or_ne (d : ZMod 3) 0 with hd hd
  · -- case `d` is divisble by 3
    obtain ⟨δ, rfl⟩ := (ZMod.nat_cast_zmod_eq_zero_iff_dvd d 3).mp hd
    -- `s₁/t₁` must be left endpoint
    have hs₁t₁ := add_le_delta_of_mem_S_le hcop₁ hSle
    obtain ⟨hs₁a₁, ht₁b₁⟩ := eq_left_of_add_le hI hcop₁ hmem₁ (by linarith) hne₁
    -- `s₂/t₂` must be right endpoint
    obtain ⟨hs₁, ht₂⟩ := le_delta_of_mem_S_ge hcop₂ hSge
    obtain ⟨hs₂a₂, ht₂b₂⟩ := eq_right_of_add_le hI hcop₂ hmem₂ (by linarith) hne₂
    -- now obtain contradiction
    refine False.elim <| Nat.lt_irrefl (3 * δ) ?_
    calc
      3 * δ < I.a₁ + I.a₂ + I.b₁ + I.b₂     := hI.2.2
      _     = (I.a₁ + I.b₁) + (I.a₂ + I.b₂) := by abel
      _     = (s₁ + t₁) + (s₂ + t₂)         := by symm; congr
      _     ≤  δ + (δ + δ)                  := by gcongr
      _     = _                             := by ring
    done
  -- Now deal with the case that `d` is not divisible by 3
  obtain ⟨hs₁t₁mod3, hyp₁⟩ := add_le_of_mem_S_le hd hcop₁ hSle
  -- `s₁/t₁` must be left endpoint
  have h' : s₁+ t₁ ≤ d
  · rcases hyp₁ with ⟨_, hyp⟩ | ⟨_, hyp⟩
    · exact hyp
    · exact hyp.trans <| Nat.div_le_self d 2 
  obtain ⟨hs₁a₁, ht₁b₁⟩ := eq_left_of_add_le hI hcop₁ hmem₁ (by linarith) hne₁
  -- get bounds for `s₂` and `t₂`
  obtain ⟨hs₂t₂mod3, hyp₂⟩ := le_of_mem_S_ge hd hcop₂ hSge
  -- write `(s₂, t₂) = k₁•(I.a₁, I,b₁) + k₂•(I.a₂, I,b₂)`
  obtain ⟨k₁, k₂, hks₂, hkt₂⟩ := exists_of_mem hmem₂
  -- A bound for `s₂ + t₂`
  have hbd : s₂ + t₂ ≤ 2 * d
  · rcases hyp₂ with ⟨_, H₁, H₂⟩ | ⟨_, H₁, H₂⟩
    · linarith only [H₁, H₂]
    · replace H₁ := H₁.trans <| Nat.div_le_self d 2
      replace H₂ := H₂.trans <| Nat.div_le_self d 2
      linarith only [H₁, H₂]
    done
  have hk₂' : 3 ∣ k₂
  · rw [← ZMod.nat_cast_zmod_eq_zero_iff_dvd]
    have : k₂ + t₂ * s₁ = s₂ * t₁
    · rw [hks₂, hkt₂, hs₁a₁, ht₁b₁, add_mul _ _ I.b₁, mul_assoc _ I.a₂, I.rel]
      ring
      done 
    apply_fun (fun z ↦ (z : ZMod 3)) at this
    push_cast at this
    simpa only [hs₁t₁mod3, hs₂t₂mod3, add_left_eq_self] using this
    done
  have hk₂ : 3 ≤ k₂
  · refine Nat.le_of_dvd ((Nat.eq_zero_or_pos _).resolve_left ?_) hk₂'
    rintro rfl
    rw [hks₂, hkt₂, zero_mul, add_zero, zero_mul, add_zero, Nat.mul_right_comm] at hne₂
    exact hne₂ rfl
  have hk₁ : 1 ≤ k₁
  · refine (Nat.eq_zero_or_pos k₁).resolve_left ?_
    rintro rfl
    simp only [zero_mul, zero_add] at hks₂ hkt₂
    rw [hks₂, hkt₂] at hcop₂
    linarith only [eq_one_of_coprime_mul_mul hcop₂, hk₂]
    done
  have : k₁ = 1 ∨ 2 ≤ k₁ := by rwa [eq_comm, Nat.succ_le, ← le_iff_eq_or_lt]
  have hbd' : 2 * d < s₂ + t₂
  · rcases this with rfl | hk₁
    · have hs₂bd : 1 * I.a₁ + 3 * I.a₂ ≤ s₂ := by rw [hks₂]; gcongr
      have ht₂bd : 1 * I.b₁ + 3 * I.b₂ ≤ t₂ := by rw [hkt₂]; gcongr
      have hI₂ := hI.2.2
      have H₁ : d < s₂ + t₂ := by linarith
      have Hd : d / 2 + d / 2 ≤ d := by rw [← two_mul]; exact Nat.mul_div_le d 2
      have H₂ : (s₂ : ZMod 3) = d :=
        (hyp₂.resolve_right (fun _ ↦ False.elim <| lt_irrefl d <| H₁.trans_le (by linarith))).1
      have H₃ : (s₁ : ZMod 3) = d
      · have : (k₂ : ZMod 3) = 0 := (ZMod.nat_cast_zmod_eq_zero_iff_dvd k₂ 3).mpr hk₂'
        apply_fun (fun z ↦ (z : ZMod 3)) at hks₂
        push_cast at hks₂
        simpa only [H₂, ← hs₁a₁, one_mul, this, zero_mul, add_zero] using hks₂.symm
      have H₄ : I.a₁ + I.b₁ ≤ d / 2
      · rw [← hs₁a₁, ← ht₁b₁]
        rcases hyp₁ with ⟨hmod, hle⟩ | ⟨_, hle⟩
        · have HH : (d : ZMod 3) = 0
          · rw [H₃] at hmod
            have hch : ringChar (ZMod 3) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; norm_num
            exact (Ring.eq_self_iff_eq_zero_of_char_ne_two hch).mp hmod.symm
          contradiction
          done
        · exact hle
      have : d < 2 * (I.a₂ + I.b₂)
      · refine lt_two_mul_of_div_two_lt ?_
        calc
          d / 2 ≤ d - d / 2         := Nat.le_sub_of_add_le Hd
          _     ≤ d - (I.a₁ + I.b₁) := Nat.sub_le_sub_left _ H₄
          _     < I.a₂ + I.b₂       := Nat.sub_lt_left_of_lt_add (H₄.trans <| Nat.div_le_self d 2)
                                                                 (by convert hI.2.2 using 1; ring)
        done
      calc
        2 * d = d + d := by ring
        _     < (I.a₁ + I.a₂ + I.b₁ + I.b₂) + 2 * (I.a₂ + I.b₂) := by gcongr
        _     = 1 * (I.a₁ + I.b₁) + 3 *(I.a₂ + I.b₂)            := by ring
        _     ≤ 1 * (I.a₁ + I.b₁) + k₂ * (I.a₂ + I.b₂)          := by gcongr
        _     = s₂ + t₂                                         := by rw [hks₂, hkt₂]; ring
      done
    · calc
        2 * d < 2 * (I.a₁ + I.a₂ + I.b₁ + I.b₂)         := by gcongr; exact hI.2.2
        _     = 2 * (I.a₁ + I.b₁) + 2 * (I.a₂ + I.b₂)   := by ring
        _     ≤ k₁ * (I.a₁ + I.b₁) + k₂ * (I.a₂ + I.b₂) := by gcongr; linarith only [hk₂]
        _     = s₂ + t₂                                 := by rw [hks₂, hkt₂]; ring
      done
  exact lt_irrefl _ <| hbd'.trans_le hbd
  done

/-- Every weight vector `[0, b, a+b]` is dominated by a weight vector `[0, t, s+t]`
 with `s + t ≤ d`. -/
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

/-- The minimal complete set of normalized weight vectors for dimension 2 and degree `d`
consists of vectors with entries bounded by `d`. -/
theorem theorem_1_6 (d : ℕ) [NeZero d] : ∀ w ∈ M 2 d, ∀ i, w i ≤ d := by
  intro w hw
  obtain ⟨a, b, hab⟩ := ex_of_fraction hw.1
  obtain ⟨s, t, hle, hdom⟩ := dom_by_max_le_d d a b
  contrapose! hw
  obtain ⟨i, hi⟩ := hw
  refine not_in_M_of_dom_ne ⟨of_fraction d s t, normalized_of_of_fraction d s t, hab ▸ hdom,
                             fun H ↦ ?_⟩
  subst H
  exact lt_irrefl d <| hi.trans_le <| (of_fraction_le d s t i).trans hle

end Weight
