import Weights.Uniqueness

namespace Weight

open BigOperators

variable {n : ℕ}

/-!
## The case `d = 1`

We show that for `n ≥ 1`, the unique minimal weight with first entry `0` is `(0, 1, ..., 1)`.
-/

/-- When `d = 1`, the `testvecs` are just the standard basis vectors. -/
lemma testvecs1 (n : ℕ) : Function.Bijective (tw n 1) := by
  refine ⟨tw_inj n 1, ?_⟩
  intro a
  have h₂ : ∑ k, a.val k = 1 := a.2
  simp [tw, tw']
  have h : ∃ j, a.val j = 1 := by
    have h₁ : ∃ j, 0 < a.val j := by
      by_contra! hf
      simp only [(fun k ↦ Nat.eq_zero_of_le_zero (hf k)), Finset.sum_const_zero,
                   Nat.zero_ne_one] at h₂
    obtain ⟨j, hj⟩ := h₁
    use j
    suffices h₃ : a.val j ≤ 1 by
      linarith
    conv_rhs => rw [← h₂]
    exact Finset.single_le_sum (fun k _ ↦ Nat.zero_le (a.val k)) (Finset.mem_univ j)
  obtain ⟨j, hj⟩ := h
  use j
  have h' : ∀ k, k ≠ j → a.val k = 0 := by
    intro k hk
    let s : Finset (Fin n.succ) := (Finset.univ \ {j})
    have hs : insert j s = Finset.univ := by simp [Finset.insert_eq, s]
    have hjs : ¬j ∈ s := by simp [s]
    rw [← hs, Finset.sum_insert hjs, hj] at h₂
    simp only [add_eq_left, Finset.sum_eq_zero_iff, Finset.mem_sdiff, Finset.mem_univ,
      Finset.mem_singleton, true_and, s] at h₂
    exact h₂ k hk
  ext k
  simp [Function.update_apply]
  split_ifs with hjk
  · rw [hjk]
    exact hj.symm
  · exact (h' k hjk).symm

/-- Define `w1 = (0, 1, ..., 1)`. -/
def w1 (n : ℕ) [NeZero n] : Weight n 1 := fun j ↦ if j = 0 then 0 else 1

lemma w1_apply (n : ℕ) [NeZero n] (j : Fin n.succ) : w1 n j = if j = 0 then 0 else 1 := rfl

lemma w1_zero (n : ℕ) [NeZero n] : w1 n 0 = 0 := by simp only [w1, if_true]

lemma sum_w1 (n : ℕ) [NeZero n] : (w1 n).sum = n := by
  simp [w1, Weight.sum, Finset.sum_ite, Finset.filter_ne']
-- use `Finset.sum_boole`? would require rewriting with `ite_not` first

lemma E_w1 (n : ℕ) [NeZero n] : (w1 n).E = 1 := by
  rw [E, sum_w1]
  simp [Nat.div_eq_zero_iff]

lemma w1_balanced (n : ℕ) [NeZero n] : (w1 n).balanced := by
  simp only [balanced]
  intro j
  rw [E_w1, w1]
  split_ifs with h
  · exact Nat.zero_le _
  · exact le_rfl

lemma pair_w1 {n : ℕ} [NeZero n] [DecidableEq (testvecs n 1)] (a : testvecs n 1) :
    (w1 n).pair a = if a = (tw n 1 0) then 0 else 1 := by
  obtain ⟨k, ha⟩ := (testvecs1 n).2 a
  rw [ha.symm, pair_tw, Nat.sub_self, zero_mul, zero_add, w1_apply]
  by_cases hk : k = 0
  · simp only [hk]
  · simp only [hk, if_false]
    split_ifs with h'
    · have t := hk (tw_inj n 1 h')
      tauto
    · rfl

/-- `w1` is the minimal weight with first entry `0` w.r.t. dominance when `d = 1`. -/
lemma w1_minimal {n : ℕ} [NeZero n] {w : Weight n 1} (hw : w 0 = 0) : (w1 n) ≤d w := by
  simp only [dom_iff, f_le_iff, f_apply]
  intro a
  classical
  simp only [E_w1, tsub_le_iff_right, pair_w1]
  split_ifs with h
  · rw [← f, h, eval_f_tw, hw]
    simp only [mul_zero, tsub_zero, add_zero]
    exact one_le_E w
  · simp only [le_add_iff_nonneg_left, zero_le']

/-- If `w` is minimal w.r.t. dominance for `d = 1` and has first entry `0`, then `w = w1`. -/
lemma w1_unique {n : ℕ} [NeZero n] {w : Weight n 1} (hw : w 0 = 0)
  (hmin : ∀ w', w' ≤d w → w ≤d w') :
    w = w1 n := by
  have h₁ := w1_minimal hw
  have h₂ := hmin _ h₁
  have hE : w.E = 1 := by
    conv_rhs => rw [← E_w1 n]
    exact E_dom_eq hw (w1_zero n) h₂ h₁
  ext j
  have hc₁ := (lec_iff _ _).mp
                ((dom_iff_gec_of_balanced hw (w1_balanced n) (hE.trans (E_w1 n).symm)).mp h₂)
  have hsum : (w1 n).sum ≤ w.sum := Finset.sum_le_sum (fun j _ ↦ hc₁ j)
  rw [sum_w1] at hsum
  rw [E] at hE
  simp [Nat.div_eq_zero_iff] at hE
  have hn : w.sum = n := Nat.eq_of_le_of_lt_succ hsum hE
  refine ((Finset.sum_eq_sum_iff_of_le (fun k _ ↦ hc₁ k)).mp ?_ j (Finset.mem_univ j)).symm
  rw [Weight.sum] at hn
  rw [hn]
  exact sum_w1 n

end Weight
