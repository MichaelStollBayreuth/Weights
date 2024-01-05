import Weights.Weights

namespace Weight

open BigOperators

variable {n d : ℕ} [NeZero d]

/-!
## Uniqueness of the minimal complete set of (normalized) weight vectors

We now proceed to show that there is a unique minimal complete set of weight vectors,
when we require the vectors to be "normalized", i.e., to be weakly increasing and
with first entry zero.


### The truncation of a weight
-/

/-- We define `trunc w` such that `trunc w j = min j (E w)`. -/
def trunc (w : Weight n d) : Weight n d := fun j ↦ min (w j) w.E

@[simp] lemma trunc_apply (w : Weight n d) (k : Fin n.succ) : w.trunc k = min (w k) w.E := rfl

lemma trunc_mono_lec {w w' : Weight n d} (h : w ≤c w') : w.trunc ≤c w'.trunc := by
  simp only [lec_iff, trunc_apply]
  exact fun j ↦ min_le_min (h j) (E_lec_mono h)

lemma trunc_lec (w : Weight n d) : w.trunc ≤c w := by
  simp_rw [lec_iff, trunc_apply]
  exact (fun j ↦ min_le_left _ _)

lemma trunc_le_E (w : Weight n d) (j : Fin n.succ) : w.trunc j ≤ w.E := by
  simp only [trunc, min_le_iff, le_refl, or_true]
  done

lemma trunc_zero {w : Weight n d} (h : w 0 = 0) : w.trunc 0 = 0 := by
  simp only [trunc_apply, Nat.min_eq_zero_iff] at h ⊢
  exact Or.inl h

lemma trunc_Monotone {w : Weight n d} (h : Monotone w) : Monotone w.trunc := by
  intro i j hij
  simp only [trunc_apply, min_le_iff, le_min_iff, le_refl, and_true, or_true]
  exact Or.inl (h hij)

lemma trunc_normalized {w : Weight n d} (h : w.normalized) : w.trunc.normalized :=
  ⟨trunc_zero h.1, trunc_Monotone h.2⟩

lemma trunc_pair_lb (w a : Weight n d) (h : ∃ j, w.E < w j ∧ 0 < a j) : w.E ≤ w.trunc.pair a := by
  obtain ⟨j, hj, ha⟩ := h
  have hm := mul_le_pair w.trunc a j
  rw [trunc_apply, min_eq_right_of_lt hj] at hm
  exact (Nat.le_mul_of_pos_left ha).trans hm

lemma trunc_pair_le_pair (w a : Weight n d) : w.trunc.pair a ≤ w.pair a :=
  pair_le_pair_of_lec w.trunc w a (trunc_lec w)

lemma E_trunc_le_E (w : Weight n d) : w.trunc.E ≤ w.E := E_lec_mono (trunc_lec w)

/-- `w` and `trunc w` give the same pairing with `a` if for each `j`, either `w j ≤ E w`
or `a j ≤ 0`. -/
lemma trunc_pair_eq_pair (w a : Weight n d) (h : ∀ j, w.E < w j → a j ≤ 0) :
    w.trunc.pair a = w.pair a := by
  simp only [pair, trunc_apply]
  congr
  ext j
  simp only [mul_eq_mul_left_iff, min_eq_left_iff]
  cases' le_or_lt (w j) w.E with h' h'
  · exact Or.inl h'
  · exact Or.inr <| Nat.eq_zero_of_le_zero (h j h')

/-- `trunc w` dominates `w`. -/
lemma trunc_dom (w : Weight n d) : w.trunc ≤d w := by
  rw [dom_iff, f_le_iff]
  intro a
  simp_rw [f]
  refine (Nat.sub_le_sub_right (E_trunc_le_E w) _).trans ?_
  by_cases h : ∃ j, w.E < w j ∧ 0 < a.1 j
  · rw [Nat.sub_eq_zero_of_le (trunc_pair_lb w a h)]
    exact Nat.zero_le _
  · push_neg at h
    rw [trunc_pair_eq_pair w a h]

/-- `w` dominates `trunc w` (and so they dominate each other) when `E (trunc w) = E w`. -/
lemma trunc_dom' {w : Weight n d} (hE : w.trunc.E = w.E) : w ≤d w.trunc := by
  rw [dom_iff, f_le_iff]
  intro a
  simp_rw [f, ← hE]
  exact Nat.sub_le_sub_left (trunc_pair_le_pair w a) _

/-- The converse: if `w` dominates `trunc w` and `w 0 = 0`, then `E (trunc w) = E w`. -/
lemma E_trunc_eq_E_of_dom {w : Weight n d} (h : w ≤d w.trunc) (h' : w 0 = 0) : w.trunc.E = w.E :=
  E_dom_eq (trunc_zero h') h' (trunc_dom _) h

/-!
### Balanced weights
-/

/-- We define `w` to be *balanced* if `w j ≤ E w` for all `j`. -/
def balanced (w : Weight n d) : Prop := ∀ j, w j ≤ E w

lemma balanced_iff_eq_trunc (w : Weight n d) : w.balanced ↔ w.trunc = w := by
  simp_rw [balanced]
  constructor <;> intro h
  · ext j
    exact min_eq_left_iff.mpr (h j)
  · exact fun j ↦ min_eq_left_iff.mp (congr_fun h j)

lemma balanced_iff_lec_E (w : Weight n d) : w.balanced ↔ w ≤c (w.E : Fin n.succ → ℕ) := by rfl

/-- If `trunc w` has the same exponent as `w`, then `trunc w` is balanced. -/
lemma trunc_balanced {w : Weight n d} (hE : w.trunc.E = w.E) : w.trunc.balanced := by
  rw [balanced_iff_lec_E, hE, lec_iff]
  exact trunc_le_E w

/-!
### Minimal weights are essentially unique

We show that two weights with first entry `0` that are both minimal with respect to domination
and dominate each other must be equal.

This implies that there is a unique minimal complete set of normalized weights
for each dimension `n` and degree `d`; see below.
-/

/-- If `w` and `w'` have the same exponent, then `w' ≤c w` implies that `w` dominates `w'`. -/
lemma dom_of_gec {w w' : Weight n d} (hE : E w = E w') (h : w' ≤c w) : w ≤d w' := by
  simp only [dom_iff, f_le_iff, f_apply, SetCoe.forall, Subtype.coe_mk, hE]
  exact fun a _ ↦ Nat.sub_le_sub_left (pair_le_pair_of_lec _ _ _ h) _

/-- If `w` has first entry `0`, `w'` is balanced, and `E w = E w'`, then `w ≤d w' ↔ w' ≤c w`. -/
lemma dom_iff_gec_of_balanced {w w' : Weight n d} (hw₁ : w 0 = 0) (hw'₂ : w'.balanced)
    (hE : E w = E w') :
    w ≤d w' ↔ w' ≤c w := by
  refine ⟨fun h ↦ (lec_iff _ _).mpr (fun j ↦ ?_), dom_of_gec hE⟩
  have hw₃ := eval_f_tw w j
  simp only [hw₁, mul_zero, tsub_zero] at hw₃
  have h' := h (tw n d j)
  rw [hw₃, eval_f_tw w' j, hE, Nat.sub_sub, add_comm, ← Nat.sub_sub] at h'
  exact (tsub_le_tsub_iff_left (hw'₂ j)).mp (h'.trans $ Nat.sub_le _ _)

/-- A helper lemma: if `w` is not balanced, but such that `E w = E (trunc w)`, and has at least
one zero entry, then increasing this entry to `1` gives a weight `w'` that is balanced, has
the same exponent as `w` and is strictly larger than `w` in the product order. -/
lemma exists_balanced_ltc (w : Weight n d) (hb : ¬ w.balanced)
    (hE : w.trunc.E = w.E) {k : Fin n.succ} (hk : w k = 0) :
    let w' : Weight n d := Function.update w.trunc k 1
    w'.E = w.trunc.E ∧ w'.balanced ∧ w.trunc ≤c w' ∧ w.trunc ≠ w' := by
  intro w'
  simp only [balanced] at hb
  push_neg at hb
  obtain ⟨j, hj⟩ := hb
  have hsum' : w'.sum = w.trunc.sum + 1
  · simp only [Weight.sum, ne_eq, Function.update_apply, trunc_apply, ge_iff_le, Finset.sum_ite,
      Finset.mem_univ, forall_true_left, Finset.filter_eq', ite_true, Finset.sum_const,
      Finset.card_singleton, smul_eq_mul, mul_one, forall_eq, Finset.filter_ne', not_true]
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ k), add_comm, add_left_inj, hk]
    simp only [Finset.mem_univ, not_true, ge_iff_le, zero_le, min_eq_left, add_zero]
    done
  have hE' : w'.E = w.trunc.E
  · rw [E, hsum', hE]
    refine le_antisymm ?_ (le_of_eq_of_le hE.symm ?_) <;> rw [E, add_le_add_iff_right]
    · have hsum : w.trunc.sum < w.sum :=
        Finset.sum_lt_sum (fun j _ ↦ (lec_iff _ _).mp (trunc_lec w) j)
                          ⟨j, Finset.mem_univ j, lt_of_le_of_lt (trunc_le_E w j) hj⟩
      exact Nat.div_le_div_right (Nat.mul_le_mul_right _ $ Nat.succ_le_iff.mpr hsum)
    · exact Nat.div_le_div_right (Nat.mul_le_mul_right _ (Nat.le_succ _))
  refine ⟨hE', fun j ↦ ?_, (lec_iff _ _).mpr (fun j ↦ ?_), fun hf ↦ ?_⟩
  · -- show `balanced w'`
    simp only [ne_eq, Function.update_apply, trunc_apply, ge_iff_le, hE']
    split_ifs
    · exact one_le_E _
    · exact trunc_balanced hE _
  · -- show `w.trunc ≤c w'`
    simp only [Function.update_apply]
    by_cases hjk : j = k <;>
      simp only [hjk, (Nat.eq_zero_of_le_zero (le_of_le_of_eq (trunc_lec w k) hk)),
        zero_le', if_false]
    · exact Nat.le_refl (trunc w j)
  · -- show `w.trunc ≠ w'`.
    rw [hf, self_eq_add_right] at hsum'
    exact Nat.one_ne_zero hsum'

/-- If `w` is normalized, then there is an index `k` such that `w k = 0` and replacing
this entry by `1` still gives a monotone weight. -/
lemma index_exists {w : Weight n d} (hw : w.normalized) :
    ∃ k, w k = 0 ∧ Monotone (Function.update w k 1) := by
  let P : ℕ → Prop := (fun i ↦ if hi : i < n.succ then w ⟨i, hi⟩ = 0 else False)
  have hP : ∀ m (hm : m < n.succ), P m ↔ w ⟨m, hm⟩ = 0 := fun  m hm ↦ by simp only [hm, dif_pos]
  let m : Fin n.succ := ⟨Nat.findGreatest P n, Nat.lt_succ_of_le (Nat.findGreatest_le n)⟩
  have hm : w m = 0
  · have h₀ : P 0 := by rw [hP 0 (Nat.zero_lt_succ n)]; exact hw.1
    rw [← hP]
    exact Nat.findGreatest_spec (Nat.zero_le n) h₀
  refine ⟨m, hm, fun i j hij ↦ ?_⟩
  simp only [Function.update_apply]
  by_cases hi : i = m <;> by_cases hj : j = m <;> simp [hi, hj]
  · have hij' : m < j := hi.symm ▸ lt_of_le_of_ne hij (hi.symm ▸ Ne.symm hj)
    have := Nat.findGreatest_is_greatest hij' (Nat.le_of_lt_succ j.2)
    simp only [Fin.is_lt, Fin.eta, dite_eq_ite, ite_true, ← Ne.def] at this
    exact Nat.one_le_iff_ne_zero.mpr this
  · exact (le_of_le_of_eq (hw.2 (le_of_le_of_eq hij hj)) hm).trans zero_le_one
  · exact hw.2 hij

/-- If `w` has first entry `0` and is minimal w.r.t. `≤d`, then `w` is balanced. -/
lemma balanced_of_min {w : Weight n d} (hw : w 0 = 0) (hmin : ∀ u, u ≤d w → w ≤d u) :
    w.balanced := by
  by_contra hb
  obtain ⟨hE', hb', hc, hne⟩ :=
    exists_balanced_ltc w hb (E_trunc_eq_E_of_dom (hmin _ (trunc_dom w)) hw) hw
  -- We use that `≤d` is equivalent to `≥c` under suitable assumptions.
  exact hne (lec_antisymm hc <| (dom_iff_gec_of_balanced (trunc_zero hw) hb' hE'.symm).mp <|
              (trunc_dom w).trans <| hmin _  <| (dom_of_gec hE' hc).trans $ trunc_dom w)

/-- If `w` is normalized and minimal w.r.t. `≤d` on monotone weights, then `w` is balanced. -/
lemma balanced_of_min' {w : Weight n d} (hw : w.normalized)
    (hmin : ∀ u : Weight n d, (Monotone u) → u ≤d w → w ≤d u) :
    w.balanced := by
  by_contra hb
  obtain ⟨k, hk₁, hk₂⟩ := index_exists hw
  obtain ⟨hE', hb', hc, hne⟩ :=
    exists_balanced_ltc w hb
      (E_trunc_eq_E_of_dom (hmin _ (trunc_normalized hw).2 w.trunc_dom) hw.1) hk₁
  -- We use that `≤d` is equivalent to `≥c` under suitable assumptions.
  refine hne <| lec_antisymm hc <|
    (dom_iff_gec_of_balanced (trunc_normalized hw).1 hb' hE'.symm).mp <|
    w.trunc_dom.trans <| hmin _ ?_ <| (dom_of_gec hE' hc).trans w.trunc_dom
  intro i j hij
  simp only [Function.update_apply, trunc_apply]
  cases' eq_or_ne i k with hi hi <;> cases' eq_or_ne j k with hj hj <;> simp [hi, hj]
  · have : w j = Function.update w k 1 j := by simp only [Function.update_apply, hj, if_false]
    refine ⟨?_, one_le_E w⟩
    rw [(Function.update_same k 1 w).symm, this]
    exact hk₂ (le_of_eq_of_le hi.symm hij)
  · exact Or.inl ((le_of_le_of_eq (hw.2 (le_of_le_of_eq hij hj)) hk₁).trans zero_le_one)
  · cases' le_or_lt w.E (w j) with h h
    · exact Or.inr h
    · exact Or.inl (hw.2 hij)

/-- If two weights with first entry `0` dominate each other and are minimal w.r.t. `≤d`,
then they are equal. -/
lemma eq_of_dom_and_min {w w' : Weight n d} (hw : w 0 = 0) (hw' : w' 0 = 0) (h : w' ≤d w)
    (hmin : ∀ u, u ≤d w → w ≤d u) :
    w = w' := by
  have h₁ := hmin _ h                   -- `w ≤d w'`
  have hmin' := fun u (hu : u ≤d w') ↦ h.trans (hmin u (hu.trans h)) -- `w'` is minimal
  have hb := balanced_of_min hw hmin    -- `w` is balanced
  have hb' := balanced_of_min hw' hmin' -- `w'` is balanced
  have hE := E_dom_eq hw hw' h₁ h       -- `E w = E w'`
  exact lec_antisymm
    ((dom_iff_gec_of_balanced hw' hb hE.symm).mp h) ((dom_iff_gec_of_balanced hw hb' hE).mp h₁)

/-- If two normalized weights dominate each other and are minimal w.r.t. `≤d` on normalized weights,
 then they are equal. -/
lemma eq_of_dom_and_min' {w w' : Weight n d} (hw : w.normalized) (hw' : w'.normalized)
    (h : w' ≤d w) (hmin : ∀ u, normalized u → u ≤d w → w ≤d u) :
    w = w' := by
  have hminw := (min_Monotone_iff_min_normalized w).mpr hmin
                                          -- `w` is minimal w.r.t. monotone weights
  have h₁ := hmin _ hw' h                 -- `w ≤d w'`
  have hminw' := fun u (hum : Monotone u) (hu : u ≤d w') ↦ h.trans (hminw u hum (hu.trans h))
                                          -- `w'` is minimal w.r.t. monotone weights
  have hb := balanced_of_min' hw hminw    -- `w` is balanced
  have hb' := balanced_of_min' hw' hminw' -- `w'` is balanced
  have hE := E_dom_eq hw.1 hw'.1 h₁ h     -- `E w = E w'`
  exact lec_antisymm
    ((dom_iff_gec_of_balanced hw'.1 hb hE.symm).mp h) ((dom_iff_gec_of_balanced hw.1 hb' hE).mp h₁)

/-!
### Domination and permutations
-/

/-- If a monotone weight `w` dominates another weight `w'`, then `w` dominates `w'` made monotone
by sorting. -/
lemma dom_of_dom_perm {w w' : Weight n d} (hw : Monotone w) (hd : w ≤d w') : w ≤d w'.sorted := by
  refine Tuple.bubble_sort_induction hd (fun (g : Weight n d) i j hij₁ hij₂ hwg ↦ ?_)
  let g' := g.comp (Equiv.swap i j)
  change w ≤d g'
  simp only [dom_iff, f_le_iff, f_apply, SetCoe.forall, Subtype.coe_mk] at hwg ⊢
  have hgg' : g'.comp (Equiv.swap i j) = g
  · ext
    simp only [Weight.comp, Function.comp_apply, Equiv.swap_apply_self]
    done
  have hgs : g' i ≤ g' j
  · simp only [Weight.comp, Function.comp_apply, Equiv.swap_apply_left, Equiv.swap_apply_right]
    exact le_of_lt hij₂
  intro a ha
  rw [E_perm g (Equiv.swap i j)]
  cases' le_or_lt (a i) (a j) with ham ham
  · rw [tsub_le_iff_right]
    specialize hwg (a.comp (Equiv.swap i j)) (testvecs_perm ha _)
    rw [pair_swap_eq g, tsub_le_iff_right] at hwg
    refine hwg.trans ?_
    rw [add_le_add_iff_left]
    exact pair_swap_le (hw (le_of_lt hij₁)) ham
  · let a' := a.comp (Equiv.swap i j)
    have haa' : a'.comp (Equiv.swap i j) = a
    · ext
      simp only [Weight.comp, Function.comp_apply, Equiv.swap_apply_self]
      done
    have ham' : a' i ≤ a' j
    · simp only [Weight.comp, Function.comp_apply, Equiv.swap_apply_left, Equiv.swap_apply_right]
      exact le_of_lt ham
    have hag : g'.pair a' = pair g a := by simp only [pair_swap_eq g' a, hgg']
    have := pair_swap_le (n := n) (d := d) hgs ham'
    simp only [haa', hag] at this
    exact (hwg a ha).trans (Nat.sub_le_sub_left this _)

lemma dom_of_dom_perm' {w w' : Weight n d} (hw' : Monotone w') (hd : w ≤d w') :
    w.sorted ≤d w' := by
  convert dom_of_dom_perm (sorted_is_Monotone w) ((dom_perm w w' (Tuple.sort w)).mpr hd)
  rw [sorted, comp_comp]
  have help : w' = w'.comp (Tuple.sort w') ↔ Monotone w'
  · change w' ∘ Equiv.refl _ = _ ↔ Monotone (w' ∘ Equiv.refl _)
    exact Tuple.comp_sort_eq_comp_iff_monotone
  rw [help.mpr hw', comp_comp, eq_comm]
  apply Tuple.comp_sort_eq_comp_iff_monotone.mpr
  let w'' := (w'.comp (Tuple.sort w)).comp (Tuple.sort (w'.comp (Tuple.sort w)))
  have hw'' : Monotone w'' := sorted_is_Monotone _
  have h : w'' = w' ∘ ⇑(Tuple.sort w' * (Tuple.sort w *
                    Tuple.sort ((w'.comp (Tuple.sort w')).comp (Tuple.sort w))))
  · simp only [Weight.comp, Equiv.Perm.coe_mul]
    rw [← Function.comp.assoc w' (Tuple.sort w'), Tuple.sort_eq_refl_iff_monotone.mpr hw']
    simp only [Equiv.coe_refl, Function.comp.right_id]
    rfl
  rwa [← h]

/-!
### Minimal complete sets of weight vectors
-/

/-- We define a set `S` of weight vectors to be *complete* if every normalized weight vector
is dominated by some `w ∈ S`. (By `dom_of_dom_perm`, this is equivalent to saying that some
permutation of every weight vector is dominated by some element of `S`. ) -/
def complete_set (S : Set (Weight n d)) : Prop :=
  ∀ w : Weight n d, w.normalized → ∃ w' ∈ S, w' ≤d w

/-- A complete set `S` of weight vectors is *minimal* if no element of `S` dominates another. -/
def minimal_complete_set (S : Set (Weight n d)) : Prop :=
  complete_set S ∧ ∀ w₁ w₂, w₁ ∈ S → w₂ ∈ S → w₁ ≤d w₂ → w₁ = w₂

/-- We define `M` to be the set of all minimal normalized weight vectors. -/
def M (n d : ℕ) [NeZero d] : Set (Weight n d) :=
  {w | w.normalized ∧ ∀ w', normalized w' → w' ≤d w → w ≤d w'}

/-- The set of all minimal normalized weight vectors is complete. -/
lemma M_is_complete : complete_set (M n d) := by
  intro w
  refine WellFoundedLT.induction (α := Weight n d)
    (C := fun w ↦ normalized w → ∃ w', w' ∈ M n d ∧ w' ≤ w) w (fun w₁ h ↦ ?_)
  intro hw₁n
  by_cases hw₁ : ∃ w₂ : Weight n d, w₂.normalized ∧ w₂ < w₁
  · obtain ⟨w₂, hw₂n, hw₂⟩ := hw₁
    obtain ⟨w', hw'₁, hw'₂⟩ := h w₂ hw₂ hw₂n
    exact ⟨w', hw'₁, hw'₂.trans <| le_of_lt hw₂⟩
  · push_neg at hw₁
    refine ⟨w₁, ⟨hw₁n, fun w' hw' h' ↦ ?_⟩, le_refl w₁⟩
    by_contra hf
    have := hw₁ w' hw'
    rw [lt_iff_le_not_le] at this
    push_neg at this
    exact hf (this h')

/-- If a normalized weight `w` dominates a weight `w' ∈ M n d`, then `w = w'`. -/
lemma eq_of_dom_in_M {w w' : Weight n d} (hw : w.normalized) (hd : w ≤d w') (hM : w' ∈ M n d) :
    w = w' :=
  (eq_of_dom_and_min' hM.1 hw hd hM.2).symm

/-- The set of all minimal normalized weight vectors is a minimal complete set. -/
lemma M_is_minimal : minimal_complete_set (M n d) :=
  ⟨M_is_complete, fun ?w₁ ?w₂ hw₁ hw₂ h₁ ↦ eq_of_dom_in_M hw₁.1 h₁ hw₂⟩

/-- If `S` is a minimal complete set of normalized weight vectors, then `S = M n d`. -/
lemma M_is_unique {S : Set (Weight n d)} (hS₁ : ∀ w ∈ S, normalized w)
    (hS₂ : minimal_complete_set S) :
    S = M n d := by
  ext w
  refine ⟨fun h ↦ ⟨hS₁ w h, fun w' hw'₁ hw'₂ ↦ ?_⟩, fun h ↦ ?_⟩
  · obtain ⟨w₁, hw₁, hle⟩ := hS₂.1 w' hw'₁
    exact le_of_eq_of_le (hS₂.2 w₁ w hw₁ h (hle.trans hw'₂)).symm hle
  · obtain ⟨hw₁, hw₂⟩ := h
    obtain ⟨w', hw'₁, hw'₂⟩ := hS₂.1 w hw₁
    suffices heq : w' = w
    · exact heq ▸ hw'₁
    exact eq_of_dom_and_min' (hS₁ w' hw'₁) hw₁ (hw₂ w' (hS₁ w' hw'₁) hw'₂)
                             (fun u hu₁ hu₂ ↦ hw'₂.trans (hw₂ u hu₁ (hu₂.trans hw'₂)))

lemma not_in_M_of_dom_ne {w : Weight n d}
    (hw : ∃ w' : Weight n d, w'.normalized ∧ w' ≤d w ∧ w' ≠ w) :
    w ∉ M n d := by
  obtain ⟨w', hw'₁, hw'₂, hw'₃⟩ := hw
  by_contra! hf
  exact hw'₃ (eq_of_dom_in_M hw'₁ hw'₂ hf)

/-- Non-zero elements of `M n d` have coprime entries. -/
lemma gcd_eq_one_of_in_M {w : Weight n d} (h₀ : w ≠ 0) (hM : w ∈ M n d) :
    Finset.univ.gcd w = 1 := by
  set g := Finset.univ.gcd w
  by_contra hfg
  have hg : 1 < g
  · refine lt_of_le_of_ne (Nat.one_le_iff_ne_zero.mpr ?_) (Ne.symm hfg)
    by_contra! hg
    have h₀' : w = 0
    · ext
      simp only [Finset.mem_univ, Finset.gcd_eq_zero_iff.mp hg, zero_apply]
      done
    exact h₀ h₀'
  let w' : Weight n d := fun i ↦ (w i) / g
  have hww' : w = g • w'
  · ext i
    simp only [Pi.smul_apply, Algebra.id.smul_eq_mul]
    exact (Nat.mul_div_cancel_left' (Finset.gcd_dvd (Finset.mem_univ i))).symm
  have hww'i i : w i = g * w' i := congrFun hww' i
  refine (not_in_M_of_dom_ne ⟨w', ⟨?_, ?_⟩, ?_, ?_⟩) hM
  · simp only
    rw [hM.1.1, Nat.zero_div]
    done
  · simp only
    exact fun i j hij ↦ Nat.div_le_div_right (hM.1.2 hij)
  · rw [hww', dom_iff]
    have := f_le_mul w' g.pred
    rwa [Nat.succ_pred_eq_of_pos (zero_lt_one.trans hg)] at this
  · obtain ⟨i, hi⟩ : ∃ i, w i ≠ 0 := by by_contra! hf; exact h₀ (funext hf)
    have hi' : w' i ≠ 0 := fun hf ↦ hi <| mul_zero g ▸ hf ▸ hww'i i
    intro hf
    rw [hww'] at hf
    have h₁ := congr_fun hf i
    rw [smul_apply] at h₁
    exact hfg (mul_right_cancel₀ hi' ((one_mul _).trans h₁)).symm

end Weight
