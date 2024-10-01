import Mathlib.Data.Fin.Tuple.NatAntidiagonal
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.RingTheory.Int.Basic
import Mathlib.Data.Fin.Tuple.BubbleSortInduction
import Mathlib.Data.DFinsupp.WellFounded
import Weights.Auxiliary

/-!
# Formalize some parts of the theory of weights

This is code formalizing some of the results in the paper
[*Minimization of hypersurfaces*](https://www.mathe2.uni-bayreuth.de/stoll/schrift.html#AG69)
by Andreas-Stephan Elsenhans and Michael Stoll.

The paper introduces the notion of a *weight* on forms of degree $d$
in $n+1$ variables, which is simply an $(n+1)$-tuple of natural numbers.
We index the entries from $0$ to $n$. See `Weight`.

We can then compare weights in the following way. We first define $J_{n,d}$
to be the Set of $(n+1)$-tuples of natural numbers whose sum is $d$ (`Weight.testvecs n d`).
Then to a weight $w$, we associate the map $f_w \colon J_{n,d} \to \mathbb{Z}_{\ge 0}$
given by sending $a \in J_{n,d}$ to
$\max\Bigl\{0, \Bigl\lfloor\frac{d \Sigma w}{n+1}\Bigr\rfloor - \langle a, w \rangle\Bigr\}$
(where $\Sigma w$ denotes the sum of the entries of $w$). See `Weight.f`.

Then we say that a weight $w$ *dominates* another weight $w'$ if $f_w \le f_{w'}$
point-wise. In this file, we write `w ≤d w'` for this relation. `≤d` is a pre-order
on the set of weights, but not a (partial) order. For example, a weight $w$
and $w + k \mathbf{1}$ dominate each other for each natural number $k$.
We can therefore restrict to weights whose minimal entry is zero.

We say that a weight $w$ that is (weakly) increasing and such that $w_0 = 0$
is *normalized* (`Weight.normalized`). We show that if a normalized weight $w$ dominates
some weight $w'$, then it also dominates the increasing permutation of $w'$
(`Weight.dom_of_dom_perm`). So up to permutations, it suffices to consider
only normalized weights.

We say that a set $S$ of normalized weights is *complete* if every normalized
weight is dominated by an element of $S$ (`Weight.complete_set`). We say that a complete
set of weights is *minimal* if it is minimal with respect to inclusion among complete sets
(`Weight.minimal_complete_set`). This is equivalent to saying that when $w$ and $w'$ are
in $S$ and $w$ dominates $w'$, then $w = w'$.

The first main result formalized here is that there is a *unique* minimal complete set
of weights, which is given by the set `Weight.M n d` of all normalized weights that are minimal
elements with respect to domination within the set of all normalized weights.
This is **Proposition 3.13** in the paper. See `Weight.M_is_minimal` and `Weight.M_is_unique`.

We show in addition that the entries of nonzero elements of `M n d` are coprime
(`Weight.gcd_eq_one_of_in_M`) and that `M n 1` consists of the single
element $(0,1,\ldots,1)$ (`Weight.w1_unique`).

The second main result is a proof of **Theorem 1.6** in the paper, which says that
in the case $n = 2$, the weights in a minimal complete set of normalized weights
have entries bounded by the degree $d$. See `Weight.dom_by_max_le_d` and `Weight.theorem_1_6`.
-/

/-!
## Definitions and first properties
-/

/-!
### Weights
-/

/-- A *weight* of *dimension* `n` and *degree* `d` is a map from `{0..n}` to `ℕ`. -/
def Weight (n _d : ℕ) : Type := Fin n.succ → ℕ
-- deriving One, AddCommMonoid -- does not work

namespace Weight

-- Derive the necessary instances manually
protected instance One (n d : ℕ) : One (Weight n d) := ⟨fun _ ↦ 1⟩

protected instance AddCommMonoid (n d : ℕ) : AddCommMonoid (Weight n d) := by
  unfold Weight; infer_instance

open BigOperators

variable {n d : ℕ} -- fix dimension and (positive) degree

/-!
### Some boilerplate `simp` and `ext` lemmas
-/

@[simp] lemma add_apply (w w' : Weight n d) (i : Fin n.succ) : (w + w') i = w i + w' i := rfl

@[simp] lemma smul_apply (w : Weight n d) (k : ℕ) (i : Fin n.succ) : (k • w) i = k * w i := rfl

@[simp] lemma one_apply (i : Fin n.succ) : (1 : Weight n d) i = 1 := rfl

@[simp] lemma zero_apply (i : Fin n.succ) : (0 : Weight n d) i = 0 := rfl

@[ext] lemma ext {w w' : Weight n d} (h : ∀ i, w i = w' i) : w = w' := funext h

/-!
### Permutations of weights
-/

/-- Permute a weight by pre-composing with a permutation. -/
-- Writing `w ∘ σ` directly is problematic, since this gets cast to `Fin n.succ → ℕ`,
-- from which `d` cannot be recovered.
protected def comp (w : Weight n d) (σ : Equiv.Perm (Fin n.succ)) : Weight n d := w ∘ σ

lemma comp_comp (w : Weight n d) (σ τ : Equiv.Perm (Fin n.succ) ) :
    (w.comp σ).comp τ = w.comp (σ * τ) := by
  simp only [Weight.comp, Equiv.Perm.coe_mul]
  rfl

@[simp] lemma comp_one (w : Weight n d) : w.comp 1 = w := rfl

@[simp] lemma comp_apply (w : Weight n d) (σ : Equiv.Perm (Fin n.succ)) (i : Fin n.succ) :
    (w.comp σ) i = w (σ i) := rfl

/-!
### Sum of a weight
-/

/-- The *sum* of a weight is the sum of its entries. -/
protected def sum (w : Weight n d) : ℕ := ∑ j, w j

@[simp] lemma sum_perm (w : Weight n d) (σ : Equiv.Perm (Fin n.succ)) :
    (w.comp σ).sum = w.sum := by
  simp only [Weight.sum, Function.comp_apply]
  exact Fintype.sum_bijective σ (Equiv.bijective σ) _ _ (fun i ↦ rfl)

@[simp] lemma sum_smul (w : Weight n d) (k : ℕ) : (k • w).sum = k * w.sum := by
  simp only [Weight.sum, Finset.mul_sum]
  rfl

lemma sum_add (w w' : Weight n d) : (w + w').sum = w.sum + w'.sum := by
  simp only [Weight.sum, add_apply, Finset.sum_add_distrib]

/-!
### Pairing
-/

/-- The *pairing* of two weights is their scalar product. -/
def pair (w a : Weight n d) : ℕ := ∑ j, a j * w j

lemma mul_le_pair (w a : Weight n d) (k : Fin n.succ) : (a k) * (w k) ≤ w.pair a := by
  simp [pair]
  rw [Finset.sum_eq_add_sum_diff_singleton (Finset.mem_univ k)]
  exact Nat.le_add_right _ _

lemma pair_add_left (w w' a : Weight n d) : (w + w').pair a = w.pair a + w'.pair a := by
  simp only [pair, add_apply, mul_add, Finset.sum_add_distrib]

@[simp] lemma pair_smul_left (w a : Weight n d) (k : ℕ) : (k • w).pair a = k * w.pair a := by
  simp_rw [pair, smul_apply, mul_left_comm]
  exact (Finset.mul_sum Finset.univ (fun i ↦ a i * w i) k).symm

open Finset in
/-- If `w` and `a` are both increasing or both decreasing on `{i, j}`,
then swapping `a i` and `a j` decreases `pair w a`. -/
lemma pair_swap_le {w a : Weight n d} {i j : Fin n.succ} (hw : w i ≤ w j) (ha : a i ≤ a j) :
    w.pair (a.comp $ Equiv.swap i j) ≤ w.pair a := by
  cases' eq_or_ne i j with h h
  · simp only [Weight.comp, h, Equiv.swap_self, Equiv.coe_refl, Function.comp_id, le_refl]
  · have haij {k} (hk : k ∈ (univ.erase j).erase i) : (a.comp (Equiv.swap i j)) k = a k := by
      rw [comp_apply,
          Equiv.swap_apply_of_ne_of_ne (ne_of_mem_erase hk)
                                       (ne_of_mem_erase (mem_of_mem_erase hk))]
    have ht {k} (hk : k ∈ (univ.erase j).erase i) :
        (a.comp (Equiv.swap i j)) k * w k = a k * w k :=
      congr_arg (· * w k) <| haij hk
    simp only [pair]
    rw [← add_sum_erase _ _ (mem_univ i), ← add_sum_erase _ _ (mem_univ j),
        ← add_sum_erase _ _ (mem_erase.mpr ⟨h.symm, mem_univ _⟩),
        ← add_sum_erase _ _ (mem_erase.mpr ⟨h, mem_univ _⟩),
        erase_right_comm, sum_congr rfl @ht, ← add_assoc, ← add_assoc]
    simp only [comp_apply, Equiv.swap_apply_left, Equiv.swap_apply_right, add_le_add_iff_right]
    rw [add_comm (a j * w i), add_comm (a j * w j)]
    exact mul_add_mul_le_mul_add_mul ha hw

lemma pair_perm (w a : Weight n d) (σ : Equiv.Perm (Fin n.succ)) :
    pair (w.comp σ) (a.comp σ) = pair w a := by
  simp only [Weight.comp, pair, Function.comp_apply]
  exact Fintype.sum_bijective σ (Equiv.bijective _) _ _ (fun k ↦ rfl)

lemma pair_perm' (w a : Weight n d) (σ : Equiv.Perm (Fin n.succ)) :
    pair (w.comp σ) a = pair w (a.comp σ⁻¹) := by
  rw [← pair_perm w _ σ]
  simp only [comp_comp, inv_mul_cancel, comp_one]

lemma pair_swap_eq (w a : Weight n d) (i j : Fin n.succ) :
    pair w (a.comp $ Equiv.swap i j) = pair (w.comp $ Equiv.swap i j) a := by
  convert (pair_perm' w a _).symm
  simp only [Equiv.swap_inv]

/-!
### Test vectors
-/

/-- We define the set of *test vectors* of dimension `n` and degree `d` to be the
set of weights whose sum is `d`. -/
def testvecs (n d : ℕ) : Set (Weight n d) := {w | w.sum = d}

lemma pair_shift (a : testvecs n d) (k : ℕ) : (k • (1 : Weight n d)).pair a = k * d := by
  simp only [pair, smul_apply, one_apply, mul_one]
  rw [mul_comm k, ← Finset.sum_mul]
  exact congr_arg (· * k) a.2

-- Maybe better use the Finset right away?
lemma tv_finset :
    ((Finset.Nat.antidiagonalTuple n.succ d) : Set (Fin n.succ → ℕ)) = testvecs n d := by
  simp only [testvecs]
  ext a
  simp only [Finset.Nat.mem_antidiagonalTuple, Finset.mem_coe, Finset.mem_mk, Weight.sum]
  rfl

/-- The set of test vectors is closed under permutation. -/
lemma testvecs_perm {a : Weight n d} (ha : a ∈ testvecs n d) (σ : Equiv.Perm (Fin n.succ)) :
    a.comp σ ∈ testvecs n d := by
  simpa only [testvecs, sum_perm, Set.mem_setOf_eq]

/-- The test vector `(d-1,0,...,1,...,0)` (`1` in position `k`),
for `k = 0`, this is `(d,0,...,0)`. First we define it as a weight. -/
def tw' (n d : ℕ) (k : Fin n.succ) : Weight n d :=
  (d - 1) • (Function.update (0 : Weight n d) 0 1) + Function.update (0 : Weight n d) k 1

-- then prove it has sum `d`.
lemma tw'_sum (n d : ℕ) [NeZero d] (k : Fin n.succ) : (tw' n d k).sum = d := by
  simp only [Weight.sum, tw', nsmul_eq_mul, Pi.natCast_def, Nat.cast_tsub, Nat.cast_id,
    Nat.cast_one, Pi.add_apply, Pi.mul_apply, Function.update_apply, zero_apply, mul_ite, mul_one,
    mul_zero, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  exact Nat.sub_add_cancel (Nat.one_le_of_lt (NeZero.pos d))

/-- Now we define the test vector `(d-1,0,...,1,...,0)` as an element of `testvecs n d`. -/
def tw (n d : ℕ) [NeZero d] (k : Fin n.succ) : testvecs n d := ⟨tw' n d k, tw'_sum n d k⟩

/-- The test vectors given by `tw n d` are pairwise distinct. -/
lemma tw_inj (n d : ℕ) [NeZero d] : Function.Injective (tw n d) := by
  intro j k h
  simp only [tw, tw', nsmul_eq_mul, Pi.natCast_def, Nat.cast_tsub, Nat.cast_id, Nat.cast_one,
    Subtype.mk.injEq] at h
  replace h := congr_fun h k
  simp only [Pi.add_apply, Pi.mul_apply, Function.update_apply, zero_apply, mul_ite, mul_one,
    mul_zero, if_true, add_right_inj, ite_eq_left_iff, zero_ne_one] at h
  exact (of_not_not h).symm

lemma pair_tw [NeZero d] (w : Weight n d) (k : Fin n.succ) :
    w.pair (tw n d k) = (d - 1) * (w 0) + (w k) := by
  simp only [pair, tw, tw', nsmul_eq_mul, Pi.natCast_def, Nat.cast_tsub, Nat.cast_id, Nat.cast_one,
    Pi.add_apply, Pi.mul_apply, Function.update_apply, zero_apply, mul_ite, mul_one, mul_zero,
    add_mul, ite_mul, zero_mul, one_mul, Finset.sum_add_distrib, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]

/-!
### The exponent of a weight
-/

/-- The *exponent* `E w` of a weight is `⌊w.sum*d/(n+1)⌋ + 1`.
(Note that we use that `/` is the quotient of division with remainder on `ℕ`.) -/
def E (w : Weight n d) : ℕ := w.sum * d / (n + 1) + 1

lemma one_le_E (w : Weight n d) : 1 ≤ w.E := by simp only [E, le_add_iff_nonneg_left, zero_le']

@[simp] lemma E_perm (w : Weight n d) (σ : Equiv.Perm (Fin n.succ)) : (w.comp σ).E = w.E := by
  simp only [E, sum_perm]

@[simp] lemma E_shift (w : Weight n d) (k : ℕ) : (w + k • (1 : Weight n d)).E = w.E + k * d := by
  simp only [E, Weight.sum, Nat.succ_eq_add_one, add_apply, smul_apply, one_apply, mul_one,
    Finset.sum_add_distrib, Finset.sum_const, Finset.card_fin, smul_eq_mul]
  rw [add_mul, mul_assoc, Nat.add_mul_div_left _ _ (Nat.succ_pos n)]
  abel

/-!
### The map associated to a weight
-/

/-- We associate to a weight `w` a map `testvecs n d → ℕ`.
(Here we use that `-` is truncated subtraction: `a - b = 0` when `a ≤ b`. ) -/
def f (w : Weight n d) (a : testvecs n d) : ℕ := w.E - (pair w a)

-- The set of maps from test vectors to `ℕ` inherits a partial order, which is defined point-wise.
example : PartialOrder (testvecs n d → ℕ) := inferInstance

@[simp] lemma f_le_iff (w w' : Weight n d) :
    f w ≤ f w' ↔ ∀ a : testvecs n d, f w a ≤ f w' a := Iff.rfl

@[simp] lemma f_apply (w : Weight n d) (a : testvecs n d) : f w a = w.E - (pair w a) := rfl

lemma eval_f_tw [NeZero d] (w : Weight n d) (k : Fin n.succ) :
    f w (tw n d k) = w.E - (d - 1) * (w 0) - (w k) := by
  simp only [f, pair, ge_iff_le, tsub_le_iff_right, Nat.sub_sub]
  exact congr_arg (E w - ·) <| pair_tw w k

lemma f_eq_on_shift (w : Weight n d) (k : ℕ) : (w + k • (1 : Weight n d)).f = w.f := by
  ext a
  simp only [f_apply, E_shift, pair_add_left, pair_shift, add_tsub_add_eq_tsub_right]

/-- The map associated to `w` is pointwise below that associated to a positive multiple of `w`. -/
lemma f_le_mul (w : Weight n d) (k : ℕ) : w.f ≤ (k.succ • w).f := by
  simp only [E, f_le_iff, f_apply, sum_smul, pair_smul_left, SetCoe.forall, Subtype.coe_mk]
  intro a _
  have H : w.sum * d / (n + 1) + 1 - w.pair a
             ≤ k.succ * (w.sum * d / (n + 1)) + 1 - k.succ * w.pair a := by
    set m := w.sum * d / (n + 1)
    set l := w.pair a
    cases' lt_or_le m l with hlt hle
    · rw [Nat.sub_eq_zero_of_le hlt]
      exact Nat.zero_le _
    · rw [← tsub_add_eq_add_tsub hle, ← tsub_add_eq_add_tsub (mul_le_mul' le_rfl hle),
          ← Nat.mul_sub_left_distrib]
      exact add_le_add_right (Nat.le_mul_of_pos_left _ (Nat.succ_pos k)) 1
  refine H.trans <| Nat.sub_le_sub_right (add_le_add_right ?_ _) _
  rw [mul_assoc]
  exact Nat.mul_div_le_mul_div_assoc ..

/-!
### Domination
-/

/-- Define `w ≤d w'` if `w` dominates `w'`. This is equivalent to `f w ≤ f w'`
in the product order. -/
protected instance Preorder : Preorder (Weight n d) := Preorder.lift f

instance fintype_tv : Fintype (testvecs n d) := by
  refine Fintype.ofFinset (Finset.Nat.antidiagonalTuple n.succ d) (fun a ↦ ?_)
  rw [← tv_finset]
  simp only [Finset.mem_coe]

lemma codom_f_well_founded : WellFoundedLT (testvecs n d → ℕ) := inferInstance

instance well_founded : IsWellFounded (Weight n d) (· < ·) :=
  ⟨InvImage.wf f codom_f_well_founded.1⟩

/-- Introduce notation `≤d` for domination -/
infix:50 " ≤d " => @LE.le (Weight _ _) _

/-- Introduce notation `≤c` ("component-wise") for the product order-/
infix:50 " ≤c " => @LE.le (Fin _ → ℕ) _

@[simp] lemma dom_iff (w w' : Weight n d) : w ≤d w' ↔ f w ≤ f w' := Iff.rfl

/-- The vector `v a = d•𝟙 - (n+1)•a` associated to a test vector `a` -/
def v (a : testvecs n d) : Fin n.succ → ℤ := fun i ↦ d - (n + 1) * (a.val i)

/-- The pairing of a weight vector with an integral vector -/
def pair' (w : Weight n d) (a : Fin n.succ → ℤ) : ℤ := ∑ j, a j * w j

lemma pair'_v (w : Weight n d) (a : testvecs n d) :
    pair' w (v a) = d * w.sum - (n + 1) * pair w a := by
  simp [v, pair, pair', Weight.sum, Finset.mul_sum, Finset.sum_sub_distrib, sub_mul, mul_assoc]

/-- `f w a` vanishes when `w` and `v a` pair to a negative value. -/
lemma f_apply_eq_zero_of_neg_pair'_v {w : Weight n d} {a : testvecs n d} (h : pair' w (v a) < 0) :
    f w a = 0 := by
  simp only [pair'_v, sub_neg] at h
  simp only [f_apply, E, tsub_eq_zero_iff_le]
  zify
  change ((Weight.sum w) * ↑d / (↑n + 1) : ℤ) < ↑(pair w ↑a)
  apply Int.ediv_lt_of_lt_mul (by linarith)
  simp only [mul_comm, h]

/-- When `w` and `v a` pair nonnegatively, then `f w a = ⌊(pair' w (v a))/(n+1)⌋ + 1`. -/
lemma f_apply_eq_pair'_v_of_nonneg {w : Weight n d} {a : testvecs n d} (h : 0 ≤ pair' w (v a)) :
    f w a = pair' w (v a) / (n + 1) + 1 := by
  simp only [pair'_v, sub_nonneg] at h
  have H : pair w a ≤ w.sum * d / (n + 1) + 1 := by
    zify
    refine Int.le_add_one (Int.le_ediv_of_mul_le (by linarith) ?_)
    simp only [mul_comm, h]
  simp only [f_apply, E, ge_iff_le, pair'_v]
  zify [H]
  rw [sub_eq_add_neg (_ * _), neg_mul_eq_mul_neg, Int.add_mul_ediv_left _ _ (by linarith)]
  ring_nf

/-- If the pairing of `w` with `v a` for any test vector `a` such that the `pair w (v a) ≥ 0`
is bounded above by the pairing of `w'` with `v a`, then `w` dominates `w'`.
Here, `v a = d•𝟙 - (n+1)•a`. (Lemma 3.14) -/
lemma dom_of_pair_le (w w' : Weight n d)
    (h : ∀ a : testvecs n d, 0 ≤ pair' w (v a) → pair' w (v a) ≤ pair' w' (v a)) :
    w ≤d w' := by
  rw [dom_iff, f_le_iff]
  intro a
  by_cases H : 0 ≤ pair' w (v a)
  · have h' := h a H
    have H' : 0 ≤ pair' w' (v a) := H.trans h'
    zify
    rw [f_apply_eq_pair'_v_of_nonneg H, f_apply_eq_pair'_v_of_nonneg H']
    simp only [add_le_add_iff_right]
    exact Int.ediv_le_ediv (by linarith) h'
  · push_neg at H
    rw [f_apply_eq_zero_of_neg_pair'_v H]
    exact Nat.zero_le _

/-- `w` and `w + k•𝟙` dominate each other. -/
lemma dom_dom_of_shift (w : Weight n d) (k : ℕ) :
    w ≤d w + k • (1 : Weight _ _) ∧ w + k • (1 : Weight _ _) ≤d w := by
  simp only [dom_iff, f_eq_on_shift, le_rfl, and_self]

lemma dom_perm (w w' : Weight n d) (σ : Equiv.Perm (Fin n.succ)) :
    w.comp σ ≤d w'.comp σ ↔ w ≤d w' := by
  simp [E_perm, pair_perm']
  refine ⟨fun h a ha ↦ ?_, fun h a ha ↦ h (a.comp σ⁻¹) (testvecs_perm ha σ⁻¹)⟩
  specialize h (a.comp σ) (testvecs_perm ha σ)
  rwa [comp_comp, mul_inv_cancel, Weight.comp, Equiv.Perm.coe_one, Function.comp_id] at h

/-- If `w` dominates `w'` and both have `0` as their first entry, then `E w ≤ E w'`. -/
lemma E_dom_mono [NeZero d] {w w' : Weight n d} (hw : w 0 = 0) (hw' : w' 0 = 0) (h : w ≤d w') :
    w.E ≤ w'.E := by
  simp only [dom_iff, f_le_iff] at h
  specialize h (tw n d 0)
  simp_rw [eval_f_tw, hw, hw'] at h
  simpa only [mul_zero, tsub_zero] using h

/-- If `w` and `w'` dominate each other and both have first entry zero, then `E w = E w'`.-/
lemma E_dom_eq [NeZero d] {w w' : Weight n d} (hw : w 0 = 0) (hw' : w' 0 = 0) (h₁ : w ≤d w') (h₂ : w' ≤d w) :
    w.E = w'.E :=
  le_antisymm (E_dom_mono hw hw' h₁) (E_dom_mono hw' hw h₂)

/-- Basic properties of the product order. -/
@[simp] lemma lec_iff (w w' : Weight n d) : w ≤c w' ↔ ∀ j, w j ≤ w' j := by rfl
 -- `:= rfl` does not work

lemma lec_antisymm {w w' : Weight n d} (h₁ : w ≤c w') (h₂ : w' ≤c w) : w = w' := by
  ext j
  exact le_antisymm ((lec_iff w w').mp h₁ j) ((lec_iff w' w).mp h₂ j)

lemma sum_le_sum_of_lec (w w' : Weight n d) (h : w ≤c w') : w.sum ≤ w'.sum :=
  Finset.sum_le_sum (fun j _ ↦ h j)

lemma pair_le_pair_of_lec (w w' a : Weight n d) (h : w ≤c w') : w.pair a ≤ w'.pair a :=
  Finset.sum_le_sum (fun j _ ↦ Nat.mul_le_mul_left _ (h j))

lemma E_lec_mono {w w' : Weight n d} (h : w ≤c w') : w.E ≤ w'.E := by
  simp only [E, add_le_add_iff_right]
  exact Nat.div_le_div_right (Nat.mul_le_mul_right _ <| sum_le_sum_of_lec w w' h)

/-!
### Normalized weights
-/

/-- `w` is *normalized* if `w 0 = 0` and `w` is increasing. -/
def normalized (w : Weight n d) : Prop := w 0 = 0 ∧ Monotone w

/-- If `w` is an increasing weight, then there is a normalized weight `w'` such that
`w` is obtained from `w'` by adding a constant map. -/
lemma normalized_of_Monotone {w : Weight n d} (hw : Monotone w) :
  ∃ (k : ℕ) (w' : Weight n d), w = w' + k • (1 : Weight _ _) ∧ w'.normalized := by
  have h : ∀ i, w 0 ≤ w i := fun _ ↦ hw bot_le
  refine ⟨w 0, fun i ↦ w i - w 0, ?_, ?_, fun i j hij ↦ ?_⟩
  · ext i
    simp only [add_apply, smul_apply, one_apply, mul_one, Nat.sub_add_cancel (h i)]
  · exact Nat.sub_self (w 0)
  · simpa only [tsub_le_iff_right, Nat.sub_add_cancel (h j)] using hw hij

/-- A weight `w` is minimal among increasing weights if and only if it is
minimal among normalized weights. -/
lemma min_Monotone_iff_min_normalized (w : Weight n d) :
    (∀ w' : Weight n d, Monotone w' → w' ≤d w → w ≤d w') ↔
      (∀ w' : Weight n d, w'.normalized → w' ≤d w → w ≤d w') := by
  refine ⟨fun h w' hw' hle ↦ h _ hw'.2 hle, fun h w' hw' hle ↦ ?_⟩
  obtain ⟨k, wr, hwr₁, hwr₂⟩ := normalized_of_Monotone hw'
  have h₁ := le_of_le_of_eq (dom_dom_of_shift wr k).1 hwr₁.symm
  exact (h wr hwr₂ (h₁.trans hle)).trans h₁

/-- `sorted w` is the increasing permutation of `w`. -/
def sorted (w : Weight n d) : Weight n d := w.comp (Tuple.sort w)

lemma sorted_is_Monotone (w : Weight n d) : Monotone w.sorted := Tuple.monotone_sort _

lemma normalized_of_sorted {w : Weight n d} (hw : w 0 = 0) : w.sorted.normalized := by
  have hm := sorted_is_Monotone w
  have h₁ : w.sorted ((Tuple.sort w)⁻¹ 0) = 0 := by
    rwa [sorted, Weight.comp, Function.comp_apply, Equiv.Perm.apply_inv_self]
  exact ⟨Nat.eq_zero_of_le_zero (le_of_le_of_eq (hm (Fin.zero_le _)) h₁), sorted_is_Monotone w⟩

end Weight
