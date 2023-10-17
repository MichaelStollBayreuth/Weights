import Mathlib.Data.Fin.Tuple.NatAntidiagonal
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.RingTheory.Int.Basic
import Mathlib.Data.Fin.Tuple.BubbleSortInduction
import Mathlib.Data.DFinsupp.WellFounded
import Mathlib.Tactic

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

The main result of this file is that there is a *unique* minimal complete set
of weights, which is given by the set `M n d` of all normalized weights that are minimal
elements with respect to domination within the set of all normalized weights.
See `Weight.M_is_minimal` and `Weight.M_is_unique`.

We show in addition that the entries of nonzero elements of `M n d` are coprime
(`Weight.gcd_eq_one_of_in_M`) and that `M n 1` consists of the single
element $(0,1,\ldots,1)$ (`Weight.w1_unique`).
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

variable {n d : ℕ} [NeZero d] -- fix dimension and (positive) degree

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
  done

@[simp] lemma comp_one (w : Weight n d) : w.comp 1 = w := rfl

@[simp] lemma comp_apply (w : Weight n d) (σ : Equiv.Perm (Fin n.succ)) (i : Fin n.succ) :
    (w.comp σ) i = w (σ i) := rfl

/-!
### Sum of a weight
-/

/-- The *sum* of a weight is the sum of its entries. -/
protected def sum (w : Weight n d) : ℕ := ∑ j, w j

@[simp] lemma sum_perm (w : Weight n d) (σ : Equiv.Perm (Fin n.succ)) : (w.comp σ).sum = w.sum := by
  simp only [Weight.sum, Function.comp_apply]
  exact Fintype.sum_bijective σ (Equiv.bijective σ) _ _ (fun i ↦ rfl)
  done

@[simp] lemma sum_smul (w : Weight n d) (k : ℕ) : (k • w).sum = k * w.sum := by
  simp only [Weight.sum, Finset.mul_sum]
  rfl
  done

lemma sum_add (w w' : Weight n d) : (w + w').sum = w.sum + w'.sum := by
  simp only [Weight.sum, add_apply, Finset.sum_add_distrib]
  done

/-!
### Pairing
-/

/-- The *pairing* of two weights is their scalar product. -/
def pair (w a : Weight n d) : ℕ := ∑ j, a j * w j

lemma mul_le_pair (w a : Weight n d) (k : Fin n.succ) : (a k) * (w k) ≤ w.pair a := by
  simp [pair]
  rw [Finset.sum_eq_add_sum_diff_singleton (Finset.mem_univ k)]
  exact Nat.le_add_right _ _
  done

lemma pair_add_left (w w' a : Weight n d) : (w + w').pair a = w.pair a + w'.pair a := by
  simp only [pair, add_apply, mul_add, Finset.sum_add_distrib]
  done

@[simp] lemma pair_smul_left (w a : Weight n d) (k : ℕ) : (k • w).pair a = k * w.pair a := by
  simp only [pair, smul_apply]
  conv =>
    lhs
    congr
    rfl
    intro x
    rw [mul_left_comm]
  exact Finset.mul_sum.symm
  done

/-- If `w` and `a` are both increasing or both decreasing on `{i, j}`, then swapping `a i` and `a j`
decreases `pair w a`. -/
lemma pair_swap_le {w a : Weight n d} {i j : Fin n.succ} (hw : w i ≤ w j) (ha : a i ≤ a j) :
    w.pair (a.comp $ Equiv.swap i j) ≤ w.pair a := by
  cases' eq_or_ne i j with h h
  · simp only [Weight.comp, h, Equiv.swap_self, Equiv.coe_refl, Function.comp.right_id, le_refl]
  · have haij : ∀ k ∈ (Finset.univ.erase j).erase i, (a.comp (Equiv.swap i j)) k = a k := by
      intros k hk
      rw [comp_apply,
          Equiv.swap_apply_of_ne_of_ne (Finset.ne_of_mem_erase hk)
                                       (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hk))]
      done
    have ht : ∀ k ∈ (Finset.univ.erase j).erase i, (a.comp (Equiv.swap i j)) k * w k = a k * w k :=
      fun k hk ↦ congr_arg (· * w k) <| haij k hk
    simp only [pair]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i),
        ← Finset.add_sum_erase _ _ (Finset.mem_univ j),
        ← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨h.symm, Finset.mem_univ _⟩), 
        ← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨h, Finset.mem_univ _⟩),
        Finset.erase_right_comm, Finset.sum_congr rfl ht, ← add_assoc, ← add_assoc]
    simp only [comp_apply, Equiv.swap_apply_left, Equiv.swap_apply_right, add_le_add_iff_right]
    rw [add_comm (a j * w i), add_comm (a j * w j)]
    exact mul_add_mul_le_mul_add_mul ha hw
    done

lemma pair_perm (w a : Weight n d) (σ : Equiv.Perm (Fin n.succ)) :
    pair (w.comp σ) (a.comp σ) = pair w a := by
  simp only [Weight.comp, pair, Function.comp_apply]
  exact Fintype.sum_bijective σ (Equiv.bijective _) _ _ (fun k ↦ rfl)
  done

lemma pair_perm' (w a : Weight n d) (σ : Equiv.Perm (Fin n.succ)) :
    pair (w.comp σ) a = pair w (a.comp σ⁻¹) := by
  rw [← pair_perm w _ σ]
  simp only [comp_comp, mul_left_inv, comp_one]
  done

lemma pair_swap_eq (w a : Weight n d) (i j : Fin n.succ) :
    pair w (a.comp $ Equiv.swap i j) = pair (w.comp $ Equiv.swap i j) a := by
  convert (pair_perm' w a _).symm
  simp only [Equiv.swap_inv]
  done

/-!
### Test vectors
-/

/-- We define the set of *test vectors* of dimension `n` and degree `d` to be the
set of weights whose sum is `d`. -/
def testvecs (n d : ℕ) [NeZero d] : Set (Weight n d) := {w | w.sum = d}

lemma pair_shift (a : testvecs n d) (k : ℕ) : (k • (1 : Weight n d)).pair a = k * d := by
  simp only [pair, smul_apply, one_apply, mul_one]
  rw [mul_comm k, ← Finset.sum_mul]
  congr 1
  exact a.2
  done

-- Maybe better use the Finset right away?
lemma tv_finset : ((Finset.Nat.antidiagonalTuple n.succ d) :
    Set (Fin n.succ → ℕ)) = testvecs n d := by
  simp only [testvecs]
  ext a
  simp only [Finset.Nat.mem_antidiagonalTuple, Finset.mem_coe, Finset.mem_mk, Weight.sum]
  rfl
  done

/-- The set of test vectors is closed under permutation. -/
lemma testvecs_perm {a : Weight n d} (ha : a ∈ testvecs n d) (σ : Equiv.Perm (Fin n.succ)) :
    a.comp σ ∈ testvecs n d := by simpa only [testvecs, sum_perm, Set.mem_setOf_eq]

/-- The test vector `(d-1,0,...,1,...,0)` (`1` in position `k`),
for `k = 0`, this is `(d,0,...,0)`. -/
-- first define it as a weight...
def tw' (n d : ℕ) [NeZero d] (k : Fin n.succ) : Weight n d :=
  (d - 1) • (Function.update (0 : Weight n d) 0 1) + Function.update (0 : Weight n d) k 1

-- then prove it has sum `d`.
lemma tw'_sum (n d : ℕ) [NeZero d] (k : Fin n.succ) : (tw' n d k).sum = d := by
  simp only [Weight.sum, tw', ge_iff_le, nsmul_eq_mul, Pi.coe_nat, Nat.cast_tsub, Nat.cast_id,
    Nat.cast_one, Pi.add_apply, Pi.mul_apply, ne_eq, Function.update_apply, zero_apply, mul_ite,
    mul_one, mul_zero, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  exact Nat.sub_add_cancel (Nat.one_le_of_lt (NeZero.pos d))
  done

-- Now we can define it as an element of `testvecs n d`.
def tw (n d : ℕ) [NeZero d] (k : Fin n.succ) : testvecs n d := ⟨tw' n d k, tw'_sum n d k⟩

/-- The test vectors given by `tw n d` are pairwise distinct. -/
lemma tw_inj (n d : ℕ) [NeZero d] : Function.Injective (tw n d) := by
  intro j k h
  simp only [tw, tw', ge_iff_le, nsmul_eq_mul, Pi.coe_nat, Nat.cast_tsub, Nat.cast_id,
    Nat.cast_one, Subtype.mk.injEq] at h 
  replace h := congr_fun h k
  simp only [ge_iff_le, Pi.add_apply, Pi.mul_apply, ne_eq, Function.update_apply, zero_apply,
    mul_ite, mul_one, mul_zero, Function.update_same, add_right_inj, ite_eq_left_iff, if_true] at h
  exact (of_not_not h).symm
  done

lemma pair_tw (w : Weight n d) (k : Fin n.succ) :
    w.pair (tw n d k) = (d - 1) * (w 0) + (w k) := by
  simp only [pair, tw, tw', ge_iff_le, nsmul_eq_mul, Pi.coe_nat, Nat.cast_tsub, Nat.cast_id,
    Nat.cast_one, Pi.add_apply, Pi.mul_apply, ne_eq, Function.update_apply, zero_apply, mul_ite,
    mul_one, mul_zero, add_mul, ite_mul, zero_mul, one_mul, Finset.sum_add_distrib,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  done

/-!
### The exponent of a weight
-/

/-- The *exponent* `E w` of a weight is `w.sum * d / (n + 1) + 1`.
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
  done

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

lemma eval_f_tw (w : Weight n d) (k : Fin n.succ) :
    f w (tw n d k) = w.E - (d - 1) * (w 0) - (w k) := by
  simp only [f, pair, ge_iff_le, tsub_le_iff_right, Nat.sub_sub]
  congr 1
  exact pair_tw w k
  done

lemma f_eq_on_shift (w : Weight n d) (k : ℕ) : (w + k • (1 : Weight n d)).f = w.f := by
  ext a
  simp only [f_apply, E_shift, pair_add_left, pair_shift, add_tsub_add_eq_tsub_right]
  done

/-- The map associated to `w` is pointwise below that associated to a positive multiple of `w`. -/
lemma f_le_mul (w : Weight n d) (k : ℕ) : w.f ≤ (k.succ • w).f := by
  simp only [E, f_le_iff, f_apply, sum_smul, pair_smul_left, SetCoe.forall, Subtype.coe_mk]
  intro a ?_
  have H : w.sum * d / (n + 1) + 1 - w.pair a
             ≤ k.succ * (w.sum * d / (n + 1)) + 1 - k.succ * w.pair a
  · set m := w.sum * d / (n + 1)
    set l := w.pair a
    cases' lt_or_le m l with hlt hle
    · rw [Nat.sub_eq_zero_of_le hlt]
      exact Nat.zero_le _
      done
    · rw [← tsub_add_eq_add_tsub hle, ← tsub_add_eq_add_tsub (mul_le_mul' le_rfl hle)]
      apply add_le_add_right
      rw [← Nat.mul_sub_left_distrib]
      exact Nat.le_mul_of_pos_left (Nat.succ_pos k)
      done
  calc w.sum * d / (n + 1) + 1 - w.pair a
    _ ≤ k.succ * (w.sum * d / (n + 1)) + 1 - k.succ * w.pair a := H
    _ ≤ k.succ * w.sum * d / (n + 1) + 1 - k.succ * w.pair a := by
      apply Nat.sub_le_sub_right
      apply add_le_add_right
      rw [mul_assoc]
      apply Nat.mul_div_le_mul_div_assoc
      done

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
  done

lemma codom_f_well_founded : WellFoundedLT (testvecs n d → ℕ) := inferInstance

instance well_founded : IsWellFounded (Weight n d) (· < ·) := ⟨InvImage.wf f codom_f_well_founded.1⟩

-- Introduce notation `≤d` for domination and `≤c` for the product order
infix:50 " ≤d " => @LE.le (Weight _ _) _
infix:50 " ≤c " => @LE.le (Fin _ → ℕ) _

@[simp] lemma dom_iff (w w' : Weight n d) : w ≤d w' ↔ f w ≤ f w' := Iff.rfl

/-- The vector `v a = d•𝟙 - (n+1)•a` associated to a test vector `a` -/
def v (a : testvecs n d) : Fin n.succ → ℤ := fun i ↦ d - (n + 1) * (a.val i)

/-- The pairing of a weight vector with an integral vector -/
def pair' (w : Weight n d) (a : Fin n.succ → ℤ) : ℤ := ∑ j, a j * w j

lemma pair'_v (w : Weight n d) (a : testvecs n d) :
    pair' w (v a) = d * w.sum - (n + 1) * pair w a := by
  simp [v, pair, pair', Weight.sum, Finset.mul_sum, Finset.sum_sub_distrib, sub_mul, mul_assoc]
  done

/-- `f w a` vanishes when `w` and `v a` pair to a negative value. -/
lemma f_apply_eq_zero_of_neg_pair'_v {w : Weight n d} {a : testvecs n d} (h : pair' w (v a) < 0) :
    f w a = 0 := by
  simp only [pair'_v, sub_neg] at h 
  simp only [f_apply, E, tsub_eq_zero_iff_le]
  zify
  change ((Weight.sum w) * ↑d / (↑n + 1) : ℤ) < ↑(pair w ↑a)
  apply Int.ediv_lt_of_lt_mul (by linarith)
  simp only [mul_comm, h]
  done

/-- When `w` and `v a` pair nonnegatively, then `f w a = ⌊(pair' w (v a))/(n+1)⌋ + 1`. -/
lemma f_apply_eq_pair'_v_of_nonneg {w : Weight n d} {a : testvecs n d} (h : 0 ≤ pair' w (v a)) :
    f w a = pair' w (v a) / (n + 1) + 1 := by
  simp only [pair'_v, sub_nonneg] at h
  have H : pair w a ≤ w.sum * d / (n + 1) + 1
  · zify
    refine Int.le_add_one (Int.le_ediv_of_mul_le (by linarith) ?_)
    simp only [mul_comm, h]
  simp [f_apply, E, pair'_v]
  zify [H]
  rw [sub_eq_add_neg (_ * _), neg_mul_eq_mul_neg, Int.add_mul_ediv_left _ _ (by linarith)]
  ring_nf
  done

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
    done
  · push_neg at H
    rw [f_apply_eq_zero_of_neg_pair'_v H]
    exact Nat.zero_le _
    done

lemma dom_dom_of_shift (w : Weight n d) (k : ℕ) :
    w ≤d w + k • (1 : Weight _ _) ∧ w + k • (1 : Weight _ _) ≤d w := by
  simp only [dom_iff, f_eq_on_shift, le_rfl, and_self]

lemma dom_perm (w w' : Weight n d) (σ : Equiv.Perm (Fin n.succ)) :
    w.comp σ ≤d w'.comp σ ↔ w ≤d w' := by
  simp [E_perm, pair_perm']
  refine ⟨fun h a ha ↦ ?_, fun h a ha ↦ h (a.comp σ⁻¹) (testvecs_perm ha σ⁻¹)⟩
  specialize h (a.comp σ) (testvecs_perm ha σ)
  rwa [comp_comp, mul_right_inv, Weight.comp, Equiv.Perm.coe_one, Function.comp.right_id] at h
  done

/-- If `w` dominates `w'` and both have `0` as their first entry, then `E w ≤ E w'`. -/
lemma E_dom_mono {w w' : Weight n d} (hw : w 0 = 0) (hw' : w' 0 = 0) (h : w ≤d w') :
    w.E ≤ w'.E := by
  simp only [dom_iff, f_le_iff] at h
  specialize h (tw n d 0)
  simp_rw [eval_f_tw, hw, hw'] at h
  simpa only [ge_iff_le, mul_zero, nonpos_iff_eq_zero, tsub_zero] using h
  done

/-- If `w` and `w'` dominate each other and both have first entry zero, then `E w = E w'`.-/
lemma E_dom_eq {w w' : Weight n d} (hw : w 0 = 0) (hw' : w' 0 = 0) (h₁ : w ≤d w') (h₂ : w' ≤d w) :
    w.E = w'.E :=
  le_antisymm (E_dom_mono hw hw' h₁) (E_dom_mono hw' hw h₂)

/-- Basic properties of the product order. -/
@[simp] lemma lec_iff (w w' : Weight n d) : w ≤c w' ↔ ∀ j, w j ≤ w' j := by rfl
 -- `:= rfl` does not work

lemma lec_antisymm {w w' : Weight n d} (h₁ : w ≤c w') (h₂ : w' ≤c w) : w = w' := by
  ext j
  exact le_antisymm ((lec_iff w w').mp h₁ j) ((lec_iff w' w).mp h₂ j)
  done

lemma sum_le_sum_of_lec (w w' : Weight n d) (h : w ≤c w') : w.sum ≤ w'.sum :=
  Finset.sum_le_sum (fun j _ ↦ h j)

lemma pair_le_pair_of_lec (w w' a : Weight n d) (h : w ≤c w') : w.pair a ≤ w'.pair a :=
  Finset.sum_le_sum (fun j _ ↦ Nat.mul_le_mul_left _ (h j))

lemma E_lec_mono {w w' : Weight n d} (h : w ≤c w') : w.E ≤ w'.E := by
  simp only [E, add_le_add_iff_right]
  refine Nat.div_le_div_right (Nat.mul_le_mul_right _ <| sum_le_sum_of_lec w w' h)
  done

/-!
### Normalized weights
-/

/-- `w` is *normalized* if `w 0 = 0` and `w` is increasing. -/
def normalized (w : Weight n d) : Prop := w 0 = 0 ∧ Monotone w

/-- If `w` is an increasing weight, then there is a normalized weight `w'` such that
`w` is obtained from `w'` by adding a constant map. -/
lemma normalized_of_Monotone {w : Weight n d} (hw : Monotone w) :
  ∃ (k : ℕ) (w' : Weight n d), w = w' + k • (1 : Weight _ _) ∧ w'.normalized := by
  have h : ∀ i, w 0 ≤ w i := fun i ↦ hw bot_le
  refine ⟨w 0, fun i ↦ w i - w 0, ?_, ?_, fun i j hij ↦ ?_⟩
  · ext i
    simp [Nat.sub_add_cancel (h i)]
    done
  · simp only [tsub_self]
    done
  · simp [Nat.sub_add_cancel (h j)]
    exact hw hij
    done

/-- A weight `w` is minimal among increasing weights if and only if it is
minimal among normalized weights. -/
lemma min_Monotone_iff_min_normalized (w : Weight n d) :
    (∀ w' : Weight n d, Monotone w' → w' ≤d w → w ≤d w') ↔
      (∀ w' : Weight n d, w'.normalized → w' ≤d w → w ≤d w') := by
  refine ⟨fun h w' hw' hle ↦ h _ hw'.2 hle, fun h w' hw' hle ↦ ?_⟩
  obtain ⟨k, wr, hwr₁, hwr₂⟩ := normalized_of_Monotone hw'
  have h₁ := le_of_le_of_eq (dom_dom_of_shift wr k).1 hwr₁.symm
  exact (h wr hwr₂ (h₁.trans hle)).trans h₁
  done

/-- `sorted w` is the increasing permutation of `w`. -/
def sorted (w : Weight n d) : Weight n d := w.comp (Tuple.sort w)

lemma sorted_is_Monotone (w : Weight n d) : Monotone w.sorted := Tuple.monotone_sort _

lemma normalized_of_sorted {w : Weight n d} (hw : w 0 = 0) : w.sorted.normalized := by
  have hm := sorted_is_Monotone w
  have h₁ : w.sorted ((Tuple.sort w)⁻¹ 0) = 0
  · rwa [sorted, Weight.comp, Function.comp_apply, Equiv.Perm.apply_inv_self]
    done
  exact ⟨Nat.eq_zero_of_le_zero (le_of_le_of_eq (hm (Fin.zero_le _)) h₁), sorted_is_Monotone w⟩
  done

/-!
### The truncation of a weight
-/

/-- We define `trunc w` such that `trunc w j = min j (E w)`. -/
def trunc (w : Weight n d) : Weight n d := fun j ↦ min (w j) w.E

@[simp] lemma trunc_apply (w : Weight n d) (k : Fin n.succ) : w.trunc k = min (w k) w.E := rfl

lemma trunc_mono_lec {w w' : Weight n d} (h : w ≤c w') : w.trunc ≤c w'.trunc := by
  simp only [lec_iff, trunc_apply]
  exact fun j ↦ min_le_min (h j) (E_lec_mono h)
  done

lemma trunc_lec (w : Weight n d) : w.trunc ≤c w := by
  simp_rw [trunc, lec_iff]
  exact (fun j ↦ min_le_left _ _)
  done

lemma trunc_le_E (w : Weight n d) (j : Fin n.succ) : w.trunc j ≤ w.E := by
  simp only [trunc, min_le_iff, le_refl, or_true]
  done

lemma trunc_zero {w : Weight n d} (h : w 0 = 0) : w.trunc 0 = 0 := by
  simp only [trunc_apply, Nat.min_eq_zero_iff] at h ⊢
  exact Or.inl h
  done

lemma trunc_Monotone {w : Weight n d} (h : Monotone w) : Monotone w.trunc := by
  intro i j hij
  simp only [trunc_apply, min_le_iff, le_min_iff, le_refl, and_true, or_true]
  exact Or.inl (h hij)
  done

lemma trunc_normalized {w : Weight n d} (h : w.normalized) : w.trunc.normalized :=
  ⟨trunc_zero h.1, trunc_Monotone h.2⟩

lemma trunc_pair_lb (w a : Weight n d) (h : ∃ j, w.E < w j ∧ 0 < a j) : w.E ≤ w.trunc.pair a := by
  obtain ⟨j, hj, ha⟩ := h
  have hm := mul_le_pair w.trunc a j
  simp only [trunc_apply] at hm
  rw [min_eq_right_of_lt hj] at hm
  exact (Nat.le_mul_of_pos_left ha).trans hm
  done

lemma trunc_pair_le_pair (w a : Weight n d) : w.trunc.pair a ≤ w.pair a :=
  pair_le_pair_of_lec w.trunc w a (trunc_lec w)

lemma E_trunc_le_E (w : Weight n d) : w.trunc.E ≤ w.E :=
  E_lec_mono (trunc_lec w)

/-- `w` and `trunc w` give the same pairing with `a` if for each `j`, either `w j ≤ E w`
or `a j ≤ 0`. -/
lemma trunc_pair_eq_pair (w a : Weight n d) (h : ∀ j, w.E < w j → a j ≤ 0) :
    w.trunc.pair a = w.pair a := by
  simp only [pair, trunc_apply]
  congr
  ext j
  specialize h j
  simp only [mul_eq_mul_left_iff, min_eq_left_iff]
  by_cases h' : w j ≤ w.E
  · exact Or.inl h'
    done
  · simp only [not_le] at h'
    exact Or.inr <| Nat.eq_zero_of_le_zero (h h')
    done

/-- `trunc w` dominates `w`. -/
lemma trunc_dom (w : Weight n d) : w.trunc ≤d w := by
  rw [dom_iff, f_le_iff]
  intro a
  simp_rw [f]
  refine (Nat.sub_le_sub_right (E_trunc_le_E w) _).trans ?_
  by_cases h : ∃ j, w.E < w j ∧ 0 < a.1 j
  · rw [Nat.sub_eq_zero_of_le (trunc_pair_lb w a h)]
    exact Nat.zero_le _
    done
  · push_neg at h
    rw [trunc_pair_eq_pair w a h]
    done

/-- `w` dominates `trunc w` (and so they dominate each other) when `E (trunc w) = E w`. -/
lemma trunc_dom' {w : Weight n d} (hE : w.trunc.E = w.E) : w ≤d w.trunc := by
  rw [dom_iff, f_le_iff]
  intro a
  simp_rw [f, ← hE]
  exact Nat.sub_le_sub_left _ (trunc_pair_le_pair w a)
  done

/-- The converse: if `w` dominates `trunc w`, then `E (trunc w) = E w`. -/
lemma E_trunc_eq_E_of_dom {w : Weight n d} (h : w ≤d w.trunc) (h' : w 0 = 0) : w.trunc.E = w.E :=
  E_dom_eq (trunc_zero h') h' (trunc_dom _) h

/-!
### Balanced weights
-/

/-- We define `w` to be *balanced* if `w j ≤ E w` for all `j`. -/
def balanced (w : Weight n d) : Prop := ∀ j, w j ≤ E w

lemma balanced_iff_eq_trunc (w : Weight n d) : w.balanced ↔ w.trunc = w := by
  simp_rw [balanced, trunc]
  constructor <;> intro h
  · ext j
    exact min_eq_left_iff.mpr (h j)
    done
  · exact fun j ↦ min_eq_left_iff.mp (congr_fun h j)
    done

lemma balanced_iff_lec_E (w : Weight n d) : w.balanced ↔ w ≤c (w.E : Fin n.succ → ℕ) := by rfl

/-- If `trunc w` has the same exponent as `w`, then `trunc w` is balanced. -/
lemma trunc_balanced {w : Weight n d} (hE : w.trunc.E = w.E) : w.trunc.balanced := by
  rw [balanced_iff_lec_E, hE, lec_iff]
  exact trunc_le_E w
  done

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
  exact fun a _ ↦ Nat.sub_le_sub_left _ (pair_le_pair_of_lec _ _ _ h)
  done

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
  done

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
      done
    · exact Nat.div_le_div_right (Nat.mul_le_mul_right _ (Nat.le_succ _))
      done
  refine ⟨hE', fun j ↦ ?_, (lec_iff _ _).mpr (fun j ↦ ?_), fun hf ↦ ?_⟩
  · -- show `balanced w'`
    simp only [ne_eq, Function.update_apply, trunc_apply, ge_iff_le, hE']
    split_ifs with hj
    · exact one_le_E _
      done
    · exact trunc_balanced hE _
      done
  · -- show `w.trunc ≤c w'`
    simp only [Function.update_apply]
    by_cases hjk : j = k <;>
      simp only [hjk, (Nat.eq_zero_of_le_zero (le_of_le_of_eq (trunc_lec w k) hk)),
        zero_le', if_false]
    · exact Nat.le_refl (trunc w j)
      done
  · -- show `w.trunc ≠ w'`.
    rw [hf, self_eq_add_right] at hsum'
    exact Nat.one_ne_zero hsum'
    done

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
    done
  refine ⟨m, hm, fun i j hij ↦ ?_⟩
  simp only [Function.update_apply]
  by_cases hi : i = m <;> by_cases hj : j = m <;> simp [hi, hj]
  · have hij' : m < j
    · rw [← hi]
      refine lt_of_le_of_ne hij ?_
      rw [hi]
      exact Ne.symm hj
      done
    have := Nat.findGreatest_is_greatest hij' (Nat.le_of_lt_succ j.2)
    simp only [Fin.is_lt, Fin.eta, dite_eq_ite, ite_true, ← Ne.def] at this 
    exact Nat.one_le_iff_ne_zero.mpr this
    done
  · exact (le_of_le_of_eq (hw.2 (le_of_le_of_eq hij hj)) hm).trans zero_le_one
    done
  · exact hw.2 hij
    done

/-- If `w` has first entry `0` and is minimal w.r.t. `≤d`, then `w` is balanced. -/
lemma balanced_of_min {w : Weight n d} (hw : w 0 = 0) (hmin : ∀ u, u ≤d w → w ≤d u) :
    w.balanced := by
  by_contra hb
  obtain ⟨hE', hb', hc, hne⟩ :=
    exists_balanced_ltc w hb (E_trunc_eq_E_of_dom (hmin _ (trunc_dom w)) hw) hw
  -- We use that `≤d` is equivalent to `≥c` under suitable assumptions.
  exact hne (lec_antisymm hc <| (dom_iff_gec_of_balanced (trunc_zero hw) hb' hE'.symm).mp <|
              (trunc_dom w).trans <| hmin _  <| (dom_of_gec hE' hc).trans $ trunc_dom w)
  done

/-- If `w` is normalized and minimal w.r.t. `≤d` on monotone weights, then `w` is balanced. -/
lemma balanced_of_min' {w : Weight n d} (hw : w.normalized)
  (hmin : ∀ u : Weight n d, (Monotone u) → u ≤d w → w ≤d u) :
    w.balanced := by
  obtain ⟨k, hk₁, hk₂⟩ := index_exists hw
  by_contra hb
  obtain ⟨hE', hb', hc, hne⟩ := 
    exists_balanced_ltc w hb
      (E_trunc_eq_E_of_dom (hmin _ (trunc_normalized hw).2 (trunc_dom w)) hw.1) hk₁
  -- We use that `≤d` is equivalent to `≥c` under suitable assumptions.
  refine hne (lec_antisymm hc <| (dom_iff_gec_of_balanced (trunc_normalized hw).1 hb' hE'.symm).mp <|
              (trunc_dom w).trans <| hmin _ ?_ <| (dom_of_gec hE' hc).trans (trunc_dom w))
  intro i j hij
  simp only [Function.update_apply, trunc_apply]
  cases' eq_or_ne i k with hi hi <;> cases' eq_or_ne j k with hj hj <;> simp [hi, hj]
  · refine ⟨?_, one_le_E w⟩
    have : w j = Function.update w k 1 j := by simp only [Function.update_apply, hj, if_false]
    rw [(Function.update_same k 1 w).symm, this]
    exact hk₂ (le_of_eq_of_le hi.symm hij)
    done
  · exact Or.inl ((le_of_le_of_eq (hw.2 (le_of_le_of_eq hij hj)) hk₁).trans zero_le_one)
    done
  · cases' le_or_lt w.E (w j) with h h
    · exact Or.inr h
      done
    · exact Or.inl (hw.2 hij)
      done

/-- If two weights with first entry `0` dominate each other and are minimal w.r.t. `≤d`,
then they are equal. -/
lemma eq_of_dom_and_min {w w' : Weight n d} (hw : w 0 = 0) (hw' : w' 0 = 0)
  (h : w' ≤d w) (hmin : ∀ u, u ≤d w → w ≤d u) :
    w = w' := by
  have h₁ := hmin _ h                   -- `w ≤d w'`
  have hmin' := fun u (hu : u ≤d w') ↦ h.trans (hmin u (hu.trans h)) -- `w'` is minimal
  have hb := balanced_of_min hw hmin    -- `w` is balanced
  have hb' := balanced_of_min hw' hmin' -- `w'` is balanced
  have hE := E_dom_eq hw hw' h₁ h       -- `E w = E w'`
  exact lec_antisymm
    ((dom_iff_gec_of_balanced hw' hb hE.symm).mp h) ((dom_iff_gec_of_balanced hw hb' hE).mp h₁)
  done

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
  done

/-!
### Domination and permutations
-/

/-- If a monotone weight `w` dominates another weight `w'`, then `w` dominates `w'` made monotone
by sorting. -/
lemma dom_of_dom_perm {w w' : Weight n d} (hw : Monotone w) (hd : w ≤d w') : w ≤d w'.sorted := by
  refine Tuple.bubble_sort_induction hd (fun g i j hij₁ hij₂ hwg ↦ ?_)
  change Weight n d at g
  change w ≤d g at hwg
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
    done
  intro a ha
  rw [E_perm g (Equiv.swap i j)]
  cases' le_or_lt (a i) (a j) with ham ham
  · rw [tsub_le_iff_right]
    specialize hwg (a.comp (Equiv.swap i j)) (testvecs_perm ha _)
    rw [pair_swap_eq g, tsub_le_iff_right] at hwg
    refine hwg.trans ?_; clear hwg
    rw [add_le_add_iff_left]
    exact pair_swap_le (hw (le_of_lt hij₁)) ham
    done
  · let a' := a.comp (Equiv.swap i j)
    have haa' : a'.comp (Equiv.swap i j) = a
    · ext
      simp only [Weight.comp, Function.comp_apply, Equiv.swap_apply_self]
      done
    have ham' : a' i ≤ a' j
    · simp only [Weight.comp, Function.comp_apply, Equiv.swap_apply_left, Equiv.swap_apply_right]
      exact le_of_lt ham
      done
    have hag : g'.pair a' = pair g a := by simp only [pair_swap_eq g' a, hgg']
    have := pair_swap_le (n := n) (d := d) hgs ham'
    simp only [haa', hag] at this
    exact (hwg a ha).trans (Nat.sub_le_sub_left _ this)
    done

lemma dom_of_dom_perm' {w w' : Weight n d} (hw' : Monotone w') (hd : w ≤d w') :
    w.sorted ≤d w' := by
  convert dom_of_dom_perm (sorted_is_Monotone w) ((dom_perm w w' (Tuple.sort w)).mpr hd)
  rw [sorted, comp_comp]
  have help : w' = w'.comp (Tuple.sort w') ↔ Monotone w'
  · change w' ∘ Equiv.refl _ = _ ↔ Monotone (w' ∘ Equiv.refl _)
    exact Tuple.comp_sort_eq_comp_iff_monotone
    done
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
    done
  rwa [← h]
  done

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
    exact ⟨w', hw'₁, (hw'₂.trans $ le_of_lt hw₂)⟩
    done
  · push_neg at hw₁
    refine ⟨w₁, ⟨hw₁n, fun w' hw' h' ↦ ?_⟩, le_refl w₁⟩
    by_contra hf
    have := hw₁ w' hw'
    rw [lt_iff_le_not_le] at this
    push_neg at this
    exact hf (this h')
    done

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
    done
  · obtain ⟨hw₁, hw₂⟩ := h
    obtain ⟨w', hw'₁, hw'₂⟩ := hS₂.1 w hw₁
    suffices heq : w' = w
    · exact heq ▸ hw'₁
      done
    exact eq_of_dom_and_min' (hS₁ w' hw'₁) hw₁ (hw₂ w' (hS₁ w' hw'₁) hw'₂)
                             (fun u hu₁ hu₂ ↦ hw'₂.trans (hw₂ u hu₁ (hu₂.trans hw'₂)))
    done

lemma not_in_M_of_dom_ne {w : Weight n d}
  (hw : ∃ w' : Weight n d, w'.normalized ∧ w' ≤d w ∧ w' ≠ w) :
    w ∉ M n d := by
  obtain ⟨w', hw'₁, hw'₂, hw'₃⟩ := hw
  by_contra' hf
  exact hw'₃ (eq_of_dom_in_M hw'₁ hw'₂ hf)
  done

/-- Non-zero elements of `M n d` have coprime entries. -/
lemma gcd_eq_one_of_in_M {w : Weight n d} (h₀ : w ≠ 0) (hM : w ∈ M n d) :
    Finset.univ.gcd w = 1 := by
  set g := Finset.univ.gcd w
  by_contra hfg
  have hg : 1 < g
  · refine lt_of_le_of_ne (Nat.one_le_iff_ne_zero.mpr ?_) (Ne.symm hfg)
    by_contra' hg
    have h₀' : w = 0
    · ext i
      simp only [Finset.mem_univ, Finset.gcd_eq_zero_iff.mp hg, zero_apply]
      done
    exact h₀ h₀'
    done
  let w' : Weight n d := fun i ↦ (w i) / g
  have hww' : w = g • w'
  · ext i
    simp only [Pi.smul_apply, Algebra.id.smul_eq_mul]
    exact (Nat.mul_div_cancel_left' (Finset.gcd_dvd (Finset.mem_univ i))).symm
    done
  have hww'i : ∀ i, w i = g * w' i
  · intro i
    rw [hww']
    simp only [smul_apply]
    done
  refine (not_in_M_of_dom_ne ⟨w', ⟨?_, ?_⟩, ?_, ?_⟩) hM
  · simp only
    rw [hM.1.1, Nat.zero_div]
    done
  · simp only
    intro i j hij
    exact Nat.div_le_div_right (hM.1.2 hij)
    done
  · rw [hww', dom_iff]
    have := f_le_mul w' g.pred
    rwa [Nat.succ_pred_eq_of_pos (zero_lt_one.trans hg)] at this
    done
  · have hnz : ∃ i, w i ≠ 0 := by by_contra' hf; exact h₀ (funext hf)
    obtain ⟨i, hi⟩ := hnz
    have hi' : w' i ≠ 0
    · intro hf
      have := hww'i i
      rw [hf, mul_zero] at this
      exact hi this
      done
    intro hf
    rw [hww'] at hf
    have h₁ := congr_fun hf i
    rw [smul_apply] at h₁
    exact hfg (mul_right_cancel₀ hi' ((one_mul _).trans h₁)).symm
    done

/-!
### The case `d = 1`

We show that for `n ≥ 1`, the unique minimal weight with first entry `0` is `(0, 1, ..., 1)`.
-/

/-- When `d = 1`, the `testvecs` are just the standard basis vectors. -/
lemma testvecs1 (n : ℕ) : Function.Bijective (tw n 1) := by
  refine ⟨tw_inj n 1, ?_⟩
  intro a
  have h₂ : ∑ k, a.val k = 1 := a.2
  simp [tw, tw']
  have h : ∃ j, a.val j = 1
  · have h₁ : ∃ j, 0 < a.val j
    · by_contra' hf
      simp only [(fun k ↦ Nat.eq_zero_of_le_zero (hf k)), Finset.sum_const_zero,
                   Nat.zero_ne_one] at h₂
      done
    obtain ⟨j, hj⟩ := h₁
    use j
    suffices h₃ : a.val j ≤ 1
    · linarith
      done
    conv_rhs => rw [← h₂]
    exact Finset.single_le_sum (fun k _ ↦ Nat.zero_le (a.val k)) (Finset.mem_univ j)
    done
  obtain ⟨j, hj⟩ := h
  use j
  have h' : ∀ k, k ≠ j → a.val k = 0
  · intro k hk
    let s : Finset (Fin n.succ) := (Finset.univ \ {j})
    have hs : insert j s = Finset.univ
    · simp [Finset.insert_eq]
      done
    have hjs : ¬j ∈ s := by simp
    rw [← hs, Finset.sum_insert hjs, hj] at h₂
    simp only [Finset.mem_univ, not_true, add_right_eq_self, Finset.sum_eq_zero_iff,
      Finset.mem_sdiff, Finset.mem_singleton, true_and] at h₂ 
    exact h₂ k hk
    done
  ext k
  simp [Function.update_apply]
  split_ifs with hjk
  · rw [hjk]
    exact hj.symm
    done
  · exact (h' k hjk).symm
    done

/-- Define `w1 = (0, 1, ..., 1)`. -/
def w1 (n : ℕ) [NeZero n] : Weight n 1 := fun j ↦ if j = 0 then 0 else 1

lemma w1_apply (n : ℕ) [NeZero n] (j : Fin n.succ) : w1 n j = if j = 0 then 0 else 1 := rfl

lemma w1_zero (n : ℕ) [NeZero n] : w1 n 0 = 0 := by simp only [w1, eq_self_iff_true, if_true]

lemma sum_w1 (n : ℕ) [NeZero n] : (w1 n).sum = n := by
  simp [w1, Weight.sum, Finset.sum_ite, Finset.filter_ne']
  done
-- use `Finset.sum_boole`? would require rewriting with `ite_not` first

lemma E_w1 (n : ℕ) [NeZero n] : (w1 n).E = 1 := by
  rw [E, sum_w1]
  simp [Nat.div_eq_zero_iff]
  done

lemma w1_balanced (n : ℕ) [NeZero n] : (w1 n).balanced := by
  simp only [balanced]
  intro j
  rw [E_w1, w1]
  split_ifs with h
  · exact Nat.zero_le _
    done
  · exact le_rfl
    done

lemma pair_w1 {n : ℕ} [NeZero n] [DecidableEq (testvecs n 1)] (a : testvecs n 1) :
    (w1 n).pair a = if a = (tw n 1 0) then 0 else 1 := by
  obtain ⟨k, ha⟩ := (testvecs1 n).2 a
  rw [ha.symm, pair_tw, Nat.sub_self, zero_mul, zero_add, w1_apply]
  by_cases hk : k = 0
  · simp only [hk, eq_self_iff_true]
    done
  · simp only [hk, if_false]
    split_ifs with h'
    · have t := hk (tw_inj n 1 h')
      tauto
      done
    · rfl
      done

/-- `w1` is the minimal weight with first entry `0` w.r.t. dominance when `d = 1`. -/
lemma w1_minimal {n : ℕ} [NeZero n] {w : Weight n 1} (hw : w 0 = 0) : (w1 n) ≤d w := by
  simp only [dom_iff, f_le_iff, f_apply, Subtype.coe_mk]
  intro a
  classical
  simp only [E_w1, ge_iff_le, tsub_le_iff_right, pair_w1]
  split_ifs with h
  · rw [← f, h, eval_f_tw, hw]
    simp only [mul_zero, tsub_zero, add_zero]
    exact one_le_E w
    done
  · simp only [le_add_iff_nonneg_left, zero_le']
    done

/-- If `w` is minimal w.r.t. dominance for `d = 1` and has first entry `0`, then `w = w1`. -/
lemma w1_unique {n : ℕ} [NeZero n] {w : Weight n 1} (hw : w 0 = 0) 
  (hmin : ∀ w', w' ≤d w → w ≤d w') :
    w = w1 n := by
  have h₁ := w1_minimal hw
  have h₂ := hmin _ h₁
  have hE : w.E = 1
  · conv_rhs => rw [← E_w1 n]
    exact E_dom_eq hw (w1_zero n) h₂ h₁
    done
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
  done

/-!
### Dimension 2

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
def mem_S_le (d a b : ℕ) : Prop :=
  0 < b ∧
  ∃ (i₁ i₂ : ℕ), 3 * i₁ + 3 * i₂ ≤ 2 * d ∧ d < 3 * i₂ ∧
                 a * (3 * i₂ - d) = b * (2 * d - 3 * i₁ - 3 * i₂)

/-- The fraction `a/b` is an element of `S_≥`. -/
def mem_S_ge (d a b : ℕ) : Prop :=
  0 < a ∧
  ∃ (i₁ i₂ : ℕ), i₁ + i₂ ≤ d ∧ 2 * d < 3 * i₁ + 3 * i₂ ∧ 3 * i₂ ≤ d ∧
                 a * (3 * i₂ - d) = b * (2 * d - 3 * i₁ - 3 * i₂)

open BasicInterval

example (a b c : ℤ) (H : 0 ≤ a) (h : b ≤ c) (h' : 0 ≤ b) : b * a ≤ c * a := by
  exact Int.mul_le_mul_of_nonneg_right h H

/-- If `I = [a₁/b₁, a₂/b₂]` is a basic interval such that `I ∩ S_≤ ⊆ {a_2/b_2}`,
then the weight vector associated to any fraction in the interior of `I` is dominated
by the weight vector associated to the left endpoint of `I`. -/
lemma dom_of_mem_interior_left (d : ℕ) [NeZero d] {a b : ℕ} {I : BasicInterval} (hm : mem_interior a b I)
    (hc : a.coprime b) (h : ∀ a' b', mem_S_le d a' b' → mem a' b' I → a' * I.b₂ = b' * I.a₂) :
    of_fraction d I.a₁ I.b₁ ≤d of_fraction d a b := by
  obtain ⟨k₁, k₂, hk₁, hk₂, h₁, h₂⟩ := exists_of_mem_interior hm
  apply dom_of_pair_le
  intro i hi -- `hi : ⟨vᵢ, w₋⟩ ≥ 0`
  have hi' : 0 ≤ pair' (of_fraction d I.a₂ I.b₂) (v i) -- `⟨vᵢ, w₊⟩ ≥ 0`
  · 
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
