import Mathlib.Tactic

/-!
# Some useful lemmas that are not specific to weigths

In this file we collect some results that we need, but seem to be missing
from Mathlib.
-/

namespace Weight

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

lemma eq_and_eq_of_coprime_coprime_mul_eq_mul {a b c d : ℕ} (hab : Nat.Coprime a b)
    (hcd : Nat.Coprime c d) (h : a * d = b * c) :
    a = c ∧ b = d :=
  ⟨Nat.dvd_antisymm (hab.dvd_of_dvd_mul_left <| Dvd.intro d h)
                    (hcd.dvd_of_dvd_mul_right <| Dvd.intro_left b h.symm),
   Nat.dvd_antisymm (hab.symm.dvd_of_dvd_mul_left <| Dvd.intro c h.symm)
                    (hcd.symm.dvd_of_dvd_mul_right <| Dvd.intro_left a h)⟩

lemma eq_one_of_coprime_mul_mul {a b c : ℕ} (h : Nat.Coprime (a * b) (a * c)) : a = 1 :=
  (Nat.coprime_self a).mp <| Nat.Coprime.coprime_mul_right <| Nat.Coprime.coprime_mul_right_right h

open Nat in
lemma lt_two_mul_of_div_two_lt {a d : ℕ} (h : d / 2 < a) : d < 2 * a := by
  rw [lt_iff_add_one_le, ← div_add_mod d 2, add_right_comm]
  rw [lt_iff_add_one_le, ← mul_le_mul_left (a := 2) zero_lt_two] at h
  rw [mul_add, two_mul 1, ← add_assoc] at h
  exact (add_le_add_left (lt_succ.mp <| mod_lt d (zero_lt_two)) _).trans h

end Weight
