import Mathlib.Tactic

/-!
# Some useful lemmas that are not specific to weigths

In this file we collect some results that we need, but seem to be missing
from Mathlib.
-/

namespace Nat

/-- Helper lemma that might go into Mathlib -/
lemma proportional_of_mul_eq_mul_of_coprime {a b c d : ℕ} (h : a * d = b * c) (h' : Coprime a b) :
    ∃ m, c = m * a ∧ d = m * b := by
  obtain ⟨c₁, rfl⟩ := (Coprime.dvd_mul_left h').mp <| Dvd.intro d h
  obtain ⟨d₁, rfl⟩ := (Coprime.dvd_mul_left h'.symm).mp <| Dvd.intro _ h.symm
  cases' eq_or_ne (a * b) 0 with H H
  · rcases mul_eq_zero.mp H with rfl | rfl
    · obtain rfl : b = 1 := h'
      exact ⟨d₁, by simp⟩
    · obtain rfl : a = 1 := h'.symm
      exact ⟨c₁, by simp⟩
  · rw [← mul_assoc, ← mul_assoc, mul_comm b] at h
    obtain rfl := mul_left_cancel₀ H h
    exact ⟨d₁, by simp [mul_comm d₁]⟩

lemma eq_and_eq_of_coprime_coprime_mul_eq_mul {a b c d : ℕ} (hab : Coprime a b)
    (hcd : Coprime c d) (h : a * d = b * c) :
    a = c ∧ b = d :=
  ⟨dvd_antisymm (hab.dvd_of_dvd_mul_left <| Dvd.intro d h)
                    (hcd.dvd_of_dvd_mul_right <| Dvd.intro_left b h.symm),
   dvd_antisymm (hab.symm.dvd_of_dvd_mul_left <| Dvd.intro c h.symm)
                    (hcd.symm.dvd_of_dvd_mul_right <| Dvd.intro_left a h)⟩

lemma eq_one_of_coprime_mul_mul {a b c : ℕ} (h : Coprime (a * b) (a * c)) : a = 1 :=
  (coprime_self a).mp <| Coprime.coprime_mul_right <| Coprime.coprime_mul_right_right h

end Nat
