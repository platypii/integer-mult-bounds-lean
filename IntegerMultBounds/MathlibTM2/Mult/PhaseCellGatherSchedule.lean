module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpGatherBatch

/-! Forward differences of ordered origins describe a single restoring sweep.
The final zero advance copies the last window without moving past it. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds.MathlibTM2.Mult.ShortConv

def windowAdvances : ℕ → List ℕ → List ℕ
  | _, [] => [0]
  | p, q::qs => (q-p)::windowAdvances q qs

@[simp] theorem windowAdvances_length (p : ℕ) (ps : List ℕ) :
    (windowAdvances p ps).length = ps.length+1 := by
  induction ps generalizing p with
  | nil => rfl
  | cons q qs ih => simp [windowAdvances, ih]

/-- Ordered origins whose whole windows fit also supply every advance fit. -/
theorem windowAdvances_fits {A : ℕ} (L p : ℕ) (ps : List ℕ) (E : List (Fin (A+4)))
    (hsorted : (p::ps).Pairwise (· ≤ ·))
    (hfit : ∀ q ∈ p::ps, q+L ≤ E.length) :
    GatherFits L (E.drop p) (windowAdvances p ps) := by
  induction ps generalizing p with
  | nil =>
    have hp := hfit p (by simp)
    simp [windowAdvances, GatherFits, List.length_drop]
    omega
  | cons q qs ih =>
    obtain ⟨hple, htail⟩ := List.pairwise_cons.mp hsorted
    have hpq := hple q (by simp)
    have hp := hfit p (by simp)
    have hq := hfit q (by simp)
    have he : (E.drop p).drop (q-p) = E.drop q := by
      rw [List.drop_drop, Nat.add_sub_of_le hpq]
    refine ⟨by simp only [List.length_drop]; omega, by simp only [List.length_drop]; omega, ?_⟩
    rw [he]
    exact ih q htail (fun r hr => hfit r (by simp [hr]))

/-- A single sweep returns exactly the windows at the original absolute origins. -/
theorem gatherRows_windowAdvances {A : ℕ} (L p : ℕ) (ps : List ℕ) (E : List (Fin (A+4)))
    (hsorted : (p::ps).Pairwise (· ≤ ·)) :
    gatherRows L (E.drop p) (windowAdvances p ps) =
      (p::ps).flatMap (fun q => (E.drop q).take L) := by
  induction ps generalizing p with
  | nil => simp [windowAdvances, gatherRows]
  | cons q qs ih =>
    obtain ⟨hp, ht⟩ := List.pairwise_cons.mp hsorted
    have hpq := hp q (by simp)
    simp only [windowAdvances, gatherRows, List.flatMap_cons]
    rw [List.drop_drop, Nat.add_sub_of_le hpq, ih q ht]
    rfl

/-- Source advances are paid once, regardless of the number of windows. -/
theorem windowAdvances_volume {A : ℕ} (L p : ℕ) (ps : List ℕ) (E : List (Fin (A+4)))
    (hsorted : (p::ps).Pairwise (· ≤ ·))
    (hfit : ∀ q ∈ p::ps, q+L ≤ E.length) :
    p+(windowAdvances p ps).sum ≤ E.length := by
  have hh := gatherFits_sum_le L (E.drop p) (windowAdvances p ps)
    (windowAdvances_fits L p ps E hsorted hfit)
  have hp := hfit p (by simp)
  simp only [List.length_drop] at hh
  omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
