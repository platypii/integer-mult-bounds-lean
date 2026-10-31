module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellScatterSchedule

/-! Publication depends only on disjoint destination intervals. Origins need
not be phase-cell boundaries; equal-length generated cores use the same sweep. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

structure PublicationWindows (s L : ℕ) where
  origins : List ℕ
  disjoint : origins.Pairwise (fun p q => p+L ≤ q)
  fits : ∀ p ∈ origins, p+L ≤ s
  count_le : origins.length ≤ s

namespace PublicationWindows
variable {s L : ℕ}

def symbolOrigins (windows : PublicationWindows s L) (w : ℕ) :=
  windows.origins.map (·*w)

def gaps (windows : PublicationWindows s L) (w : ℕ) :=
  windowGaps (L*w) 0 (windows.symbolOrigins w)

@[simp] theorem gaps_length (windows : PublicationWindows s L) (w : ℕ) :
    (windows.gaps w).length = windows.origins.length := by
  simp [gaps,symbolOrigins]

theorem symbolOrigins_disjoint (windows : PublicationWindows s L) (w : ℕ) :
    (windows.symbolOrigins w).Pairwise (fun p q => p+L*w ≤ q) := by
  apply List.pairwise_map.mpr
  exact windows.disjoint.imp (fun h => by
    simpa only [Nat.add_mul] using Nat.mul_le_mul_right w h)

theorem gaps_fits {α : Type*} (windows : PublicationWindows s L) (w : ℕ)
    (E : List α) (hE : s*w ≤ E.length) : ScatterFits (L*w) E (windows.gaps w) := by
  apply windowGaps_fits (L*w) 0 _ E (fun _ _ => Nat.zero_le _)
    (windows.symbolOrigins_disjoint w)
  intro p hp
  change p ∈ windows.origins.map (·*w) at hp
  obtain ⟨origin,horigin,he⟩ := List.mem_map.mp hp
  subst p
  have hfit : origin*w+L*w ≤ s*w := by
    simpa only [Nat.add_mul] using Nat.mul_le_mul_right w (windows.fits origin horigin)
  exact hfit.trans hE

theorem gaps_volume (windows : PublicationWindows s L) (w : ℕ) :
    scatterVolume (L*w) (windows.gaps w) ≤ s*w := by
  let E : List Unit := List.replicate (s*w) ()
  simpa [E] using scatterVolume_le (L*w) E (windows.gaps w)
    (windows.gaps_fits w E (by simp [E]))

def cost (windows : PublicationWindows s L) (w : ℕ) :=
  windows.origins.length*(12*(L*w)+23)+12*(windows.gaps w).sum+6

theorem cost_le (windows : PublicationWindows s L) (w : ℕ) (hw : 1 ≤ w) :
    windows.cost w ≤ 35*s*w+6 := by
  have hvol := windows.gaps_volume w
  simp only [scatterVolume,gaps_length] at hvol
  have hc := windows.count_le
  have hsw : s ≤ s*w := by simpa using Nat.mul_le_mul_left s hw
  dsimp only [cost]
  nlinarith only [hvol,hc,hsw]

end PublicationWindows
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
