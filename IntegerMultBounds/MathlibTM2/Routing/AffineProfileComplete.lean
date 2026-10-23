module

public import IntegerMultBounds.MathlibTM2.Routing.AffineSourceProfileGenerate
public import IntegerMultBounds.MathlibTM2.Routing.RepairRotationCoordinates

/-! Profiles whose first physical slot is zero already include the mirrored
terminal coordinate. This covers Y, YZ and X repair rotations without an extra
terminal emitter. Selected/key and temporary-bit profiles remain separate. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

variable {A W m N : ℕ}

theorem sparseCoordinateClose_zero (hm : 0 < m) (pos : ℕ → ℕ) (hzero : pos 0 = 0)
    (src : Fin m → Option (Fin W)) :
    sparseCoordinateClose N (sparsePatternCoordinates (N := N) pos src) =
      sparsePatternCoordinates (N := N) pos src := by
  have ht : ∃ q, (N - 1, q) ∈ sparsePatternCoordinates (N := N) pos src := by
    refine ⟨(src ⟨0, hm⟩).elim 0 Fin.succ, ?_⟩
    simp only [sparsePatternCoordinates, List.mem_reverse, List.mem_ofFn]
    exact ⟨⟨0, hm⟩, by simp [hzero]⟩
  unfold sparseCoordinateClose
  split
  · rfl
  · contradiction

theorem affineSourceProfile_complete_output (Li Lk Ls k : ℕ) (hm : 0 < m)
    (src : Fin m → Option (Fin W)) :
    affineProfileOutput (A := A) Li Lk Ls 0 k 0 N (affineSourceProfile src) =
      sparseCoordinateFrames (Li + Lk) Ls (sparseCoordinateValues
        (sparseCoordinateClose N (sparsePatternCoordinates (N := N) (fun j => j * k) src))) := by
  rw [sparseCoordinateClose_zero hm _ (by simp)]
  simpa only [Nat.zero_add, Nat.add_zero] using
    affineSourceProfile_output (N := N) Li Lk Ls 0 k 0 src

theorem repairAffineProfile_output (p : Par) (X : ℕ) (hG : 0 < p.G) (hK : 0 < p.K)
    (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X)
    (hn : 0 < p.n) (off : Off) (hoff : off = .Y ∨ off = .YZ ∨ off = .X) (j : Fin 2)
    (Li Lk Ls : ℕ) :
    affineProfileOutput (A := A) Li Lk Ls 0 p.G 0 (selectiveTargetWidth p off)
      (affineSourceProfile (repairRotationSources p X hG hK active s off j)) =
      sparseCoordinateFrames (Li + Lk) Ls
        (sparseCoordinateValues (repairRotationCoordinates p X hG hK active s off j)) := by
  rcases hoff with rfl | rfl | rfl <;>
    exact affineSourceProfile_complete_output Li Lk Ls p.G hn _

end IntegerMultBounds.MathlibTM2.Routing
