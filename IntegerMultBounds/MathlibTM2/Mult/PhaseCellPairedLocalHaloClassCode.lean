module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHaloClassController
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPairedLocalHaloGroup
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHaloPhaseRangeCode
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellOriginController
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellWeightWidth

/-! Generate one clipped length class by scanning only its halo phase range. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

/-- Initialize once, compute local endpoints, and scan precisely that range. -/
def pairedLocalHaloClassCode : TblCode 16 := originInitCode ;; haloPhaseRangeCode ;; pairedLocalHaloGroupCode

theorem pairedLocalHaloClassCode_do {A V s t band a b L : ℕ} [NeZero s]
    (hst : s < t) (hab : a ≤ b) (hbS : b ≤ s) (hL : 0 < L)
    (hwide : 8*(t+1)^2+2*band+8 < 2^V) :
    TblDo A V V pairedLocalHaloClassCode (haloClassRawState A s t band a b L)
      (fun st' => st'.acc = ((haloLengthGroup s t band a b L).flatMap
        (fun phase => tblPairs A V (haloStart s t band a phase) (haloStart s t band a phase-a))).reverse ++ [])
      (37*haloPhaseCount s t a b+16) := by
  have hi := haloClassInitCode_do (A := A) (W := V) (w := V)
    (a := a) (b := b) (L := L) (NeZero.pos s) hst hwide
  have hc := hi.seq (fun st₁ heq => by
    subst st₁
    exact (haloPhaseRangeCode_do (w := V) (haloClassReadyState A s t band a b L)
      (by simp [haloClassReadyState,haloClassRawState])
      (by simp [haloClassReadyState,haloClassRawState])
      (by simp [haloClassReadyState,haloClassRawState])
      (by simp [haloClassReadyState,haloClassRawState])
      (NeZero.pos s) hst (hab.trans hbS) hbS hwide).seq
      (fun st₂ ⟨hstart,hend,hacc,hframe⟩ => by
        have hf (k : Fin 16) (hk4 : k ≠ 4) (hk8 : k ≠ 8) (hk15 : k ≠ 15) :=
          hframe k hk4 hk8 hk15
        apply (pairedLocalHaloGroupCode_do st₂
          (by simpa [haloClassReadyState,haloClassRawState] using hf 0 (by decide) (by decide) (by decide))
          (by simpa [haloClassReadyState,haloClassRawState] using hf 2 (by decide) (by decide) (by decide))
          (by simpa [haloClassReadyState,haloClassRawState] using hf 3 (by decide) (by decide) (by decide))
          (by simpa [haloClassReadyState,haloClassRawState] using hf 6 (by decide) (by decide) (by decide))
          (by simpa [haloClassReadyState,haloClassRawState] using hf 7 (by decide) (by decide) (by decide))
          hstart hend
          (by simpa [haloClassReadyState,haloClassRawState] using hf 13 (by decide) (by decide) (by decide))
          (by simpa [haloClassReadyState,haloClassRawState] using hf 14 (by decide) (by decide) (by decide))
          hab hbS hst hL hwide).mono
        · intro st₃ hout
          simpa only [hacc,haloClassReadyState,haloClassRawState] using hout
        · exact le_rfl))
  exact hc.mono (fun _ h => h) (by omega)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
