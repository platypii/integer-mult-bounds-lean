module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHaloClassController
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
def localHaloClassCode : TblCode 16 := originInitCode ;; haloPhaseRangeCode ;; localHaloGroupCode

theorem localHaloClassCode_do {A V s t band a b L : ℕ} [NeZero s]
    (hst : s < t) (hab : a ≤ b) (hbS : b ≤ s) (hL : 0 < L)
    (hwide : 8*(t+1)^2+2*band+8 < 2^V) :
    TblDo A V V localHaloClassCode (haloClassRawState A s t band a b L)
      (fun st' => st'.acc = ((haloLengthGroup s t band a b L).flatMap
        (fun phase => tblPairs A V (haloStart s t band a phase) 0)).reverse ++ [])
      (36*haloPhaseCount s t a b+16) := by
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
        apply (localHaloGroupCode_do st₂
          (by simpa [haloClassReadyState,haloClassRawState] using hf 0 (by decide) (by decide) (by decide))
          (by simpa [haloClassReadyState,haloClassRawState] using hf 2 (by decide) (by decide) (by decide))
          (by simpa [haloClassReadyState,haloClassRawState] using hf 3 (by decide) (by decide) (by decide))
          (by simpa [haloClassReadyState,haloClassRawState] using hf 6 (by decide) (by decide) (by decide))
          (by simpa [haloClassReadyState,haloClassRawState] using hf 7 (by decide) (by decide) (by decide))
          (by simpa [haloClassReadyState,haloClassRawState] using hf 12 (by decide) (by decide) (by decide))
          hstart hend
          (by simpa [haloClassReadyState,haloClassRawState] using hf 13 (by decide) (by decide) (by decide))
          (by simpa [haloClassReadyState,haloClassRawState] using hf 14 (by decide) (by decide) (by decide))
          hab hbS hst hL hwide).mono
        · intro st₃ hout
          simpa only [hacc,haloClassReadyState,haloClassRawState] using hout
        · exact le_rfl))
  exact hc.mono (fun _ h => h) (by omega)

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def localHaloClassController : Pr P₀ 117 Q A U := countedOriginHost localHaloClassCode

theorem localHaloClassController_exec {V s t band a b L : ℕ}
    (hs : 0 < s) (hst : s < t) (hband : band ≤ s) (hab : a ≤ b) (hbs : b ≤ s) (hL : 0 < L) (hLs : L ≤ s)
    (hwide : 8*(t+1)^2+2*band+8 < 2^V)
    (hA : 4 ≤ A) (v : HS 117 Q A U) (S : Stacks 117 A)
    (hS : tblHolds originReg S (tblRho V
      (List.replicate V tick)
      (List.replicate V tick) (haloClassRawState A s t band a b L)))
    (h104 : S.R 104 = []) (h106 : S.R 106 = []) (h116 : S.R 116 = []) :
    ∃ v' S' m, ∃ st' : TblSt 16 A, v'.user = v.user ∧
      m ≤ (36*haloPhaseCount s t a b+16)*tblC V V + (haloLengthGroup s t band a b L).length*(8*V+6)+6 ∧
      Exec body localHaloClassController (mk v S) m (mk v' S') ∧
      S'.R 109 = haloOriginPackets A V s t band a b L ++ S.R 109 ∧
      S'.R 116 = List.replicate (haloLengthGroup s t band a b L).length tick ∧
      tblHolds originReg S' (tblRho V (List.replicate V tick) (List.replicate V tick) ⟨st'.val, []⟩) ∧
      (∀ j, st'.val j < 2^V) ∧ S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧
      ∀ k, k ≠ 109 → k ≠ 116 → (∀ r, originReg r ≠ k) → S'.R k = S.R k := by
  let : NeZero s := ⟨by omega⟩
  have hpkt : s < 2^V := by nlinarith only [hwide,hst]
  have hV : 0 < V := by
    by_contra h
    have he : V = 0 := by omega
    simp [he] at hwide
  exact countedOriginHost_exec localHaloClassCode (haloClassRawState A s t band a b L)
    (localHaloClassCode_do hst hab hbs hL hwide) hpkt.le le_rfl hA hV
    (haloClassRawState_bounded (hab.trans hbs) hbs hLs hst hband hwide)
    rfl v S hS h104 h106 h116

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
