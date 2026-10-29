module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedHaloBoundaryWorkspace
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedCellInputBank
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellLengthKeyReady
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellComponentWorkspace
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryWorkspace
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellTableWorkspace
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReleaseCellRuntime

/-! Retire the factory's coordinate page and headers, retaining all factor data.
The arithmetic readiness contract supplies the remaining released native bank. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 242 Q A U}

def releasePackedBoundaryRuntime : Pr P 242 Q A U := clearWords [109,115,116]

def releasedPackedBoundaryRuntime {A : ℕ} (S : Stacks 242 A) : Stacks 242 A :=
  {S with R := fun k => if k ∈ [(109 : Fin 242),115,116] then [] else S.R k}

theorem releasePackedBoundaryRuntime_exec (N V : ℕ) (v : HS 242 Q A U) (S : Stacks 242 A)
    (h109 : (S.R 109).length = N*V) (h115 : (S.R 115).length = V)
    (h116 : (S.R 116).length = N) :
    ∃ v', v'.user = v.user ∧
      Exec body releasePackedBoundaryRuntime (mk v S) (2*(N*V+V+N)+7)
        (mk v' (releasedPackedBoundaryRuntime S)) := by
  obtain ⟨v',hu,he⟩ := clearWords_exec (body := body) [(109 : Fin 242),115,116] (by decide) v S
  refine ⟨v',hu,he.cast ?_ rfl⟩
  simp [h109,h115,h116]
  omega

theorem releasedPackedBoundaryRuntime_high {A : ℕ} (S : Stacks 242 A)
    (k : Fin 242) (hk : 168 ≤ k.val) :
    (releasedPackedBoundaryRuntime S).R k = S.R k := by
  have h109 : k ≠ 109 := by intro he; subst k; contradiction
  have h115 : k ≠ 115 := by intro he; subst k; contradiction
  have h116 : k ≠ 116 := by intro he; subst k; contradiction
  simp [releasedPackedBoundaryRuntime,h109,h115,h116]

theorem releasedPackedBoundaryRuntime_reg {A : ℕ} (S : Stacks 242 A) (i : Fin 226)
    (h109 : i ≠ 109) (h115 : i ≠ 115) (h116 : i ≠ 116) :
    (releasedPackedBoundaryRuntime S).R (packedBoundaryFactorReg i) = S.R (packedBoundaryFactorReg i) := by
  have h109' : packedBoundaryFactorReg i ≠ 109 := packedBoundaryFactorReg_injective.ne h109
  have h115' : packedBoundaryFactorReg i ≠ 115 := packedBoundaryFactorReg_injective.ne h115
  have h116' : packedBoundaryFactorReg i ≠ 116 := packedBoundaryFactorReg_injective.ne h116
  simp [releasedPackedBoundaryRuntime,h109',h115',h116']

theorem releasedPackedBoundaryRuntime_factorState {A : ℕ} (S : Stacks 242 A) :
    boundaryFactorState (embStk preparedBoundaryCoreReg
      (embStk packedBoundaryFactorReg (releasedPackedBoundaryRuntime S))) =
      boundaryFactorState (embStk preparedBoundaryCoreReg (embStk packedBoundaryFactorReg S)) := by
  rw [packedBoundaryFactorState_of_high_frame S _ (releasedPackedBoundaryRuntime_high S)]
  have hrhs : (releasedPackedBoundaryRuntime S).R 143 = S.R 143 := by
    simp [releasedPackedBoundaryRuntime]
  rw [hrhs]
  exact Function.update_eq_self _ _

theorem releasedPackedBoundaryRuntime_native {A precision stage q l s t u band : ℕ}
    (S : Stacks 242 A) (input : List (Fin (A+4)))
    (hleft : ∀ i : Fin 117, S.L ⟨i.val,by omega⟩ = [])
    (hready : LengthKeyReady precision stage q l s t u band 0 0 input
      (embStk componentReg (embStk boundaryArithmeticReg (embStk tableReg
        (embStk boundaryFactorLegacyReg (embStk preparedBoundaryCoreReg
          (embStk packedBoundaryFactorReg S))))))) :
    embStk packedCellCoreReg (embStk packedHaloRuntimeReg (releasedPackedBoundaryRuntime S)) =
      releasedCellBank [] input (S.R 93) S.inp S.out := by
  have hread (k : Fin 144) (hk : k.val < 117)
      (h109 : k.val ≠ 109) (h115 : k.val ≠ 115) (h116 : k.val ≠ 116) :
      (embStk componentReg (embStk boundaryArithmeticReg (embStk tableReg
        (embStk boundaryFactorLegacyReg (embStk preparedBoundaryCoreReg
          (embStk packedBoundaryFactorReg S)))))).R k = S.R ⟨k.val,by omega⟩ := by
    simp [embStk,componentReg,boundaryArithmeticReg,tableReg,boundaryFactorLegacyReg,
      preparedBoundaryCoreReg,packedBoundaryFactorReg,Fin.ext_iff,h109,h115,h116,
      show k.val ≠ 140 by omega,show k.val ≠ 143 by omega,show k.val ≠ 206 by omega,
      show k.val < 154 by omega]
  refine Stacks.ext rfl rfl ?_ ?_
  · funext i
    exact hleft i
  · funext i
    have hi := i.isLt
    by_cases h93 : i.val = 93
    · simp [embStk,packedCellCoreReg,packedHaloRuntimeReg,releasedPackedBoundaryRuntime,
        releasedCellBank,Fin.ext_iff,h93]
    by_cases h110 : i.val = 110
    · have hs := hready.source
      rw [hread 110 (by decide) (by decide) (by decide) (by decide)] at hs
      simpa [embStk,packedCellCoreReg,packedHaloRuntimeReg,releasedPackedBoundaryRuntime,
        releasedCellBank,Fin.ext_iff,h93,h110] using hs
    by_cases h109 : i.val = 109
    · simp [embStk,packedCellCoreReg,packedHaloRuntimeReg,releasedPackedBoundaryRuntime,
        releasedCellBank,Fin.ext_iff,h93,h110,h109]
    by_cases h115 : i.val = 115
    · simp [embStk,packedCellCoreReg,packedHaloRuntimeReg,releasedPackedBoundaryRuntime,
        releasedCellBank,Fin.ext_iff,h93,h110,h115]
    by_cases h116 : i.val = 116
    · simp [embStk,packedCellCoreReg,packedHaloRuntimeReg,releasedPackedBoundaryRuntime,
        releasedCellBank,Fin.ext_iff,h93,h110,h116]
    have hz := hready.blank ⟨i.val,by omega⟩ hi
      (by simpa [Fin.ext_iff] using h93) (by simpa [Fin.ext_iff] using h110)
    rw [hread _ hi h109 h115 h116] at hz
    simpa [embStk,packedCellCoreReg,packedHaloRuntimeReg,releasedPackedBoundaryRuntime,
      releasedCellBank,Fin.ext_iff,h93,h110,h109,h115,h116] using hz

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
