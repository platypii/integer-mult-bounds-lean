module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPacketWidthControls
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDerivedInputShiftBatch

/-! Common-width input packets feed the generated numerical scale conversion. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 303 Q A U}

def commonWidthInput : Pr P 303 Q A U :=
  .seq (generatedNarrowPackets 11 12 110 4 0 13 14) (inputShiftBatch false)

/-- Width narrowing and the existing generated scale conversion agree on the
actual numerical input word. The binary inverse scalar bank is borrowed and
restored; only the owned source stream changes. -/
theorem commonWidthInput_exec (hA : 4 ≤ A) {p u l target s t a b : ℕ} [NeZero s]
    (hst : s < t) (ha : a ≤ s) (hb : b ≤ s) (hband : PhaseCellBand.width p u ≤ s)
    (wl : List (Fin (A+4))) (hwl : wl.length = inverseCallerWordWidth p u l target s t)
    (W : ℕ) (xs : List GaussianInt) (hxs : ∀ z ∈ xs, ‖value p z‖ ≤ 1)
    (v : HS 303 Q A U) (S : Stacks 303 A)
    (hS : tblHolds familyInverseScalarReg S
      (tblRho (inverseCallerWordWidth p u l target s t) wl [] (inverseInputScalars p u l target s t a b)))
    (hblank : ∀ r ∈ ([0,1,2,3,4,5,6,7,8,9,10,13,14] : List (Fin 303)), S.R r = [])
    (hwide : (S.R 11).length = W) (hsrc : S.R 110 = cstream A W xs) :
    let E := inverseExecutionExponent p l target (haloBoundary s t (PhaseCellBand.width p u) a b).card (PhaseCellBand.width p u)
    let w := 8*E+8
    let d := 4*E-p-1
    w ≤ W → (S.R 12).length = w →
    ∃ v' n, v'.user = v.user ∧
      n ≤ 4*W+4*w+2*(W-w)+(xs.length*(4*W+2*w+14)+4)+10+
        inputShiftBatchCost (inverseCallerWordWidth p u l target s t) p u l target s t a b xs.length ∧
      Exec body commonWidthInput (mk v S) n
        (mk v' {S with R := (Function.update S.R 110
          (cstream A w (xs.map (fun z => (2 : GaussianInt)^d*z))))}) := by
  dsimp only
  let E := inverseExecutionExponent p l target (haloBoundary s t (PhaseCellBand.width p u) a b).card (PhaseCellBand.width p u)
  let w := 8*E+8
  let d := 4*E-p-1
  intro hw hword
  obtain ⟨v₁,hu₁,he₁⟩ := generatedNarrowPackets_exec (body := body)
    (show [(11 : Fin 303),12,110,4,0,13,14].Nodup by decide)
    W w (by omega) hw xs v S hwide hword hsrc
    (hblank 4 (by decide)) (hblank 0 (by decide))
    (hblank 13 (by decide)) (hblank 14 (by decide))
  let S₁ : Stacks 303 A := {S with R := Function.update S.R 110 (cstream A w xs)}
  have hS₁ : tblHolds familyInverseScalarReg S₁
      (tblRho (inverseCallerWordWidth p u l target s t) wl [] (inverseInputScalars p u l target s t a b)) := by
    intro r
    have hne := familyInverseScalarReg_core r (110 : Fin 263)
    have hne' : familyInverseScalarReg r ≠ (110 : Fin 303) := by
      simpa [familyInverseCoreReg,familyInverseScalarReg] using hne
    simpa [S₁,hne'] using hS r
  have hblank₁ : ∀ r ∈ ([0,1,2,3,4,5,6,7,8,9,10] : List (Fin 303)), S₁.R r = [] := by
    intro r hr
    have hne : r ≠ (110 : Fin 303) := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    simpa [S₁,hne] using hblank r (by exact List.mem_append_left [13,14] hr)
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := inputShiftBatch_derived_exec (body := body) hA false
    hst ha hb hband wl hwl xs hxs v₁ S₁ hS₁ hblank₁ (by simp [S₁,inputShiftSource,w,E])
  refine ⟨v₂,_,hu₂.trans hu₁,Nat.add_le_add_left hn₂ _,
    (Exec.seq he₁ he₂).cast rfl ?_⟩
  apply congrArg (mk v₂)
  simp [S₁,inputShiftResult]

/-- The output has exactly the numerical precision and signed fits used by
normalization, including negative real and imaginary components. -/
theorem commonWidthInput_value_fits (p l target rowCount band : ℕ)
    (z : GaussianInt) (hz : ‖value p z‖ ≤ 1) :
    let E := inverseExecutionExponent p l target rowCount band
    let d := 4*E-p-1
    value (4*E) ((2 : GaussianInt)^d*z) = (1/2 : ℂ)*value p z ∧
      TopFitsZ (8*E+8) ((2 : GaussianInt)^d*z) := by
  dsimp only
  let E := inverseExecutionExponent p l target rowCount band
  have hp : p+1 ≤ 4*E := by dsimp [E,inverseExecutionExponent]; omega
  have hd : p+1+(4*E-p-1) = 4*E := by omega
  refine ⟨?_,(inputShift_fits p (4*E-p-1) (8*E+8) (by omega) z hz).2⟩
  simpa only [hd] using halfGrid_value p (4*E-p-1) z

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
