module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellTakeKeyBatch
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCommonWidthInput

/-! Isolate one key batch and normalize only its owned numerical source. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 303 Q A U}

def keyBatchInput : Pr P 303 Q A U :=
  .seq (takeKeyBatch 16 17 18 15 110 19 20 21) commonWidthInput

theorem keyBatchInput_exec (hA : 4 ≤ A) {p u l target s t a b : ℕ} [NeZero s]
    (hst : s < t) (ha : a ≤ s) (hb : b ≤ s) (hband : PhaseCellBand.width p u ≤ s)
    (wl : List (Fin (A+4))) (hwl : wl.length = inverseCallerWordWidth p u l target s t)
    (N L W : ℕ) (xs : List GaussianInt) (hlen : xs.length = N*L)
    (hxs : ∀ z ∈ xs, ‖value p z‖ ≤ 1) (tail : List (Fin (A+4)))
    (v : HS 303 Q A U) (S : Stacks 303 A)
    (hS : tblHolds familyInverseScalarReg S
      (tblRho (inverseCallerWordWidth p u l target s t) wl [] (inverseInputScalars p u l target s t a b)))
    (hblank : ∀ r ∈ ([0,1,2,3,4,5,6,7,8,9,10,13,14,18,19,20,21,110] : List (Fin 303)), S.R r = [])
    (hreplicas : (S.R 16).length = N) (hpacket : (S.R 17).length = L*W)
    (hwide : (S.R 11).length = W) (hsrc : S.R 15 = cstream A W xs++tail) :
    let E := inverseExecutionExponent p l target (haloBoundary s t (PhaseCellBand.width p u) a b).card (PhaseCellBand.width p u)
    let w := 8*E+8
    let d := 4*E-p-1
    w ≤ W → (S.R 12).length = w →
    ∃ v' n, v'.user = v.user ∧
      n ≤ (N*(12*(L*W)+9)+12)+
        (4*W+4*w+2*(W-w)+(xs.length*(4*W+2*w+14)+4)+10+
          inputShiftBatchCost (inverseCallerWordWidth p u l target s t) p u l target s t a b xs.length) ∧
      Exec body keyBatchInput (mk v S) n
        (mk v' {S with R := (Function.update (Function.update S.R 15 tail) 110
          (cstream A w (xs.map (fun z => (2 : GaussianInt)^d*z))))}) := by
  dsimp only
  intro hW hword
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := takeCoefficientKeyBatch_exec (body := body)
    (show [(16 : Fin 303),17,18,15,110,19,20,21].Nodup by decide)
    N L W xs hlen tail v S hreplicas hpacket hsrc
    (hblank 110 (by decide)) (hblank 18 (by decide)) (hblank 19 (by decide))
    (hblank 20 (by decide)) (hblank 21 (by decide))
  let M : Stacks 303 A := {S with R := (Function.update (Function.update S.R 15 tail) 110 (cstream A W xs))}
  have hscalar : tblHolds familyInverseScalarReg M
      (tblRho (inverseCallerWordWidth p u l target s t) wl [] (inverseInputScalars p u l target s t a b)) := by
    intro r
    have hoff (k : Fin 263) : familyInverseScalarReg r ≠ familyInverseCoreReg k := familyInverseScalarReg_core r k
    have h15 : familyInverseScalarReg r ≠ (15 : Fin 303) := by
      simpa [familyInverseCoreReg,familyInverseScalarReg] using hoff 15
    have h110 : familyInverseScalarReg r ≠ (110 : Fin 303) := by
      simpa [familyInverseCoreReg,familyInverseScalarReg] using hoff 110
    simpa [M,h15,h110] using hS r
  have hblankM : ∀ r ∈ ([0,1,2,3,4,5,6,7,8,9,10,13,14] : List (Fin 303)), M.R r = [] := by
    intro r hr
    have hoff : r ≠ (15 : Fin 303) ∧ r ≠ 110 := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    simpa [M,hoff.1,hoff.2] using hblank r (List.mem_append_left [18,19,20,21,110] hr)
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := commonWidthInput_exec (body := body) hA hst ha hb hband wl hwl
    W xs hxs v₁ M hscalar hblankM (by simpa [M] using hwide) (by simp [M])
    hW (by simpa [M] using hword)
  refine ⟨v₂,n₁+n₂,hu₂.trans hu₁,Nat.add_le_add hn₁ hn₂,(Exec.seq he₁ he₂).cast rfl ?_⟩
  apply congrArg (mk v₂)
  simp only [M,Function.update_idem]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
