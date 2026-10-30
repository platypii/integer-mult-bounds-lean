module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellKeyBatchInput
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellKeyBatchPlacement
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

theorem protectedKeyBatchInput_exec
    (bodyLarge : P → Pr P 306 Q A U)
    (hbody : ∀ f, bodyLarge f = embProg keyBatchInputReg id (body f)) (hA : 4 ≤ A) {p u l target s t a b : ℕ} [NeZero s]
    (hst : s < t) (ha : a ≤ s) (hb : b ≤ s) (hband : PhaseCellBand.width p u ≤ s)
    (wl : List (Fin (A+4))) (hwl : wl.length = inverseCallerWordWidth p u l target s t)
    (N L W : ℕ) (xs : List GaussianInt) (hlen : xs.length = N*L)
    (hxs : ∀ z ∈ xs, ‖value p z‖ ≤ 1) (tail : List (Fin (A+4)))
    (v : HS 306 Q A U) (S : Stacks 306 A)
    (hS : tblHolds familyInverseScalarReg (embStk keyBatchInputReg S)
      (tblRho (inverseCallerWordWidth p u l target s t) wl [] (inverseInputScalars p u l target s t a b)))
    (hblank : ∀ r ∈ ([0,1,2,3,4,5,6,7,8,9,10,13,14,18,19,20,21,110] : List (Fin 303)), S.R (keyBatchInputReg r) = [])
    (hreplicas : (S.R 304).length = N) (hpacket : (S.R 17).length = L*W)
    (hwide : (S.R 305).length = W) (hsrc : S.R 303 = cstream A W xs++tail) :
    let E := inverseExecutionExponent p l target (haloBoundary s t (PhaseCellBand.width p u) a b).card (PhaseCellBand.width p u)
    let w := 8*E+8
    let d := 4*E-p-1
    w ≤ W → (S.R 12).length = w →
    ∃ v' n, v'.user = v.user ∧
      n ≤ (N*(12*(L*W)+9)+12)+
        (4*W+4*w+2*(W-w)+(xs.length*(4*W+2*w+14)+4)+10+
          inputShiftBatchCost (inverseCallerWordWidth p u l target s t) p u l target s t a b xs.length) ∧
      Exec bodyLarge (embProg keyBatchInputReg id keyBatchInput) (mk v S) n
        (mk v' {S with R := (Function.update (Function.update S.R 303 tail) 110
          (cstream A w (xs.map (fun z => (2 : GaussianInt)^d*z))))}) := by
  dsimp only
  intro hW hword
  obtain ⟨v₁,n,hu,hn,he⟩ := keyBatchInput_exec (body := body) hA hst ha hb hband wl hwl
    N L W xs hlen hxs tail (embDn keyBatchInputReg v) (embStk keyBatchInputReg S) hS hblank
    (by simpa [embStk,keyBatchInputReg] using hreplicas)
    (by simpa [embStk,keyBatchInputReg] using hpacket)
    (by simpa [embStk,keyBatchInputReg] using hwide)
    (by simpa [embStk,keyBatchInputReg] using hsrc) hW
    (by simpa [embStk,keyBatchInputReg] using hword)
  obtain ⟨v₂,hv₂,hu₂,he₂⟩ := exec_emb_ovr keyBatchInputReg_injective hbody he v rfl S rfl
  refine ⟨v₂,n,hu₂.trans hu,hn,?_⟩
  let B : Stacks 303 A := {embStk keyBatchInputReg S with
    R := Function.update (embStk keyBatchInputReg S).R 15 tail}
  let E := inverseExecutionExponent p l target (haloBoundary s t (PhaseCellBand.width p u) a b).card (PhaseCellBand.width p u)
  let ys := cstream A (8*E+8) (xs.map (fun z => (2 : GaussianInt)^(4*E-p-1)*z))
  change Exec bodyLarge (embProg keyBatchInputReg id keyBatchInput) (mk v S) n
    (mk v₂ (embOvr keyBatchInputReg ({B with R := Function.update B.R 110 ys}).get S)) at he₂
  rw [embOvr_updR keyBatchInputReg_injective] at he₂
  have hB : embOvr keyBatchInputReg B.get S =
      {S with R := Function.update S.R (keyBatchInputReg 15) tail} := by
    dsimp only [B]
    rw [embOvr_updR keyBatchInputReg_injective,embOvr_stk]
  rw [hB] at he₂
  simpa only [show keyBatchInputReg 15 = 303 by decide,
    show keyBatchInputReg 110 = 110 by decide] using he₂

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
