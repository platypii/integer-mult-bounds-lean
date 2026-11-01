module

public import IntegerMultBounds.MathlibTM2.Fast.BandLine
public import IntegerMultBounds.MathlibTM2.Host.AutoStock

/-! Native band bookkeeping has a fixed push bound. Numerical multiplication
is deliberately absent: its reusable reserve is supplied by the stream rule. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.Main
variable {T Q A : ℕ} {P U : Type} {rg : RsbR → Fin T}

theorem rsbMv_native (c t x y : Fin T) :
    mnNativePushBound 2 (rsbMv (P := P) (Q := Q) (A := A) (U := U) c t x y) := by
  simp [rsbMv,scanR,drainR,popDo,keepIn,rsbMvTop,moveR,moveStep,whileR,peekR,
    mnNativePushBound,mnActPush]

theorem bandPopP_native : mnNativePushBound 2 (bandPopP (P := P) (Q := Q) (A := A) (U := U) rg) := by
  exact ⟨rsbMv_native ..,by simp [moveR,moveStep,whileR,peekR,mnNativePushBound,mnActPush]⟩

theorem bandColP_native : mnNativePushBound 2 (bandColP (P := P) (Q := Q) (A := A) (U := U) rg) := by
  exact ⟨rsbMv_native ..,by simp [moveR,moveStep,whileR,peekR,mnNativePushBound,mnActPush]⟩

theorem rsbSubBody_native : mnNativePushBound 2 (rsbSubBody (P := P) (Q := Q) (A := A) (U := U) rg) := by
  refine ⟨⟨by simp [mnNativePushBound,mnActPush],autoWord_native _ _ _ _ _ _ _ (by decide) (by decide)⟩,?_⟩
  simp [moveR,moveStep,whileR,peekR,mnNativePushBound,mnActPush]

theorem bandSubP_native : mnNativePushBound 2 (bandSubP (P := P) (Q := Q) (A := A) (U := U) rg) := by
  refine ⟨rsbMv_native ..,⟨?_,⟨rsbSubBody_native,?_⟩⟩⟩ <;>
    simp [moveR,moveStep,whileR,peekR,mnNativePushBound,mnActPush]

theorem rsbCopyTo_native (x y : RsbR) :
    mnNativePushBound 2 (rsbCopyTo (P := P) (Q := Q) (A := A) (U := U) rg x y) := by
  simp [rsbCopyTo,copyR,copyStep,moveR,moveStep,whileR,peekR,mnNativePushBound,mnActPush]

theorem rsbRep_native {p : Pr P T Q A U} (a t : Fin T) (hp : mnNativePushBound 2 p) :
    mnNativePushBound 2 (rsbRep a t p) := by
  simp [rsbRep,rsbScanIf,popPush,moveR,moveStep,whileR,peekR,mnNativePushBound,mnActPush,hp]

/-- Lift an existing native phase contract, using only its own linear traffic bill. -/
theorem RsbRuns.exec_within_native {R : Type} {rg : R → Fin T} {ι : Fin 64 → Fin T}
    {body : P → Pr P T Q A U} {p : Pr P T Q A U} {ρ ρ' : R → List (Fin (A+4))}
    {time c : ℕ} (h : RsbRuns body rg ι p ρ ρ' time) (hp : mnNativePushBound c p)
    (v : HS T Q A U) (S : Stacks T A) (hc : RsbClean ι S) (hS : RsbHolds rg S ρ) :
    ∃ v' F n, v'.user = v.user ∧ n ≤ time ∧ RsbHolds rg F ρ' ∧ RsbFr rg S F ∧
      ∀ depth, ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+c*time)
        depth p (mk v S) n (mk v' F) := by
  obtain ⟨v',F,n,hu,hn,he,hh,hf⟩ := h v S hc hS
  exact ⟨v',F,n,hu,hn,hh,hf,fun depth =>
    mn_native_exec_within he c hp depth _
      (Nat.add_le_add_left (Nat.mul_le_mul_left c hn) _)⟩

end IntegerMultBounds.MathlibTM2.Fast
