import IntegerMultBounds.Machine.CompactComplexRootPieceCleanup

/-! One original-header root-piece machine, including paid controller entry
and exit cleanup. The native recursive callback remains an explicit exact
contract; no root paths, base digits or numeric piece descriptors are input. -/
namespace IntegerMultBounds.Machine.CompactComplexRootPieceRun
noncomputable section
open CompactComplexRecursiveGeometry (arity)
open RecursiveChildQuotientsConstant (bits)
variable {a t q : ℕ}

def CallbackSpec (callback : Program (43+(1+t)) q a) (active : ℕ)
    (native : ℕ → Tapes t a) (callCost : ℕ → ℕ → ℕ) : Prop :=
∀ k (hk : k<(Nat.digits arity active).length), ∀ j<(Nat.digits arity active)[k],
      HoareTime callback
      (fun v => v=CompactComplexRootPieceClock.input
        (CompactComplexRootPieceController.state (CompactComplexRootDigits.state 0) (Nat.digits arity active) k)
        (CompactComplexRootPieceVisits.preceding ((Nat.digits arity active).take k)+j*arity^k)
        ((Nat.digits arity active)[k]-j)
        (FiniteReturnStack.bank (CompactComplexRootPieceController.queue (Nat.digits arity active))
          (CompactComplexRootPieceController.cursor (Nat.digits arity active) (k+1)))
        (native (CompactComplexRootPiecePrefixes.count ((Nat.digits arity active).take k)+j)))
      (fun v => v=CompactComplexRootPieceClock.input
        (CompactComplexRootPieceController.state (CompactComplexRootDigits.state 0) (Nat.digits arity active) k)
        (CompactComplexRootPieceVisits.preceding ((Nat.digits arity active).take k)+j*arity^k)
        ((Nat.digits arity active)[k]-j)
        (FiniteReturnStack.bank (CompactComplexRootPieceController.queue (Nat.digits arity active))
          (CompactComplexRootPieceController.cursor (Nat.digits arity active) (k+1)))
        (native (CompactComplexRootPiecePrefixes.count ((Nat.digits arity active).take k)+j+1)))
      (callCost k j)

def program (src : Fin t) (callback : Program (43+(1+t)) q a) : Σ k, Program (43+(1+t)) k a :=
  ⟨_,seq (CompactComplexRootPieceEntry.program src callback).2
    (CompactComplexRootPieceCleanup.program (a := a) (t := t)).2⟩

/-- All controller tapes return to their original blank state. The arbitrary
appended native/stack bank is exactly the callback chain's final bank. -/
theorem runs (src : Fin t) (callback : Program (43+(1+t)) q a) (active : ℕ)
    (native : ℕ → Tapes t a) (callCost : ℕ → ℕ → ℕ)
    (ht : (native 0).tape src=RadixZeroFill.encodedBinary (bits active))
    (hh : (native 0).head src=1) (hc : CallbackSpec callback active native callCost) :
    HoareTime (program src callback).2
      (fun v => v=CompactComplexRootPieceDigit.input CompactComplexRootDigitsFromHeader.emptyState
        (fun _ => blank) 0 (native 0))
      (fun v => v=CompactComplexRootPieceDigit.input CompactComplexRootDigitsFromHeader.emptyState
        (fun _ => blank) 0 (native (CompactComplexRootPiecePrefixes.count (Nat.digits arity active))))
      (2*active+67+101000*(active+arity+1)^2*(Nat.digits arity active).length+
        4*(CompactComplexRootDigits.fields (a := a) (Nat.digits arity active)).length+
        100*((Nat.digits arity active).length+active+arity^(Nat.digits arity active).length+4)+
        ∑ k : Fin (Nat.digits arity active).length,
          (CompactComplexRootPieceController.bodyCost (CompactComplexRootDigits.state 0)
            (Nat.digits arity active) k callCost+2)) := by
  have he := CompactComplexRootPieceEntry.runs src callback active native callCost ht hh hc
  have hx := CompactComplexRootPieceCleanup.runs (Nat.digits arity active)
    (native (CompactComplexRootPiecePrefixes.count (Nat.digits arity active)))
  rw [CompactComplexRootPieceController.final_left] at hx
  apply (he.seq hx).consequence (fun _ h => h) (fun _ h => h)
  omega

end
end IntegerMultBounds.Machine.CompactComplexRootPieceRun
