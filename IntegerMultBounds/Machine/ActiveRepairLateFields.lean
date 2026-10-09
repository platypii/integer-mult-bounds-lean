import IntegerMultBounds.Machine.ActiveRepairLateFieldsCleanup

/-! One fixed extracted-field later repair machine. No local rank or prepared
key sentinel is supplied; copies, inverse, guard, toggle and erasure are paid. -/
namespace IntegerMultBounds.Machine.ActiveRepairLateFields
noncomputable section

def program := seq ActiveRepairLateFieldsRun.program ActiveRepairLateFieldsCleanup.program

theorem runs (q b : ℕ) (hb : 1≤b) (hbq : b+1≤q) (hbq3 : b+3≤q)
    (V W U X cs : List Bool) (hs : Fin 3 → List Bool)
    (hV : V.length=X.length*q) (hW : W.length=X.length*b) (hU : U.length=X.length*b)
    (hv : ∀ i, Counter.value (hs i)=CountedPackedShapeHeaders.originalValues q b X.length i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    HoareTime program (fun z => z=ActiveRepairLateFieldsBank.before V W U X cs hs)
      (fun z => z=ActiveRepairLateFieldsCleanup.output q b hb hbq V W U X cs hs)
      (9700*((X.length+1)*(q+b+1))) := by
  have h1 := ActiveRepairLateFieldsRun.runs q b hb hbq hbq3 V W U X cs hs hV hW hU hv hc
  have h2 := ActiveRepairLateFieldsCleanup.runs q b hb hbq V W U X cs hs hV hW hU
  exact (h1.seq h2).consequence (fun _ h => h) (fun _ h => h) (by nlinarith)

end
end IntegerMultBounds.Machine.ActiveRepairLateFields
