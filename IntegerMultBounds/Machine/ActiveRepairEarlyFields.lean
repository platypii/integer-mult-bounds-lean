import IntegerMultBounds.Machine.ActiveRepairEarlyFieldsCleanup

/-! Reusable early repair calculation from actual extracted fields and their
current source controls. Full original-layout rank patching is separate. -/
namespace IntegerMultBounds.Machine.ActiveRepairEarlyFields
noncomputable section
open ActiveRepairEarlyFieldsBank

def program := seq ActiveRepairEarlyFieldsRun.program ActiveRepairEarlyFieldsCleanup.program

theorem runs (q b : ℕ) (hb : 1≤b) (hbq : b+1≤q) (hbq3 : b+3≤q)
    (V W Z cs : List Bool) (hs : Fin 3 → List Bool)
    (hV : V.length=Z.length*q) (hW : W.length=Z.length*b)
    (hv : ∀ i, Counter.value (hs i)=CountedRankSplitBank.values q b Z.length i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    HoareTime program (fun z => z=before V W Z cs hs)
      (fun z => z=ActiveRepairEarlyFieldsCleanup.output q b hb hbq V W Z cs hs)
      (4400*((Z.length+1)*(q+b+1))) := by
  have h1 := ActiveRepairEarlyFieldsRun.runs q b hb hbq hbq3 V W Z cs hs hV hW hv hc
  have h2 := ActiveRepairEarlyFieldsCleanup.runs q b hb hbq V W Z cs hs hV hW
  have hp : 1≤(Z.length+1)*(q+b+1) := Nat.mul_pos (by omega) (by omega)
  exact (h1.seq h2).consequence (fun _ h => h) (fun _ h => h) (by omega)

end
end IntegerMultBounds.Machine.ActiveRepairEarlyFields
