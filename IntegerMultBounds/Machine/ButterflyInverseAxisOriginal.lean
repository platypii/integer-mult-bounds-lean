import IntegerMultBounds.Machine.ButterflyInverseAxisPrepared

/-! A full inverse axis from the original D,t,R,p headers: physical header
construction, inverse split/arithmetic/merge, copied-header cleanup and selected
axis increment. Exactly the forward clean endpoint bank and cost are used. -/
namespace IntegerMultBounds.Machine.ButterflyInverseAxisOriginal
noncomputable section
open ButterflyAxisHeadersData ButterflyAxisHeadersGeometry ButterflyAxisHeadersBudget
open ButterflyStreamData (Coefficient)
open ButterflyInverseAxisRouting (transformed)
open ButterflyAxisOriginal (bank setup install uninstall finish)

abbrev count := ButterflyAxisOriginal.count

def program := seq (seq (seq (seq setup install) ButterflyInverseAxisPrepared.program) uninstall) finish
abbrev constant := ButterflyAxisOriginal.constant

theorem runs (D t R p : ℕ) (ht : t<D) (hR : 0<R)
    (xs : Fin (RecursiveInterchangeRows.groups 2 (descriptor D t R p)) → Fin 2 → Fin (lower t R) → Coefficient)
    (hw : ∀ h j k,(xs h j k).1.length=ButterflyGuard.width p D ∧
      (xs h j k).2.length=ButterflyGuard.width p D) :
    HoareTime program (fun z => z=bank D t R p (ButterflyAxisBank.word xs))
      (fun z => z=bank D (t+1) R p (ButterflyAxisBank.word (transformed xs)))
      (constant*logicalVolume D R p) := by
  have hsetup := (ButterflyAxisHeadersData.runs (a:=2) D t R p ht hR).consequence
    (fun _ h => h) (fun _ h => h) (ButterflyAxisHeadersBudget.cost_linear D t R p ht hR)
  have h0 := hoare_extend_eq (hoare_extend_eq (hoare_extend_eq hsetup
    (CountedLoopReuseAlphabet.one (ButterflyAxisBank.word xs) 0)) (SharedBank.empty 8 2))
    (SharedBank.empty ButterflyAxisPorts.count 2)
  have h1 := hoare_extend_eq (ButterflyAxisHeadersInstall.runs D t R p ht hR (ButterflyAxisBank.word xs))
    (SharedBank.empty ButterflyAxisPorts.count 2)
  have h2 := ButterflyInverseAxisPrepared.runs D t R p ht hR xs hw
  have h3 := hoare_extend_eq (ButterflyAxisHeadersInstall.cleans D t R p ht hR (ButterflyAxisBank.word (transformed xs)))
    (SharedBank.empty ButterflyAxisPorts.count 2)
  have h4 := hoare_extend_eq (hoare_extend_eq (hoare_extend_eq
    (ButterflyAxisHeadersCleanup.runs (a:=2) D t R p ht hR)
    (CountedLoopReuseAlphabet.one (ButterflyAxisBank.word (transformed xs)) 0)) (SharedBank.empty 8 2))
    (SharedBank.empty ButterflyAxisPorts.count 2)
  have hV := ButterflyAxisHeadersInstall.volume_pos D R p hR
  exact ((((h0.seq h1).seq h2).seq h3).seq h4).consequence (fun _ h => h) (fun _ h => h)
    (by unfold constant ButterflyAxisOriginal.constant; nlinarith)

end
end IntegerMultBounds.Machine.ButterflyInverseAxisOriginal
