import IntegerMultBounds.Machine.ButterflyAxisPrepared
import IntegerMultBounds.Machine.ButterflyAxisHeadersCleanup

/-! One whole native butterfly axis from original D,t,R,p and a sole coefficient
stream. All derived headers, their copied ports and the axis work bank start
blank and are physically erased. The actual selected-position header advances
by one, enabling a fixed runtime-counted body across successive axes. -/
namespace IntegerMultBounds.Machine.ButterflyAxisOriginal
noncomputable section
open ButterflyAxisHeadersData ButterflyAxisHeadersGeometry ButterflyAxisHeadersBudget
open ButterflyStreamData (Coefficient)
open ButterflyStreamSemantics (transformed)

abbrev count := ButterflyAxisPrepared.count

def bank (D t R p : ℕ) (f : ℤ → Fin 6) :=
  (ButterflyAxisHeadersInstall.input (initial D t R p) f).append
    (SharedBank.empty ButterflyAxisPorts.count 2)

def setup := extend (extend (extend (ButterflyAxisHeadersArithmetic.compile (a:=2)
  ButterflyAxisHeadersData.schedule).2 1) 8) ButterflyAxisPorts.count
def install := extend (ButterflyAxisHeadersInstall.program (a:=2)) ButterflyAxisPorts.count
def uninstall := extend (ButterflyAxisHeadersInstall.cleanup (a:=2)) ButterflyAxisPorts.count
def finish := extend (extend (extend (ButterflyAxisHeadersArithmetic.compile (a:=2)
  ButterflyAxisHeadersCleanup.schedule).2 1) 8) ButterflyAxisPorts.count
def program := seq (seq (seq (seq setup install) ButterflyAxisPrepared.program) uninstall) finish

def constant := ButterflyAxisHeadersBudget.constant+ButterflyAxisRun.constant+3656

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
  have h2 := ButterflyAxisPrepared.runs D t R p ht hR xs hw
  have h3 := hoare_extend_eq (ButterflyAxisHeadersInstall.cleans D t R p ht hR (ButterflyAxisBank.word (transformed xs)))
    (SharedBank.empty ButterflyAxisPorts.count 2)
  have h4 := hoare_extend_eq (hoare_extend_eq (hoare_extend_eq
    (ButterflyAxisHeadersCleanup.runs (a:=2) D t R p ht hR)
    (CountedLoopReuseAlphabet.one (ButterflyAxisBank.word (transformed xs)) 0)) (SharedBank.empty 8 2))
    (SharedBank.empty ButterflyAxisPorts.count 2)
  have hV := ButterflyAxisHeadersInstall.volume_pos D R p hR
  exact ((((h0.seq h1).seq h2).seq h3).seq h4).consequence (fun _ h => h) (fun _ h => h)
    (by unfold constant; nlinarith)

end
end IntegerMultBounds.Machine.ButterflyAxisOriginal
