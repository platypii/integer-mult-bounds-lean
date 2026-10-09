import IntegerMultBounds.Machine.ButterflySpectatorOriginal
import IntegerMultBounds.Machine.ButterflyInverseSpectatorGeometry

/-! A fixed native axis machine over all arbitrary outer row spectators.
Header multiplication, copied ports, routing, arithmetic and erasure are paid. -/
namespace IntegerMultBounds.Machine.ButterflyInverseSpectatorOriginal
noncomputable section
open ButterflySpectatorHeaders
open ButterflySpectatorGeometry
open ButterflyInverseSpectatorGeometry (applyAxis)
open ButterflyAxisHeadersArithmetic (compile scheduleCost)
open ButterflyAxisHeadersInstall (caller source)
open ButterflyAxisPrepared (commonPorts common_injective)

def prepared (rows D t R p : ℕ) (f : ℤ → Fin 6) :=
  (caller (output rows D t R p) f).append (FixedHeaderBankCopy.headerBank (words rows D t R p))
def bank (rows D t R p : ℕ) (f : ℤ → Fin 6) :=
  (ButterflyAxisHeadersInstall.input (initial rows D t R p) f).append
    (SharedBank.empty ButterflyAxisPorts.count 2)
def preparedBank (rows D t R p : ℕ) (f : ℤ → Fin 6) :=
  (prepared rows D t R p f).append (SharedBank.empty ButterflyAxisPorts.count 2)

def setup := extend (extend (extend (compile (a:=2) schedule).2 1) 8) ButterflyAxisPorts.count
def finish := extend (extend (extend (compile (a:=2) cleanup).2 1) 8) ButterflyAxisPorts.count
def install := extend (ButterflyAxisHeadersInstall.program (a:=2)) ButterflyAxisPorts.count
def uninstall := extend (ButterflyAxisHeadersInstall.cleanup (a:=2)) ButterflyAxisPorts.count
def program := seq (seq (seq (seq setup install) ButterflyInverseAxisPrepared.program) uninstall) finish

def axisCost (rows D t R p : ℕ) :=
  ButterflyAxisRun.constant*RecursiveInterchangeLayout.volume 2 (descriptor rows D t R p)
def cost (rows D t R p : ℕ) :=
  scheduleCost schedule (initial rows D t R p)+
  FixedHeaderBankCopy.cost (FixedHeaderBankCopy.ops 8) (words rows D t R p)+
  axisCost rows D t R p+FixedHeaderBankCopy.cleanupCost (t:=44) (words rows D t R p)+
  scheduleCost cleanup (output rows D t R p)+4

theorem source_tape (rows D t R p : ℕ) (f : ℤ → Fin 6) (i : Fin 8) :
    (caller (output rows D t R p) f).tape (source i)=RadixZeroFill.encodedBinary (words rows D t R p i) := by
  fin_cases i <;> rfl

theorem source_head (rows D t R p : ℕ) (f : ℤ → Fin 6) (i : Fin 8) :
    (caller (output rows D t R p) f).head (source i)=1 := by
  fin_cases i <;> rfl

theorem payload (rows D t R p : ℕ) (f : ℤ → Fin 6) :
    SharedBank.payload (prepared rows D t R p f) commonPorts=
      (CountedLoopReuseAlphabet.one f 0).append
        (ButterflyAxisPorts.headers (words rows D t R p 0) (words rows D t R p 1) (headers rows D t R p)) := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem frame (rows D t R p : ℕ) (f g : ℤ → Fin 6) :
    SharedBank.strip (prepared rows D t R p f) commonPorts=
      SharedBank.strip (prepared rows D t R p g) commonPorts := by
  apply congrArg₂ Tapes.mk
  · rfl
  · funext i
    by_cases hi : ∃ j,commonPorts j=i
    · simp only [hi,ite_true]
    · simp only [hi,ite_false]
      induction i using (Fin.addCases (m:=44) (n:=8)) with
      | left i =>
        induction i using (Fin.addCases (m:=43) (n:=1)) with
        | left i => simp [prepared,caller,Tapes.append]
        | right i => fin_cases i; exact (hi ⟨0,rfl⟩).elim
      | right i => simp [prepared,Tapes.append]

theorem axis_runs (rows D t R p : ℕ) (hr : 0<rows) (hR : 0<R)
    (xs : Fin (RecursiveInterchangeRows.groups 2 (descriptor rows D t R p)) → Fin 2 → Fin (ButterflyAxisHeadersData.lower t R) → ButterflyStreamData.Coefficient)
    (hw : ∀ h j k,(xs h j k).1.length=ButterflyGuard.width p D ∧ (xs h j k).2.length=ButterflyGuard.width p D) :
    HoareTime ButterflyInverseAxisPrepared.program
      (fun z => z=preparedBank rows D t R p (ButterflyAxisBank.word xs))
      (fun z => z=preparedBank rows D t R p (ButterflyAxisBank.word (ButterflyInverseAxisRouting.transformed xs)))
      (axisCost rows D t R p) := by
  have hh := ButterflyInverseAxisRun.runs_linear (headers rows D t R p) (headers_spec rows D t R p)
    (positive rows D t R p hr hR) (divides rows D t R p) xs (ButterflyGuard.width p D) hw
    (row_length rows D t R p) (words rows D t R p 0) (words rows D t R p 1)
    (paired_count rows D t R p) (stream_count rows D t R p) (canonical rows D t R p 0) (canonical rows D t R p 1)
  apply CleanSubbank.realizes (c:=9) (s:=ButterflyAxisPorts.count) (k:=52) ButterflyInverseAxisRun.program
    ButterflyAxisPorts.ports commonPorts ButterflyAxisPorts.injective common_injective
    (prepared rows D t R p (ButterflyAxisBank.word xs))
    (prepared rows D t R p (ButterflyAxisBank.word (ButterflyInverseAxisRouting.transformed xs))) _ _ _ ?_ ?_ ?_ ?_ ?_ hh
  · rw [ButterflyAxisPorts.payload,payload]
  · rw [ButterflyAxisPorts.payload,payload]
  · exact ButterflyAxisPorts.clean _ _ _ _
  · exact ButterflyAxisPorts.clean _ _ _ _
  · exact frame rows D t R p _ _

theorem runs (rows D t R p : ℕ) (hr : 0<rows) (ht : t<D) (hR : 0<R)
    (f : Array rows D R) (hw : Width rows D R p f) :
    HoareTime program (fun z => z=bank rows D t R p (ButterflyStreamData.full (fun _ => blank) 0 f))
      (fun z => z=bank rows D (t+1) R p (ButterflyStreamData.full (fun _ => blank) 0 (ButterflyInverseSpectatorGeometry.applyAxis rows D t R p ht f)))
      (cost rows D t R p) := by
  let xs := reshape rows D t R p ht f
  have h0 := hoare_extend_eq (hoare_extend_eq (hoare_extend_eq
    (ButterflySpectatorHeaders.runs rows D t R p ht hR hr)
    (CountedLoopReuseAlphabet.one (ButterflyAxisBank.word xs) 0)) (SharedBank.empty 8 2))
    (SharedBank.empty ButterflyAxisPorts.count 2)
  have h1 := hoare_extend_eq (FixedHeaderBankCopy.constructs (by decide) source (words rows D t R p)
    (caller (output rows D t R p) (ButterflyAxisBank.word xs))
    (source_tape rows D t R p _) (source_head rows D t R p _)) (SharedBank.empty ButterflyAxisPorts.count 2)
  have h2 := axis_runs rows D t R p hr hR xs (fun h j k => hw _)
  have h3 := hoare_extend_eq (FixedHeaderBankCopy.cleans (by decide)
    (caller (output rows D t R p) (ButterflyAxisBank.word (ButterflyInverseAxisRouting.transformed xs)))
    (words rows D t R p)) (SharedBank.empty ButterflyAxisPorts.count 2)
  have h4 := hoare_extend_eq (hoare_extend_eq (hoare_extend_eq
    (cleanup_runs rows D t R p)
    (CountedLoopReuseAlphabet.one (ButterflyAxisBank.word (ButterflyInverseAxisRouting.transformed xs)) 0))
    (SharedBank.empty 8 2)) (SharedBank.empty ButterflyAxisPorts.count 2)
  have hh := ((((h0.seq h1).seq h2).seq h3).seq h4).consequence (fun _ h => h) (fun _ h => h)
    (show _≤cost rows D t R p by unfold cost; omega)
  change HoareTime program (fun z => z=bank rows D t R p (ButterflyAxisBank.word xs))
    (fun z => z=bank rows D (t+1) R p (ButterflyAxisBank.word (ButterflyInverseAxisRouting.transformed xs))) _ at hh
  rw [source_word rows D t R p ht f,word_unshape rows D t R p ht] at hh
  exact hh

end
end IntegerMultBounds.Machine.ButterflyInverseSpectatorOriginal
