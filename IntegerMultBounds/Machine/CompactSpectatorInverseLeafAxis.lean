import IntegerMultBounds.Machine.CompactSpectatorLeafHeaders
import IntegerMultBounds.Machine.ButterflySpectatorPorts
import IntegerMultBounds.Machine.ButterflyInverseSpectatorOriginal

/-! One actual stopped-call leaf body derives its selected global bit,
executes the spectator-preserving native butterfly, reclaims all derived
headers and advances its chunk ordinal. No body execution callback is used. -/
namespace IntegerMultBounds.Machine.CompactSpectatorInverseLeafAxis
noncomputable section
open CompactGadgetReservationShape (Shape)
open CompactComplexRecursiveGeometry
open CompactSpectatorLeafHeaders
open CompactSpectatorVisitGeometry (Array)

def common (st : ActiveRepairRankHeadersCommands.State) (f : ℤ → Fin 6) :=
  (ActiveRepairRankHeadersCommands.bank st).append (CountedLoopReuseAlphabet.one f 0)
def bank (st : ActiveRepairRankHeadersCommands.State) (f : ℤ → Fin 6) :=
  (common st f).append (SharedBank.empty ButterflySpectatorPorts.count 2)
def word {s : Shape} {rows ell : ℕ} (f : Array s rows ell) := ButterflyStreamData.full (fun _ => blank) 0 f

def focus : Fin 6 → Fin 44 := ![0,12,16,3,1,43]
theorem focus_injective : Function.Injective focus := by decide

def axisProgram := Placement.placed ButterflyInverseSpectatorOriginal.program
  (CleanSubbank.placement ButterflySpectatorPorts.ports focus focus_injective)
def headerProgram (ops : List ButterflyAxisHeadersArithmetic.Op) :=
  extend (extend (ButterflyAxisHeadersArithmetic.compile (a:=2) ops).2 1) ButterflySpectatorPorts.count
def program := seq (seq (headerProgram setup) axisProgram) (headerProgram cleanup)

theorem payload (s : Shape) (rows ell p rho ordinal count shift : ℕ) (f : ℤ → Fin 6) :
    SharedBank.payload (common (prepared s rows ell p rho ordinal count shift) f) focus=
      ButterflySpectatorPorts.payload rows s.bits (selected s rho ordinal+shift) (2^ell) p f := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem frame (s : Shape) (rows ell p rho ordinal count : ℕ) (f g : ℤ → Fin 6) :
    SharedBank.strip (common (prepared s rows ell p rho ordinal count 0) f) focus=
      SharedBank.strip (common (prepared s rows ell p rho ordinal count 1) g) focus := by
  apply congrArg₂ Tapes.mk
  · funext i; fin_cases i <;> rfl
  · funext i
    by_cases hi : ∃ j,focus j=i
    · simp only [hi,ite_true]
    · simp only [hi,ite_false]
      fin_cases i
      all_goals first | exact (hi ⟨1,rfl⟩).elim | exact (hi ⟨5,rfl⟩).elim | rfl

def result (s : Shape) (rows ell p : ℕ) (rho : Fin s.chunk) {left k : ℕ}
    (visit : Visit s.active left k) (i : Fin (arity^k)) (f : Array s rows ell) :=
  ButterflyInverseSpectatorGeometry.applyAxis rows s.bits (selected s rho.val (left+i.val)) (2^ell) p
    (by simpa [selected,CompactSpectatorVisitGeometry.selected] using CompactSpectatorVisitGeometry.selected_lt rho visit i) f

theorem axis_runs (s : Shape) (rows ell p : ℕ) (hr : 0<rows) (rho : Fin s.chunk)
    {left k : ℕ} (visit : Visit s.active left k) (i : Fin (arity^k)) (f : Array s rows ell)
    (hw : ButterflySpectatorGeometry.Width rows s.bits (2^ell) p f) :
    HoareTime axisProgram
      (fun v => v=bank (prepared s rows ell p rho.val (left+i.val) (arity^k) 0) (word f))
      (fun v => v=bank (prepared s rows ell p rho.val (left+i.val) (arity^k) 1)
        (word (result s rows ell p rho visit i f)))
      (ButterflyInverseSpectatorOriginal.cost rows s.bits (selected s rho.val (left+i.val)) (2^ell) p) := by
  have hh := ButterflyInverseSpectatorOriginal.runs rows s.bits (selected s rho.val (left+i.val))
    (2^ell) p hr (by simpa [selected,CompactSpectatorVisitGeometry.selected] using
      CompactSpectatorVisitGeometry.selected_lt rho visit i) (pow_pos (by decide) _) f hw
  change HoareTime ButterflyInverseSpectatorOriginal.program
    (fun v => v=ButterflyInverseSpectatorOriginal.bank rows s.bits (selected s rho.val (left+i.val)) (2^ell) p (word f))
    (fun v => v=ButterflyInverseSpectatorOriginal.bank rows s.bits (selected s rho.val (left+i.val)+1) (2^ell) p
      (word (result s rows ell p rho visit i f))) _ at hh
  apply CleanSubbank.realizes (c:=6) (s:=ButterflySpectatorPorts.count) (k:=44) ButterflyInverseSpectatorOriginal.program
    ButterflySpectatorPorts.ports focus ButterflySpectatorPorts.injective focus_injective
    (common (prepared s rows ell p rho.val (left+i.val) (arity^k) 0) (word f))
    (common (prepared s rows ell p rho.val (left+i.val) (arity^k) 1) (word (result s rows ell p rho visit i f)))
    _ _ _ ?_ ?_ ?_ ?_ ?_ hh
  · exact (payload s rows ell p rho.val (left+i.val) (arity^k) 0 (word f)).symm
  · exact (payload s rows ell p rho.val (left+i.val) (arity^k) 1 (word (result s rows ell p rho visit i f))).symm
  · exact ButterflySpectatorPorts.clean _ _ _ _ _ _
  · exact ButterflySpectatorPorts.clean _ _ _ _ _ _
  · exact frame _ _ _ _ _ _ _ _ _

def cost (s : Shape) (rows ell p rho ordinal count : ℕ) :=
  ButterflyAxisHeadersArithmetic.scheduleCost setup (initial s rows ell p rho ordinal count)+
  ButterflyInverseSpectatorOriginal.cost rows s.bits (selected s rho ordinal) (2^ell) p+
  ButterflyAxisHeadersArithmetic.scheduleCost cleanup (prepared s rows ell p rho ordinal count 1)+2

theorem runs_visit (s : Shape) (rows ell p : ℕ) (hr : 0<rows) (rho : Fin s.chunk)
    {left k : ℕ} (visit : Visit s.active left k) (i : Fin (arity^k)) (f : Array s rows ell)
    (hw : ButterflySpectatorGeometry.Width rows s.bits (2^ell) p f) :
    HoareTime program
      (fun v => v=bank (initial s rows ell p rho.val (left+i.val) (arity^k)) (word f))
      (fun v => v=bank (initial s rows ell p rho.val (left+i.val+1) (arity^k))
        (word (result s rows ell p rho visit i f)))
      (cost s rows ell p rho.val (left+i.val) (arity^k)) := by
  have hf := visit.fits
  have hi := i.isLt
  have hK : 0<s.chunk := by have := rho.isLt; omega
  have h0 := hoare_extend_eq (hoare_extend_eq
    (setup_runs s rows ell p rho.val (left+i.val) (arity^k) (by omega) hK)
    (CountedLoopReuseAlphabet.one (word f) 0)) (SharedBank.empty ButterflySpectatorPorts.count 2)
  have h1 := axis_runs s rows ell p hr rho visit i f hw
  have h2 := hoare_extend_eq (hoare_extend_eq
    (cleanup_runs s rows ell p rho.val (left+i.val) (arity^k))
    (CountedLoopReuseAlphabet.one (word (result s rows ell p rho visit i f)) 0))
    (SharedBank.empty ButterflySpectatorPorts.count 2)
  exact ((h0.seq h1).seq h2).consequence (fun _ h => h) (fun _ h => h) (by unfold cost; omega)

end
end IntegerMultBounds.Machine.CompactSpectatorInverseLeafAxis
