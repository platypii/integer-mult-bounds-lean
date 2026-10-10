import IntegerMultBounds.Machine.CompactNativeRoleChildGuardRuns
import IntegerMultBounds.Machine.NativePolynomialStageHeaders

/-! Paid original role child: row quotient, native codec payload synthesis,
baseline precision conversion, genuine guarded leaf, and complete reverse
metadata restoration. The leaf's derived output stays on its original role. -/
namespace IntegerMultBounds.Machine.CompactNativeRoleGuardedChildCaller
noncomputable section
open CompactGadgetReservationShape (Shape)
open CompactComplexRecursiveGeometry
open CompactSpectatorLeafSetup (raw)
open ActiveRepairRankHeadersCommands (State)
open CompactNativeRoleSourcePorts (external callerTapes)
open CompactSpectatorLeafGuardOriginal (Direction)
open SharedPlacementAlphabet (setTape)
variable {c t : ℕ}

abbrev leafTapes := CompactSpectatorLeafOriginal.tapes

def setRole (payload : Tapes (1+c) 2) (j : Fin c) (g : ℤ → Fin 6) :=
  setTape payload (Fin.natAdd 1 j) g 0

theorem external_setRole (old : Tapes t 2) (ht : 43<t) (st : State)
    (payload : Tapes (1+c) 2) (j : Fin c) (g : ℤ → Fin 6) :
    setTape (external old ht st payload) (CompactNativeRoleChildBank.roleSource t j) g 0=
      external old ht st (setRole payload j g) := by
  have h0 : (0 : Fin (1+c))≠Fin.natAdd 1 j := by
    intro h; have hv := congrArg Fin.val h; simp at hv; omega
  have hroles : CompactNativeRoleSourcePorts.roles (setRole payload j g)=
      setTape (CompactNativeRoleSourcePorts.roles payload) j g 0 := by
    apply congrArg₂ Tapes.mk <;> funext i
    all_goals have hi : (⟨i.val+1,by omega⟩ : Fin (1+c))=Fin.natAdd 1 i := by apply Fin.ext; dsimp; omega
    all_goals simp [CompactNativeRoleSourcePorts.roles,hi,setRole,setTape,Function.update]
  have hsource : CompactNativeRoleSourcePorts.replaceSource old ht (setRole payload j g)=
      CompactNativeRoleSourcePorts.replaceSource old ht payload := by
    apply congrArg₂ Tapes.mk <;> funext i
    all_goals simp [setRole,setTape,Function.update,h0]
  unfold external CompactNativeRoleChildBank.roleSource
  rw [SharedPlacementAlphabet.setTape_append_right,hroles,hsource]

def payloadProgram (t c : ℕ) := Placement.placed (NativePolynomialStageHeaders.program (a:=2))
  (CompactNativeRoleChildHeadersPorts.placement t c)
def payloadRestore (t c : ℕ) := Placement.placed
  (ButterflyAxisHeadersArithmetic.compile (a:=2) NativePolynomialStageHeaders.restore).2
  (CompactNativeRoleChildHeadersPorts.placement t c)

private theorem numeric {q : ℕ} (M : Program 43 q 2) (old : Tapes t 2) (ht : 43<t)
    (st su : State) (payload : Tapes (1+c) 2) (cost : ℕ)
    (h : HoareTime M (fun v => v=ActiveRepairRankHeadersCommands.bank st)
      (fun v => v=ActiveRepairRankHeadersCommands.bank su) cost) :
    HoareTime (Placement.placed M (CompactNativeRoleChildHeadersPorts.placement t c))
      (fun v => v=external old ht st payload) (fun v => v=external old ht su payload) cost := by
  have hh := Placement.hoare_at h (CompactNativeRoleChildHeadersPorts.placement t c)
    (external old ht st payload) (CompactNativeRoleChildHeadersPorts.active old ht st payload)
  apply hh.consequence (fun _ hv => hv) _ le_rfl
  rintro v ⟨small,rfl,rfl⟩
  rw [Placement.replace,CompactNativeRoleChildHeadersPorts.extra old ht st su payload,
    ←CompactNativeRoleChildHeadersPorts.active old ht su payload,Placement.view]

def program (dir : Direction) (t c : ℕ) (j : Fin c) :=
  seq (seq (seq (seq (seq (seq
    (extend (CompactNativeRoleChildHeadersPorts.program (CompactNativeRoleChildBank.prepare c) t c) leafTapes)
    (extend (payloadProgram t c) leafTapes))
    (extend (CompactNativeRoleChildPrecision.program CompactNativeRoleChildPrecision.prepare t c) leafTapes))
    (CompactNativeRoleChildGuardRuns.program dir t j))
    (extend (CompactNativeRoleChildPrecision.program CompactNativeRoleChildPrecision.restore t c) leafTapes))
    (extend (payloadRestore t c) leafTapes))
    (extend (CompactNativeRoleChildHeadersPorts.program (CompactNativeRoleChildBank.restore c) t c) leafTapes)

def cost (dir : Direction) (c : ℕ) (s : Shape) (rows ell p : ℕ) (rho : Fin s.chunk)
    {left k : ℕ} (visit : Visit s.active left k) (slots right src dst : ℕ) :=
  CompactChildHeadersArithmetic.scheduleCost (CompactNativeRoleChildBank.prepare c)
    (raw s rows ell p rho.val left (arity^k) slots right src dst)+
  NativePolynomialStageHeaders.cost s (rows/c) ell p rho.val left (arity^k) slots right src dst+
  ButterflyAxisHeadersArithmetic.scheduleCost CompactNativeRoleChildPrecision.prepare
    (raw (NativePolynomialStageShape.shape s ell p) (rows/c) ell p rho.val left (arity^k) slots right src dst)+
  CompactSpectatorLeafGuardOriginal.phaseCost dir (NativePolynomialStageShape.shape s ell p) (rows/c) ell
    (p-2*s.bits) rho visit slots right src dst+
  ButterflyAxisHeadersArithmetic.scheduleCost CompactNativeRoleChildPrecision.restore
    (CompactNativeRoleChildPrecision.baseline (NativePolynomialStageShape.shape s ell p) (rows/c) ell p
      rho.val left (arity^k) slots right src dst)+
  ButterflyAxisHeadersArithmetic.scheduleCost NativePolynomialStageHeaders.restore
    (NativePolynomialStageHeaders.prepared s (rows/c) ell p rho.val left (arity^k) slots right src dst)+
  CompactChildHeadersArithmetic.scheduleCost (CompactNativeRoleChildBank.restore c)
    (raw s (rows/c) ell p rho.val left (arity^k) slots right src dst)+6

def resultWord (dir : Direction) (s : Shape) (rows c ell p : ℕ) (rho : Fin s.chunk)
    {left k : ℕ} (visit : Visit s.active left k) (hd : c∣rows)
    (f : CompactSpectatorVisitGeometry.Array s rows ell) (j : Fin c) :=
  CompactSpectatorLeafAxis.word (CompactSpectatorLeafGuardOriginal.result dir
    (NativePolynomialStageShape.shape s ell p) (rows/c) ell (p-2*s.bits) rho visit
    (CompactNativeRoleReservedBridge.role s rows c ell hd f j))

theorem runs (dir : Direction) (old : Tapes t 2) (ht : 43<t) (s : Shape) (rows ell p : ℕ)
    (rho : Fin s.chunk) {left k : ℕ} (visit : Visit s.active left k)
    (slots right src dst : ℕ) (hd : c∣rows) (hc : 0<c) (hr : 0<rows)
    (hG : 0<s.guard) (hA : 0<s.axes) (hp : 2*s.bits≤p)
    (f : CompactSpectatorVisitGeometry.Array s rows ell)
    (hw : ∀ i,(f i).1.length=CompactNativeRoleHeaders.recordWidth s p ∧
      (f i).2.length=CompactNativeRoleHeaders.recordWidth s p) (j : Fin c) :
    HoareTime (program dir t c j)
      (fun v => v=CleanSubbank.bank (s:=leafTapes) (external old ht
        (raw s rows ell p rho.val left (arity^k) slots right src dst)
        (CompactNativeRoleReservedBridge.rolePayload s rows c ell hd f)))
      (fun v => v=CleanSubbank.bank (s:=leafTapes) (external old ht
        (raw s rows ell p rho.val left (arity^k) slots right src dst)
        (setRole (CompactNativeRoleReservedBridge.rolePayload s rows c ell hd f) j
          (resultWord dir s rows c ell p rho visit hd f j))))
      (cost dir c s rows ell p rho visit slots right src dst) := by
  let payload := CompactNativeRoleReservedBridge.rolePayload s rows c ell hd f
  let out := setRole payload j (resultWord dir s rows c ell p rho visit hd f j)
  have hK : 0<s.chunk := by have := rho.isLt; omega
  have h0 := hoare_extend_eq (CompactNativeRoleChildHeadersPorts.prepare_runs old ht s rows ell p rho.val
    left (arity^k) slots right src dst payload hc) (SharedBank.empty leafTapes 2)
  have h1 := hoare_extend_eq (numeric _ old ht _ _ payload _
    (NativePolynomialStageHeaders.runs (a:=2) s (rows/c) ell p rho.val left (arity^k) slots right src dst hG hA hK))
    (SharedBank.empty leafTapes 2)
  have h2 := hoare_extend_eq (CompactNativeRoleChildPrecisionSaved.exterior_prepare old ht
    (NativePolynomialStageShape.shape s ell p) (rows/c) ell p rho.val left (arity^k) slots right src dst s.payload
    hG hA hK hp payload) (SharedBank.empty leafTapes 2)
  have h3 := CompactNativeRoleChildGuardRuns.phase_runs dir old ht (NativePolynomialStageShape.shape s ell p)
    rows ell p rho visit slots right src dst s.payload hd hc hr hG hA hp f hw j
  dsimp only at h3
  rw [external_setRole] at h3
  have h4 := hoare_extend_eq (CompactNativeRoleChildPrecisionSaved.exterior_restore old ht
    (NativePolynomialStageShape.shape s ell p) (rows/c) ell p rho.val left (arity^k) slots right src dst s.payload out)
    (SharedBank.empty leafTapes 2)
  have h5 := hoare_extend_eq (numeric _ old ht _ _ out _
    (NativePolynomialStageHeaders.restore_runs (a:=2) s (rows/c) ell p rho.val left (arity^k) slots right src dst))
    (SharedBank.empty leafTapes 2)
  have h6 := hoare_extend_eq (CompactNativeRoleChildHeadersPorts.restore_runs old ht s rows ell p rho.val
    left (arity^k) slots right src dst out hd hc hr) (SharedBank.empty leafTapes 2)
  exact ((((((h0.seq h1).seq h2).seq h3).seq h4).seq h5).seq h6).consequence
    (fun _ h => h) (fun _ h => h) (by unfold cost; simp only [NativePolynomialStageShape.bits]; omega)

end
end IntegerMultBounds.Machine.CompactNativeRoleGuardedChildCaller
