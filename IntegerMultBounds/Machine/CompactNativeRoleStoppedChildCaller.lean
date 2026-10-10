import IntegerMultBounds.Machine.CompactNativeRoleGuardedChildCaller
import IntegerMultBounds.Machine.CompactSpectatorLeafCountBudget

/-! Actual stopped positive node descriptors contain per-slot child width.
Expand header7 by real slots6, run the complete guarded role child, then
restore header7 exactly while preserving its derived native output. -/
namespace IntegerMultBounds.Machine.CompactNativeRoleStoppedChildCaller
noncomputable section
open CompactComplexRecursiveGeometry
open CompactGadgetReservationShape (Shape)
open CompactSpectatorLeafSetup (raw)
open ActiveRepairRankHeadersCommands (State)
open CompactNativeRoleSourcePorts (external)
open CompactSpectatorLeafGuardOriginal (Direction)
open CompactNativeRoleGuardedChildCaller (leafTapes setRole resultWord)
variable {c t : ℕ}

def nodeState (s : Shape) (rows ell p : ℕ) (rho : Fin s.chunk) {left k : ℕ}
    (visit : Visit s.active left (k+1)) (hactive : s.active≤s.axes)
    (pair : Networks.BinaryRowProgram.Op (Fin arity)) :=
  raw s rows ell p rho.val left (arity^k) arity (node rho visit hactive).right pair.source.val pair.target.val

theorem expanded_node (s : Shape) (rows ell p : ℕ) (rho : Fin s.chunk) {left k : ℕ}
    (visit : Visit s.active left (k+1)) (hactive : s.active≤s.axes)
    (pair : Networks.BinaryRowProgram.Op (Fin arity)) :
    CompactSpectatorLeafCountBudget.expanded (nodeState s rows ell p rho visit hactive pair) arity (arity^k)=
      raw s rows ell p rho.val left (arity^(k+1)) arity (node rho visit hactive).right pair.source.val pair.target.val := by
  funext i
  fin_cases i <;> simp [CompactSpectatorLeafCountBudget.expanded,nodeState,raw,
    ActiveRepairRankHeadersCommands.put,Function.update,pow_succ]

def countProgram (ops : List CompactChildHeadersArithmetic.Op) (t c : ℕ) :=
  CompactNativeRoleChildHeadersPorts.program ops t c

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
  seq (seq (extend (countProgram CompactSpectatorLeafCountBudget.expand t c) leafTapes)
    (CompactNativeRoleGuardedChildCaller.program dir t c j))
    (extend (countProgram CompactSpectatorLeafCountBudget.restore t c) leafTapes)

def cost (dir : Direction) (c : ℕ) (s : Shape) (rows ell p : ℕ) (rho : Fin s.chunk) {left k : ℕ}
    (visit : Visit s.active left (k+1)) (hactive : s.active≤s.axes)
    (pair : Networks.BinaryRowProgram.Op (Fin arity)) :=
  CompactChildHeadersArithmetic.scheduleCost CompactSpectatorLeafCountBudget.expand
    (nodeState s rows ell p rho visit hactive pair)+
  CompactNativeRoleGuardedChildCaller.cost dir c s rows ell p rho visit arity
    (node rho visit hactive).right pair.source.val pair.target.val+
  CompactChildHeadersArithmetic.scheduleCost CompactSpectatorLeafCountBudget.restore
    (CompactSpectatorLeafCountBudget.expanded (nodeState s rows ell p rho visit hactive pair) arity (arity^k))+2

theorem runs (dir : Direction) (old : Tapes t 2) (ht : 43<t) (s : Shape) (rows ell p : ℕ)
    (rho : Fin s.chunk) {left k : ℕ} (visit : Visit s.active left (k+1))
    (hactive : s.active≤s.axes) (pair : Networks.BinaryRowProgram.Op (Fin arity))
    (hd : c∣rows) (hc : 0<c) (hr : 0<rows) (hG : 0<s.guard) (hA : 0<s.axes) (hp : 2*s.bits≤p)
    (f : CompactSpectatorVisitGeometry.Array s rows ell)
    (hw : ∀ i,(f i).1.length=CompactNativeRoleHeaders.recordWidth s p ∧
      (f i).2.length=CompactNativeRoleHeaders.recordWidth s p) (j : Fin c) :
    HoareTime (program dir t c j)
      (fun v => v=CleanSubbank.bank (s:=leafTapes) (external old ht
        (nodeState s rows ell p rho visit hactive pair)
        (CompactNativeRoleReservedBridge.rolePayload s rows c ell hd f)))
      (fun v => v=CleanSubbank.bank (s:=leafTapes) (external old ht
        (nodeState s rows ell p rho visit hactive pair)
        (setRole (CompactNativeRoleReservedBridge.rolePayload s rows c ell hd f) j
          (resultWord dir s rows c ell p rho visit hd f j))))
      (cost dir c s rows ell p rho visit hactive pair) := by
  let st := nodeState s rows ell p rho visit hactive pair
  let payload := CompactNativeRoleReservedBridge.rolePayload s rows c ell hd f
  let out := setRole payload j (resultWord dir s rows c ell p rho visit hd f j)
  have he := CompactSpectatorLeafCountBudget.expand_runs (a:=2) st arity (arity^k) rfl rfl rfl (pow_pos (by decide) k)
  have h0 := hoare_extend_eq (numeric _ old ht _ _ payload _ he) (SharedBank.empty leafTapes 2)
  dsimp only [st] at h0
  rw [expanded_node] at h0
  have h1 := CompactNativeRoleGuardedChildCaller.runs dir old ht s rows ell p rho visit arity
    (node rho visit hactive).right pair.source.val pair.target.val hd hc hr hG hA hp f hw j
  have hs := CompactSpectatorLeafCountBudget.restore_runs (a:=2) st arity (arity^k) rfl rfl rfl (by decide : 0<arity)
  have h2 := hoare_extend_eq (numeric _ old ht _ _ out _ hs) (SharedBank.empty leafTapes 2)
  dsimp only [st] at h2
  rw [expanded_node] at h2
  exact ((h0.seq h1).seq h2).consequence (fun _ h => h) (fun _ h => h) (by unfold cost; rw [expanded_node]; omega)

end
end IntegerMultBounds.Machine.CompactNativeRoleStoppedChildCaller
