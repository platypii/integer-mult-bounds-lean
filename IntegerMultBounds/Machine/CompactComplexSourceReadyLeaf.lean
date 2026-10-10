import IntegerMultBounds.Machine.CompactComplexSourceReadyLeafCodec
import IntegerMultBounds.Machine.NativePolynomialStageHeaders

/-! Complete source-ready directional leaf lifecycle. Polynomial codec width
and baseline precision are genuinely computed from retained raw metadata, the
actual source executes the leaf, and all original node descriptors are restored.
There is no role selection, row division, row multiplication or source merge. -/
namespace IntegerMultBounds.Machine.CompactComplexSourceReadyLeaf
noncomputable section
open CompactGadgetReservationShape (Shape)
open CompactComplexRecursiveGeometry
open CompactComplexSourceReadyLeafPhase (publicTapes privateTapes source ready)
open CompactComplexSourceReadyLeafCodec (headers numericProgram numeric_runs headers_active
  headers_source headers_headers headers_set_source headers_original active_set_source)
open CompactComplexNonleafRoleEntry (headerPlacement)
open CompactComplexNonleafRoleSourceReturn (base)
open CompactSpectatorLeafGuardOriginal (Direction)
open SharedPlacementAlphabet (setTape)
open ButterflyAxisHeadersArithmetic (compile scheduleCost)
variable {s c : ℕ}

def program (dir : Direction) := seq (seq (seq (seq
  (extend (numericProgram (s:=s) (c:=c) (NativePolynomialStageHeaders.program (a:=2))) privateTapes)
  (extend (numericProgram (s:=s) (c:=c) (compile (a:=2) CompactNativeRoleChildPrecision.prepare).2) privateTapes))
  (CompactComplexSourceReadyLeafPhase.program (s:=s) (c:=c) dir))
  (extend (numericProgram (s:=s) (c:=c) (compile (a:=2) CompactNativeRoleChildPrecision.restore).2) privateTapes))
  (extend (numericProgram (s:=s) (c:=c) (compile (a:=2) NativePolynomialStageHeaders.restore).2) privateTapes)

def cost (dir : Direction) (sh : Shape) (rows ell p : ℕ) (rho : Fin sh.chunk)
    {left k : ℕ} (visit : Visit sh.active left k) (slots right src dst : ℕ) :=
  NativePolynomialStageHeaders.cost sh rows ell p rho.val left (arity^k) slots right src dst+
  scheduleCost CompactNativeRoleChildPrecision.prepare
    (NativePolynomialStageHeaders.prepared sh rows ell p rho.val left (arity^k) slots right src dst)+
  CompactSpectatorLeafGuardOriginal.phaseCost dir (NativePolynomialStageShape.shape sh ell p)
    rows ell (p-2*sh.bits) rho visit slots right src dst+
  scheduleCost CompactNativeRoleChildPrecision.restore
    (ActiveRepairRankHeadersCommands.put
      (CompactNativeRoleChildPrecision.baseline (NativePolynomialStageShape.shape sh ell p)
        rows ell p rho.val left (arity^k) slots right src dst) 26 sh.payload)+
  scheduleCost NativePolynomialStageHeaders.restore
    (NativePolynomialStageHeaders.prepared sh rows ell p rho.val left (arity^k) slots right src dst)+4

/-- The actual whole-bank output changes only the source word. Metadata,
roles, controllers, ancestor frames, scratch7 and borrowed leaf work are restored. -/
theorem runs (dir : Direction) (sh : Shape) (rows ell p : ℕ) (rho : Fin sh.chunk)
    {left k : ℕ} (visit : Visit sh.active left k) (slots right src dst : ℕ)
    (v : Tapes (publicTapes s c) 2)
    (f : CompactSpectatorVisitGeometry.Array (NativePolynomialStageShape.shape sh ell p) rows ell)
    (hG : 0<sh.guard) (hA : 0<sh.axes) (hr : 0<rows) (hp : 2*sh.bits≤p)
    (hw : ∀ i,(f i).1.length=CompactNativeRoleHeaders.recordWidth sh p ∧
      (f i).2.length=CompactNativeRoleHeaders.recordWidth sh p)
    (hraw : Placement.active headerPlacement (base v)=ActiveRepairRankHeadersCommands.bank
      (CompactSpectatorLeafSetup.raw sh rows ell p rho.val left (arity^k) slots right src dst))
    (hsource : v.head source=0 ∧ v.tape source=CompactSpectatorLeafAxis.word f) :
    HoareTime (program dir) (fun z => z=ready v)
      (fun z => z=ready (setTape v source
        (CompactSpectatorLeafAxis.word (CompactSpectatorLeafGuardOriginal.result dir
          (NativePolynomialStageShape.shape sh ell p) rows ell (p-2*sh.bits) rho visit f)) 0))
      (cost dir sh rows ell p rho visit slots right src dst) := by
  let shape := NativePolynomialStageShape.shape sh ell p
  let raw := CompactSpectatorLeafSetup.raw sh rows ell p rho.val left (arity^k) slots right src dst
  let prepared := NativePolynomialStageHeaders.prepared sh rows ell p rho.val left (arity^k) slots right src dst
  let baseline := ActiveRepairRankHeadersCommands.put
    (CompactNativeRoleChildPrecision.baseline shape rows ell p rho.val left (arity^k) slots right src dst) 26 sh.payload
  let g := CompactSpectatorLeafAxis.word
    (CompactSpectatorLeafGuardOriginal.result dir shape rows ell (p-2*sh.bits) rho visit f)
  have hK : 0<sh.chunk := by have := rho.isLt;omega
  have h0 := hoare_extend_eq (numeric_runs _ v raw prepared _ hraw
    (NativePolynomialStageHeaders.runs sh rows ell p rho.val left (arity^k) slots right src dst hG hA hK))
    (SharedBank.empty privateTapes 2)
  have h1 := hoare_extend_eq (numeric_runs _ (headers v prepared) prepared baseline _ (headers_active _ _)
    (CompactNativeRoleChildPrecisionSaved.prepare_runs shape rows ell p rho.val left (arity^k) slots right src dst
      sh.payload hG hA hK hp)) (SharedBank.empty privateTapes 2)
  rw [headers_headers] at h1
  have hwidth : CompactNativeRoleHeaders.recordWidth sh p=
      ButterflyGuard.width (ButterflyIndependentGuardHeaders.reservation sh.bits (p-2*sh.bits)) sh.bits := by
    unfold CompactNativeRoleHeaders.recordWidth ButterflyGuard.width ButterflyGuard.halfWidth
      ButterflyIndependentGuardHeaders.reservation
    omega
  have hf : ButterflySpectatorSemantics.Width rows shape.bits (2^ell) (p-2*sh.bits) f := by
    intro i
    change (f i).1.length=ButterflyGuard.width (ButterflyIndependentGuardHeaders.reservation sh.bits (p-2*sh.bits)) sh.bits ∧
      (f i).2.length=ButterflyGuard.width (ButterflyIndependentGuardHeaders.reservation sh.bits (p-2*sh.bits)) sh.bits
    rw [←hwidth]
    exact hw i
  have hs : (headers v baseline).head source=0 ∧
      (headers v baseline).tape source=CompactSpectatorLeafAxis.word f := by
    rw [(headers_source v baseline).1,(headers_source v baseline).2]
    exact hsource
  have h2 := CompactComplexSourceReadyLeafPhase.runs dir shape rows ell (p-2*sh.bits) rho visit
    slots right src dst p sh.payload (headers v baseline) f hG hA hr hf (headers_active _ _) hs
  have h3 := hoare_extend_eq (numeric_runs _ (setTape (headers v baseline) source g 0) baseline prepared _
    ((active_set_source _ _).trans (headers_active _ _))
    (CompactNativeRoleChildPrecisionSaved.restore_runs shape rows ell p rho.val left (arity^k) slots right src dst sh.payload))
    (SharedBank.empty privateTapes 2)
  rw [headers_set_source,headers_headers] at h3
  have h4 := hoare_extend_eq (numeric_runs _ (setTape (headers v prepared) source g 0) prepared raw _
    ((active_set_source _ _).trans (headers_active _ _))
    (NativePolynomialStageHeaders.restore_runs sh rows ell p rho.val left (arity^k) slots right src dst))
    (SharedBank.empty privateTapes 2)
  rw [headers_set_source,headers_headers,headers_original v raw hraw] at h4
  have h := (((h0.seq h1).seq h2).seq h3).seq h4
  exact h.consequence (fun _ hz => hz) (fun _ hz => hz) (by unfold cost;dsimp only [shape,NativePolynomialStageHeaders.prepared];omega)

end
end IntegerMultBounds.Machine.CompactComplexSourceReadyLeaf
