import IntegerMultBounds.Machine.ProgramPairSequence
import IntegerMultBounds.Machine.NativeEndpointCharacterCanonicalSourceReady
import IntegerMultBounds.Machine.NativeEndpointCharacterPath
import IntegerMultBounds.Machine.NativeUniformPolynomialRotationSourceReady
import IntegerMultBounds.Machine.CompactComplexSourceReadyEndpointRoleExchange

/-! Fixed actual sink signs, column phase, X negation and named X/Y exchange
compose on one recursive bank and reclaim the same borrowed leaf storage. -/
namespace IntegerMultBounds.Machine.CompactComplexSourceReadySinkCorrections
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters (Stage)
open CompactSpectatorVisitGeometry (Array)
open CompactComplexRolePhaseSite (roleCount)
open CompactComplexEndpointRoleExchange (Wire)
variable {s : ℕ} {sh : Shape}
attribute [local irreducible] seq HoareTime roleCount CompactComplexScalarCountLifecycle.roleDivisor
  NativeEndpointCharacterCanonicalSourceReady.program
  NativeUniformPolynomialRotationSourceReady.program
  CompactComplexSourceReadyEndpointRoleExchange.program CompactComplexEndpointRoleExchange.program

def signed (v : Stage sh) (hslots : v.slots=NativeEndpointCharacterRoles.arity)
    (ell p : ℕ) {rows : ℕ} (before : Wire → Array sh rows ell) :=
  NativeEndpointCharacterNamedBank.data true v hslots ell p before

def phased (v : Stage sh) (hslots : v.slots=NativeEndpointCharacterRoles.arity)
    (ell p : ℕ) {rows : ℕ} (before : Wire → Array sh rows ell) :=
  NativeUniformPolynomialRotationNamedBank.data false v (signed v hslots ell p before)

def negated (v : Stage sh) (hslots : v.slots=NativeEndpointCharacterRoles.arity)
    (ell p : ℕ) {rows : ℕ} (before : Wire → Array sh rows ell) :=
  NativeUniformPolynomialRotationNamedBank.data true v (phased v hslots ell p before)

def data (v : Stage sh) (hslots : v.slots=NativeEndpointCharacterRoles.arity)
    (ell p : ℕ) {rows : ℕ} (before : Wire → Array sh rows ell) :=
  fun a => negated v hslots ell p before (Networks.ComplexFramedExecution.route a)

theorem signed_width (v : Stage sh) (hslots : v.slots=NativeEndpointCharacterRoles.arity)
    (ell p width : ℕ) {rows : ℕ} (before : Wire → Array sh rows ell)
    (hw : ∀ a i,(before a i).1.length=width ∧ (before a i).2.length=width) :
    ∀ a i,(signed v hslots ell p before a i).1.length=width ∧
      (signed v hslots ell p before a i).2.length=width := by
  intro a i
  rcases a with a | a | a
  · exact hw _ _
  · exact NativeEndpointCharacterPath.width true v hslots ell p before a width (hw _) i
  · exact hw _ _

theorem uniform_width (negative : Bool) (v : Stage sh) (width : ℕ)
    {rows ell : ℕ} (before : Wire → Array sh rows ell)
    (hw : ∀ a i,(before a i).1.length=width ∧ (before a i).2.length=width) :
    ∀ a i,(NativeUniformPolynomialRotationNamedBank.data negative v before a i).1.length=width ∧
      (NativeUniformPolynomialRotationNamedBank.data negative v before a i).2.length=width := by
  intro a i
  cases negative <;> rcases a with a | a | a
  all_goals first | exact hw _ _ | exact UnitPhasePolynomialArray.result_width _ _ width (hw _) i

def exchange : Σ q,Program (CompactComplexSourceReadyScalarWorkspace.tapes s roleCount) q 2 :=
  ⟨_,CompactComplexSourceReadyOrientedControls.widen (s:=s) (c:=roleCount)
    (CompactComplexSourceReadyNonleafContraction.placed (s:=s) (c:=roleCount)
      (CompactComplexEndpointRoleExchange.program (s:=10+s) (u:=10)).2)⟩

def program : Σ q,Program (CompactComplexSourceReadyScalarWorkspace.tapes s roleCount) q 2 :=
  ProgramPairSequence.pair
    (NativeEndpointCharacterCanonicalSourceReady.program (s:=s)
      (w:=CompactComplexSourceReadyScalarWorkspace.scratch) true)
    (ProgramPairSequence.pair
      (NativeUniformPolynomialRotationSourceReady.program (s:=s)
        (w:=CompactComplexSourceReadyScalarWorkspace.scratch) false)
      (ProgramPairSequence.pair
        (NativeUniformPolynomialRotationSourceReady.program (s:=s)
          (w:=CompactComplexSourceReadyScalarWorkspace.scratch) true)
        (exchange (s:=s))))

def constant := NativeEndpointCharacterCanonicalRoles.constant
    CompactComplexScalarCountLifecycle.roleDivisor+
  2*NativeUniformPolynomialRotationRoles.constant+CompactComplexEndpointRoleExchange.constant+3

private theorem payload_cast {rows next ell : ℕ} (he : rows=next)
    (master : ℤ → Fin 6) (masterHead : ℤ) (before : Wire → Array sh next ell) :
    CompactComplexEndpointRoleExchange.payload master masterHead
      (fun a i => before a (Fin.cast (congrArg (fun r => r*(2^sh.bits*2^ell)) he) i))=
      CompactComplexEndpointRoleExchange.payload master masterHead before := by
  cases he
  rfl

private theorem signed_payload_cast {rows next ell : ℕ} (he : rows=next)
    (v : Stage sh) (hslots : v.slots=NativeEndpointCharacterRoles.arity) (p : ℕ)
    (master : ℤ → Fin 6) (masterHead : ℤ) (before : Wire → Array sh next ell) :
    CompactComplexEndpointRoleExchange.payload master masterHead
      (NativeEndpointCharacterNamedBank.data true v hslots ell p
        (fun a i => before a (Fin.cast (congrArg (fun r => r*(2^sh.bits*2^ell)) he) i)))=
      CompactComplexEndpointRoleExchange.payload master masterHead
        (signed v hslots ell p before) := by
  cases he
  rfl

theorem compose_runs (v : Stage sh) (parentRows ell p : ℕ)
    (hslots : v.slots=NativeEndpointCharacterRoles.arity) (hG : 0<sh.guard) (hA : 0<sh.axes)
    (hGK : sh.guard+1≤sh.chunk) (hpay : sh.payload=1)
    (hr : 0<parentRows/roleCount)
    (control : Tapes 43 2) (queue : Tapes 1 2)
    (scalar : ActiveRepairRankHeadersCommands.State) (tail : Tapes 22 2)
    (storage : Tapes (10+s) 2) (master : ℤ → Fin 6) (masterHead : ℤ)
    (before : Wire → Array sh (parentRows/roleCount) ell)
    (hw : ∀ a i,(before a i).1.length=NativePolynomialStageShape.width sh p ∧
      (before a i).2.length=NativePolynomialStageShape.width sh p)
    (frame : Tapes 9 2) (leaf : Tapes CompactComplexSourceReadyWorkspace.leafTapes 2)
    (suffix : Tapes CompactComplexSourceReadyScalarWorkspace.scratch 2)
    (hb : ∀ i : Fin 67,leaf.head ⟨i.val,lt_of_lt_of_le i.isLt NativeEndpointCharacterSourceReady.leaf_capacity⟩=0 ∧
      leaf.tape ⟨i.val,lt_of_lt_of_le i.isLt NativeEndpointCharacterSourceReady.leaf_capacity⟩=(fun _ => blank)) :
    HoareTime (program (s:=s)).2
      (fun z => z=(CompactComplexSourceReadyNonleafContraction.ready
        (CompactComplexNativeCodecFrame.bank control queue scalar
          (CompactComplexNativeCodec.raw v parentRows ell p) tail storage
          (CompactComplexEndpointRoleExchange.payload master masterHead before)) frame leaf).append suffix)
      (fun z => z=(CompactComplexSourceReadyNonleafContraction.ready
        (CompactComplexNativeCodecFrame.bank control queue scalar
          (CompactComplexNativeCodec.raw v parentRows ell p) tail storage
          (CompactComplexEndpointRoleExchange.payload master masterHead
            (data v hslots ell p before))) frame leaf).append suffix)
      (NativeEndpointCharacterCanonicalRoles.constant CompactComplexScalarCountLifecycle.roleDivisor*
        CompactNativeRoleTransferBudget.volume parentRows sh ell p+1+
        (NativeUniformPolynomialRotationRoles.constant*
          CompactNativeRoleTransferBudget.volume parentRows sh ell p+1+
          (NativeUniformPolynomialRotationRoles.constant*
            CompactNativeRoleTransferBudget.volume parentRows sh ell p+1+
            CompactComplexEndpointRoleExchange.constant*
              CompactNativeRoleTransferBudget.volume parentRows sh ell p))) := by
  have he : parentRows/CompactComplexScalarCountLifecycle.roleDivisor=parentRows/roleCount := by
    rw [CompactComplexScalarCountLifecycle.roleDivisor_eq]
  have hr' : 0<parentRows/CompactComplexScalarCountLifecycle.roleDivisor := by rw [he]; exact hr
  have hsign := NativeEndpointCharacterCanonicalSourceReady.runs (s:=s)
    (w:=CompactComplexSourceReadyScalarWorkspace.scratch) true v parentRows ell p
    hslots hG hA hGK hpay hr' control queue scalar tail storage master masterHead
    (fun a i => before a (Fin.cast (congrArg (fun r => r*(2^sh.bits*2^ell)) he) i))
    (fun a i => hw a _) frame leaf suffix hb
  rw [payload_cast he master masterHead before,
    signed_payload_cast he v hslots p master masterHead before] at hsign
  have hw1 := signed_width v hslots ell p (NativePolynomialStageShape.width sh p) before hw
  have hphase := NativeUniformPolynomialRotationSourceReady.runs false v parentRows ell p
    hG hA hGK hpay hr control queue scalar tail storage master masterHead
    (signed v hslots ell p before) hw1 frame leaf suffix hb
  have hw2 := uniform_width false v (NativePolynomialStageShape.width sh p) _ hw1
  have hnegative := NativeUniformPolynomialRotationSourceReady.runs true v parentRows ell p
    hG hA hGK hpay hr control queue scalar tail storage master masterHead
    (phased v hslots ell p before) hw2 frame leaf suffix hb
  have hw3 := uniform_width true v (NativePolynomialStageShape.width sh p) _ hw2
  have hexchange := CompactComplexSourceReadyEndpointRoleExchange.runs sh parentRows ell p hr
    control queue scalar (CompactComplexNativeCodec.raw v parentRows ell p) tail storage
    master masterHead (negated v hslots ell p before) hw3 frame leaf suffix
  have h := ProgramPairSequence.runs
    (NativeEndpointCharacterCanonicalSourceReady.program (s:=s)
      (w:=CompactComplexSourceReadyScalarWorkspace.scratch) true) _ hsign
    (ProgramPairSequence.runs
      (NativeUniformPolynomialRotationSourceReady.program (s:=s)
        (w:=CompactComplexSourceReadyScalarWorkspace.scratch) false) _ hphase
      (ProgramPairSequence.runs
        (NativeUniformPolynomialRotationSourceReady.program (s:=s)
          (w:=CompactComplexSourceReadyScalarWorkspace.scratch) true)
        (exchange (s:=s)) hnegative hexchange))
  dsimp only [program,data]
  exact h

end
end IntegerMultBounds.Machine.CompactComplexSourceReadySinkCorrections
