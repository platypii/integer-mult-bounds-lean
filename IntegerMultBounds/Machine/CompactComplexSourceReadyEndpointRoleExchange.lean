import IntegerMultBounds.Machine.CompactComplexEndpointRoleExchange
import IntegerMultBounds.Machine.CompactComplexSourceReadyNonleafContraction
import IntegerMultBounds.Machine.CompactComplexSourceReadyOrientedControls

/-! Original named X/Y exchanges execute on the existing node bank, retaining
its frame9, leaf, work10 and scalar suffix. The complete endpoint is the literal
caller with its routed array payload; no local execution contract is supplied. -/
namespace IntegerMultBounds.Machine.CompactComplexSourceReadyEndpointRoleExchange
noncomputable section
open CompactGadgetReservationShape (Shape)
open CompactSpectatorVisitGeometry (Array)
open CompactComplexRolePhaseSite (roleCount roleEncoding)
open CompactComplexEndpointRoleExchange (Wire)
open CompactComplexNativeCodecFrame (bank permanentTapes)
variable {s : ℕ}

private def words {A S : Type*} {c : ℕ} (e : NamedRoleWordExchange.Role A S ≃ Fin c)
    {sh : Shape} {rows ell : ℕ} (data : NamedRoleWordExchange.Role A S → Array sh rows ell) : Tapes c 2 :=
  ⟨fun _ => 0,fun j => NativeZeroPadding.word (NativeZeroPaddingArray.word (data (e.symm j)))⟩

/-- Abstract counts keep this identity independent of the astronomical
original role cardinality. -/
private theorem replace_roles {A S : Type*} {n c u : ℕ}
    (e : NamedRoleWordExchange.Role A S ≃ Fin c)
    (base : Tapes n 2) (extra : Tapes u 2) {sh : Shape} {rows ell : ℕ}
    (before after : NamedRoleWordExchange.Role A S → Array sh rows ell) :
    NamedRoleWordExchange.bank (fun a => Fin.castAdd u (Fin.natAdd n (e a)))
      ((base.append (words e before)).append extra) after=
      (base.append (words e after)).append extra := by
  have hinj : Function.Injective (fun a => Fin.castAdd u (Fin.natAdd n (e a))) := by
    intro a b h
    have hv := congrArg (fun j : Fin ((n+c)+u) => j.val) h
    apply e.injective
    apply Fin.ext
    simp only [Fin.val_castAdd,Fin.val_natAdd] at hv
    omega
  apply congrArg₂ Tapes.mk
  · funext i
    induction i using Fin.addCases (m:=n+c) (n:=u) with
    | right i => simp only [Tapes.append,Fin.addCases_right]
    | left i =>
      induction i using Fin.addCases (m:=n) (n:=c) with
      | left i => simp only [Tapes.append,Fin.addCases_left]
      | right i => simp only [Tapes.append,Fin.addCases_left,Fin.addCases_right,words]
  · funext i
    change (NamedRoleWordExchange.bank (fun a => Fin.castAdd u (Fin.natAdd n (e a)))
      ((base.append (words e before)).append extra) after).tape i=
      ((base.append (words e after)).append extra).tape i
    induction i using Fin.addCases (m:=n+c) (n:=u) with
    | right i =>
      rw [NamedRoleWordExchange.bank_frame]
      · simp only [Tapes.append,Fin.addCases_right]
      · intro a h
        have hv := congrArg (fun j : Fin ((n+c)+u) => j.val) h
        have ha := (e a).isLt
        simp only [Fin.val_castAdd,Fin.val_natAdd] at hv
        omega
    | left i =>
      induction i using Fin.addCases (m:=n) (n:=c) with
      | left i =>
        rw [NamedRoleWordExchange.bank_frame]
        · simp only [Tapes.append,Fin.addCases_left]
        · intro a h
          have hv := congrArg (fun j : Fin ((n+c)+u) => j.val) h
          have hi := i.isLt
          simp only [Fin.val_castAdd,Fin.val_natAdd] at hv
          omega
      | right i =>
        have he : Fin.castAdd u (Fin.natAdd n i)=Fin.castAdd u (Fin.natAdd n (e (e.symm i))) := by
          rw [Equiv.apply_symm_apply]
        rw [he,NamedRoleWordExchange.bank_role _ hinj]
        simp only [Tapes.append,Fin.addCases_left,Fin.addCases_right,words,Equiv.apply_symm_apply]

private theorem role_payload (source : ℤ → Fin 6) (sourceHead : ℤ)
    {sh : Shape} {rows ell : ℕ} (data : Wire → Array sh rows ell) :
    CompactNativeRoleSourcePorts.roles (CompactComplexEndpointRoleExchange.payload source sourceHead data)=
      words roleEncoding data := by
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals
    have he : (⟨i.val+1,by omega⟩ : Fin (1+roleCount))=Fin.natAdd 1 i := Fin.ext (by simp;omega)
    simp only [CompactComplexEndpointRoleExchange.payload,
      CyclicRowCopy.payload,he,Tapes.append,Fin.addCases_right]

/-- Exact complete-bank endpoint, with the work10 still empty. -/
theorem caller_endpoint (control : Tapes 43 2) (queue : Tapes 1 2)
    (scalar stage : ActiveRepairRankHeadersCommands.State) (tail : Tapes 22 2)
    (storage : Tapes (10+s) 2) (source : ℤ → Fin 6) (sourceHead : ℤ)
    {sh : Shape} {rows ell : ℕ} (data : Wire → Array sh rows ell) :
    let before := bank control queue scalar stage tail storage
      (CompactComplexEndpointRoleExchange.payload source sourceHead data)
    CompactComplexEndpointRoleExchange.bank (before.append (SharedBank.empty 10 2))
      (fun a => data (Networks.ComplexFramedExecution.route a))=
      (bank control queue scalar stage tail storage
        (CompactComplexEndpointRoleExchange.payload source sourceHead
          (fun a => data (Networks.ComplexFramedExecution.route a)))).append (SharedBank.empty 10 2) := by
  dsimp only
  unfold CompactComplexEndpointRoleExchange.bank bank CompactComplexNativeRoleBridge.bank
  rw [role_payload,role_payload]
  exact replace_roles roleEncoding _ _ data (fun a => data (Networks.ComplexFramedExecution.route a))

attribute [local irreducible] CompactComplexEndpointRoleExchange.program

def nodeProgram : Σ q,Program (CompactComplexSourceReadyWorkspace.tapes s roleCount) q 2 :=
  ⟨_,CompactComplexSourceReadyNonleafContraction.placed
    (CompactComplexEndpointRoleExchange.program (s:=10+s) (u:=10)).2⟩
def program : Σ q,Program (CompactComplexSourceReadyScalarWorkspace.tapes s roleCount) q 2 :=
  ⟨nodeProgram.1,CompactComplexSourceReadyOrientedControls.widen nodeProgram.2⟩

/-- Actual fixed original-role exchange on the source-ready node bank. -/
theorem node_runs (sh : Shape) (parentRows ell p : ℕ) (hr : 0<parentRows/roleCount)
    (control : Tapes 43 2) (queue : Tapes 1 2)
    (scalar stage : ActiveRepairRankHeadersCommands.State) (tail : Tapes 22 2)
    (storage : Tapes (10+s) 2) (source : ℤ → Fin 6) (sourceHead : ℤ)
    (data : Wire → Array sh (parentRows/roleCount) ell)
    (hw : ∀ a i,(data a i).1.length=CompactNativeRoleHeaders.recordWidth sh p ∧
      (data a i).2.length=CompactNativeRoleHeaders.recordWidth sh p)
    (frame : Tapes 9 2) (leaf : Tapes CompactComplexSourceReadyWorkspace.leafTapes 2) :
    HoareTime (CompactComplexSourceReadyNonleafContraction.placed
      (CompactComplexEndpointRoleExchange.program (s:=10+s) (u:=10)).2)
      (fun z => z=CompactComplexSourceReadyNonleafContraction.ready
        (bank control queue scalar stage tail storage
          (CompactComplexEndpointRoleExchange.payload source sourceHead data)) frame leaf)
      (fun z => z=CompactComplexSourceReadyNonleafContraction.ready
        (bank control queue scalar stage tail storage
          (CompactComplexEndpointRoleExchange.payload source sourceHead
            (fun a => data (Networks.ComplexFramedExecution.route a)))) frame leaf)
      (CompactComplexEndpointRoleExchange.constant*CompactNativeRoleTransferBudget.volume parentRows sh ell p) := by
  have h := CompactComplexEndpointRoleExchange.runs_caller sh parentRows ell p hr control queue scalar stage
    tail storage (SharedBank.empty 10 2) source sourceHead data hw
  dsimp only at h
  rw [caller_endpoint] at h
  exact CompactComplexSourceReadyNonleafContraction.placed_runs (s:=s) (c:=roleCount)
    (M:=(CompactComplexEndpointRoleExchange.program (s:=10+s) (u:=10)).2) h frame leaf

/-- The same real exchange retains arbitrary leaf, recursive frame and scalar
workspace contents, with every physical cost paid by parent native volume. -/
theorem runs (sh : Shape) (parentRows ell p : ℕ) (hr : 0<parentRows/roleCount)
    (control : Tapes 43 2) (queue : Tapes 1 2)
    (scalar stage : ActiveRepairRankHeadersCommands.State) (tail : Tapes 22 2)
    (storage : Tapes (10+s) 2) (source : ℤ → Fin 6) (sourceHead : ℤ)
    (data : Wire → Array sh (parentRows/roleCount) ell)
    (hw : ∀ a i,(data a i).1.length=CompactNativeRoleHeaders.recordWidth sh p ∧
      (data a i).2.length=CompactNativeRoleHeaders.recordWidth sh p)
    (frame : Tapes 9 2) (leaf : Tapes CompactComplexSourceReadyWorkspace.leafTapes 2)
    (scratch : Tapes CompactComplexSourceReadyScalarWorkspace.scratch 2) :
    HoareTime (CompactComplexSourceReadyOrientedControls.widen
      (CompactComplexSourceReadyNonleafContraction.placed
        (CompactComplexEndpointRoleExchange.program (s:=10+s) (u:=10)).2))
      (fun z => z=(CompactComplexSourceReadyNonleafContraction.ready
        (bank control queue scalar stage tail storage
          (CompactComplexEndpointRoleExchange.payload source sourceHead data)) frame leaf).append scratch)
      (fun z => z=(CompactComplexSourceReadyNonleafContraction.ready
        (bank control queue scalar stage tail storage
          (CompactComplexEndpointRoleExchange.payload source sourceHead
            (fun a => data (Networks.ComplexFramedExecution.route a)))) frame leaf).append scratch)
      (CompactComplexEndpointRoleExchange.constant*CompactNativeRoleTransferBudget.volume parentRows sh ell p) :=
  CompactComplexSourceReadyOrientedControls.widen_runs (s:=s) (c:=roleCount)
    (node_runs sh parentRows ell p hr control queue scalar stage tail storage source sourceHead data hw frame leaf) scratch

end
end IntegerMultBounds.Machine.CompactComplexSourceReadyEndpointRoleExchange
