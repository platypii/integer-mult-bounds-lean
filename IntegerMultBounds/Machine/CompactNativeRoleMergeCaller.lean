import IntegerMultBounds.Machine.CompactNativeRoleMetadataCleanup

/-! Arbitrary native descendant results are physically joined at source43,
then the copied original13/ell/p metadata is erased. The original scalar caller
and unrelated streams remain framed; role streams and all scratch finish blank. -/
namespace IntegerMultBounds.Machine.CompactNativeRoleMergeCaller
noncomputable section
open CompactNativeRoleSourcePorts
open CompactGadgetReservationShape (Shape)
variable {n c t : ℕ}

theorem empty_roles (s : Shape) (ell : ℕ)
    (f : CompactNativeRoleGeometry.Array n c (CompactNativeRoleOriginal.inner s ell)) :
    roles (CompactNativeRoleOriginal.sourcePayload s ell f)=SharedBank.empty c 2 := by
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals
    have he : (⟨i.val+1,by omega⟩ : Fin (1+c))=Fin.natAdd 1 i := Fin.ext (by dsimp; omega)
    simp [he,CompactNativeRoleOriginal.sourcePayload,CyclicRowCopy.payload,Tapes.append]

def cleanupProgram (c t : ℕ) :=
  extend (extend (Placement.placed (CompactChildHeadersArithmetic.compile (a:=2)
    CompactNativeRoleMetadataCleanup.schedule).2
      (finAddFlip : Fin (43+t) ≃ Fin (t+43))) c) (localTapes c)
def program (c t : ℕ) (ht : 43<t) :=
  seq (placed (CompactNativeRoleOriginal.mergeProgram c) t ht) (cleanupProgram c t)

def cost (n c : ℕ) (s : Shape) (ell p rho left count slots right src dst : ℕ) :=
  CompactNativeRoleOriginal.cost true n c s ell p rho left count slots right src dst+1+
  CompactChildHeadersArithmetic.scheduleCost CompactNativeRoleMetadataCleanup.schedule
    (CompactSpectatorLeafSetup.raw s (n*c) ell p rho left count slots right src dst)

theorem merges (n : ℕ) (s : Shape) (ell p rho left count slots right src dst : ℕ)
    (hc : 0<c) (hn : 0<n) (hG : 0<s.guard) (hA : 0<s.axes) (hK : 0<s.chunk)
    (data : Fin c → Fin (n*CompactNativeRoleOriginal.inner s ell) → ButterflyStreamData.Coefficient)
    (hw : ∀ j z,(data j z).1.length=CompactNativeRoleHeaders.recordWidth s p ∧
      (data j z).2.length=CompactNativeRoleHeaders.recordWidth s p)
    (old : Tapes t 2) (ht : 43<t) :
    HoareTime (program c t ht)
      (fun v => v=CleanSubbank.bank (s:=localTapes c)
        (external old ht (CompactSpectatorLeafSetup.raw s (n*c) ell p rho left count slots right src dst)
          (CompactNativeRoleAssembly.payload (n:=n) (c:=c) (L:=CompactNativeRoleOriginal.inner s ell) data)))
      (fun v => v=CleanSubbank.bank (s:=localTapes c)
        (((replaceSource old ht (CompactNativeRoleOriginal.sourcePayload (n:=n) (c:=c) s ell
          (CompactNativeRoleAssembly.join (n:=n) (c:=c) (L:=CompactNativeRoleOriginal.inner s ell) data))).append
            (SharedBank.empty 43 2)).append (SharedBank.empty c 2)))
      (cost n c s ell p rho left count slots right src dst) := by
  let result := CompactNativeRoleOriginal.sourcePayload (n:=n) (c:=c) s ell
    (CompactNativeRoleAssembly.join (n:=n) (c:=c) (L:=CompactNativeRoleOriginal.inner s ell) data)
  have h0 := CompactNativeRoleSourceRuns.merges n s ell p rho left count slots right src dst hc hn hG hA hK data hw old ht
  have h1 := hoare_extend_eq (hoare_extend_eq
    (RecursiveRowsConstruct.left_frame
      (CompactNativeRoleMetadataCleanup.raw_runs s (n*c) ell p rho left count slots right src dst)
        (replaceSource old ht result)) (roles result)) (SharedBank.empty (localTapes c) 2)
  have hh := h0.seq h1
  simpa only [program,cost,cleanupProgram,external,CleanSubbank.bank,result,empty_roles] using hh

end
end IntegerMultBounds.Machine.CompactNativeRoleMergeCaller
