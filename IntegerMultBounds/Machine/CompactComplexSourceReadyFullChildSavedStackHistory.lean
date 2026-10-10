import IntegerMultBounds.Machine.CompactComplexSavedStackTailInvariant
import IntegerMultBounds.Machine.CompactComplexSourceReadyChildEntryPath

/-! The complete real child-entry endpoint has the actual pushed call frame.
Source preparation and raw replacement retain storage; target, live and header
saves use distinct physical ports. No endpoint equality is assumed. -/
namespace IntegerMultBounds.Machine.CompactComplexSourceReadyFullChildSavedStackHistory
noncomputable section
open Networks
open CompactGadgetReservationShape (Shape)
open CompactComplexRecursiveGeometry (arity Visit)
open CompactComplexChildHeadersData (parent child)
open CompactComplexNonleafRoleChildBank
open CompactComplexNonleafRolePreparation (sourceReady)
open SharedPlacementAlphabet (setTape)
open RecursiveChildQuotientsConstant (bits)
open CompactComplexSavedStackTailInvariant (History)
variable {s c : ℕ} {sh : Shape} {left k siteCount : ℕ}
attribute [local irreducible] ComplexRank25.program ComplexRecursiveCallSchema.sites
  CompactComplexRolePhaseSite.roleCount CompactComplexCallReturn.addressWidth

private theorem storage_ne {i j : Fin (10+s)} (h : i≠j) :
    storage (c:=c) i≠storage j := by
  intro he
  apply h
  apply Fin.ext
  have hv := congrArg Fin.val he
  simp only [storage,CompactComplexSpectatorTargetBank.oldSlot,
    CompactComplexControllerNativeFrame.storageSlot,Fin.val_castAdd,Fin.val_natAdd] at hv
  omega

/-- The child bank's full sequence writes exactly the saved call word and head. -/
theorem output_pc (v : Tapes (tapes s c) 2) (parentTarget n e : ℕ)
    (headerStack pcStack liveStack : Fin s) (hh : pcStack≠headerStack) (hl : pcStack≠liveStack)
    (site : Fin siteCount) (rho : Fin sh.chunk) (visit : Visit sh.active left (k+2))
    (hactive : sh.active≤sh.axes) (pair : Networks.BinaryRowProgram.Op (Fin arity))
    (coordinate : Fin arity) (rows ell p : ℕ) (payload : Tapes (1+c) 2) :
    let out := output v parentTarget n e headerStack pcStack liveStack site rho visit hactive pair coordinate rows ell p payload
    out.head (storage (Fin.natAdd 10 pcStack))=
      v.head (storage (Fin.natAdd 10 pcStack))+CompactComplexCallReturn.addressWidth siteCount arity ∧
    out.tape (storage (Fin.natAdd 10 pcStack))=
      FiniteReturnStack.wordPart (v.tape (storage (Fin.natAdd 10 pcStack)))
        (v.head (storage (Fin.natAdd 10 pcStack))) (CompactComplexCallReturn.codeFor site coordinate)
        (CompactComplexCallReturn.addressWidth siteCount arity) le_rfl := by
  dsimp only
  have hhead : storage (c:=c) (Fin.natAdd 10 pcStack)≠storage (Fin.natAdd 10 headerStack) :=
    storage_ne (fun he => hh (Fin.natAdd_injective _ _ he))
  have hlive : storage (c:=c) (Fin.natAdd 10 pcStack)≠storage (Fin.natAdd 10 liveStack) :=
    storage_ne (fun he => hl (Fin.natAdd_injective _ _ he))
  have htar : storage (c:=c) (Fin.natAdd 10 pcStack)≠target :=
    storage_ne (by intro he; have hv := congrArg Fin.val he; change 10+pcStack.val=8 at hv; omega)
  have htarStack : storage (c:=c) (Fin.natAdd 10 pcStack)≠targetStack :=
    storage_ne (by intro he; have hv := congrArg Fin.val he; change 10+pcStack.val=9 at hv; omega)
  have hcontrol : storage (c:=c) (Fin.natAdd 10 pcStack)≠CompactComplexNonleafRoleChildBank.control 1 := by
    intro he
    have hv := congrArg Fin.val he
    simp only [storage,CompactComplexSpectatorTargetBank.oldSlot,
      CompactComplexControllerNativeFrame.storageSlot,CompactComplexNonleafRoleChildBank.control,Fin.val_castAdd,Fin.val_natAdd] at hv
    omega
  have h := replace_storage
    (descended (pcSaved (headersSaved (liveSaved (targetSaved v parentTarget) liveStack n) headerStack
      (CompactComplexControllerChildPrefix.data (parent rho visit hactive pair))) pcStack site coordinate) e)
    (CompactNativeRoleOriginal.bank (CompactComplexNativeCodec.raw (child rho visit hactive pair coordinate) rows ell p) payload)
    (Fin.natAdd 10 pcStack)
  constructor
  · apply h.1.trans
    simp only [descended,pcSaved,FiniteReturnStackAt.pushed,headersSaved,liveSaved,targetSaved,setTape]
    rw [Function.update_of_ne hcontrol,Function.update_self]
    simp only [Function.update_of_ne hhead,Function.update_of_ne hlive,
      Function.update_of_ne htar,Function.update_of_ne htarStack]
  · apply h.2.trans
    simp only [descended,pcSaved,FiniteReturnStackAt.pushed,headersSaved,liveSaved,targetSaved,setTape]
    rw [Function.update_of_ne hcontrol,Function.update_self]
    simp only [Function.update_of_ne hhead,Function.update_of_ne hlive,
      Function.update_of_ne htar,Function.update_of_ne htarStack]

/-- Quotient source preparation preserves the original saved-PC tape literally. -/
theorem source_ready_pc (selected : Fin c) (rho : Fin sh.chunk)
    (visit : Visit sh.active left (k+2)) (hactive : sh.active≤sh.axes)
    (pair : Networks.BinaryRowProgram.Op (Fin arity)) (rows ell p : ℕ)
    (f : CompactSpectatorVisitGeometry.Array sh (rows/c) ell)
    (v : Tapes (CompactComplexNonleafRoleEntry.tapes (10+s) c) 2) (pcStack : Fin s) :
    (sourceReady selected rho visit hactive pair rows ell p f v).head (storage (Fin.natAdd 10 pcStack))=
      v.head (CompactComplexNonleafRoleReturnFrame.oldSlot (Fin.natAdd 10 pcStack)) ∧
    (sourceReady selected rho visit hactive pair rows ell p f v).tape (storage (Fin.natAdd 10 pcStack))=
      v.tape (CompactComplexNonleafRoleReturnFrame.oldSlot (Fin.natAdd 10 pcStack)) := by
  exact CompactComplexNonleafRolePreparation.quotient_output_storage selected sh rows ell p
    (parent rho visit hactive pair).rho (parent rho visit hactive pair).left
    (parent rho visit hactive pair).f (parent rho visit hactive pair).slots
    (parent rho visit hactive pair).right (parent rho visit hactive pair).source.val
    (parent rho visit hactive pair).target.val f v (Fin.natAdd 10 pcStack)

local notation "RC" => CompactComplexRolePhaseSite.roleCount

/-- The full actual endpoint has exactly the pcSaved bank of its entry caller. -/
theorem public_output_pc_saved (call : ComplexRecursiveCallSchema.Call) (rho : Fin sh.chunk)
    (visit : Visit sh.active left (k+2)) (hactive : sh.active≤sh.axes)
    (pair : Networks.BinaryRowProgram.Op (Fin arity)) (rows ell p : ℕ)
    (f : CompactSpectatorVisitGeometry.Array sh (rows/RC) ell)
    (v : Tapes (CompactComplexNonleafRoleEntry.tapes (10+s) RC) 2)
    (parentTarget n : ℕ) (headerStack pcStack liveStack : Fin s)
    (hh : pcStack≠headerStack) (hl : pcStack≠liveStack) :
    let out := CompactComplexSourceReadyChildEntryPath.publicOutput call rho visit hactive pair rows ell p f v
      parentTarget n headerStack pcStack liveStack
    let saved := pcSaved (v.append (SharedBank.empty 7 2)) pcStack call.site call.slot
    FiniteReturnStack.bank (out.tape (storage (Fin.natAdd 10 pcStack)))
      (out.head (storage (Fin.natAdd 10 pcStack)))=
    FiniteReturnStack.bank (saved.tape (storage (Fin.natAdd 10 pcStack)))
      (saved.head (storage (Fin.natAdd 10 pcStack))) := by
  dsimp only [CompactComplexSourceReadyChildEntryPath.publicOutput]
  have hs := source_ready_pc (CompactComplexSourceReadyChildEntryPath.selected call) rho visit hactive pair rows ell p f v pcStack
  have ho := output_pc (sourceReady (CompactComplexSourceReadyChildEntryPath.selected call) rho visit hactive pair rows ell p f v)
    parentTarget n (k+2) headerStack pcStack liveStack hh hl call.site rho visit hactive pair call.slot
    (rows/RC) ell p (CompactNativeRoleReservedBridge.sourcePayload sh (rows/RC) ell f RC)
  dsimp only at ho
  apply congrArg₂ FiniteReturnStack.bank
  · rw [ho.2,hs.1,hs.2]
    simp only [pcSaved,FiniteReturnStackAt.pushed,setTape,Function.update_self,
      storage,CompactComplexNonleafRoleReturnFrame.oldSlot,Tapes.append,Fin.addCases_left]
  · rw [ho.1,hs.1]
    simp only [pcSaved,FiniteReturnStackAt.pushed,setTape,Function.update_self,
      storage,CompactComplexNonleafRoleReturnFrame.oldSlot,Tapes.append,Fin.addCases_left]

/-- Full physical child entry extends genuine history with its actual call. -/
theorem public_output_history (call : ComplexRecursiveCallSchema.Call) (rho : Fin sh.chunk)
    (visit : Visit sh.active left (k+2)) (hactive : sh.active≤sh.axes)
    (pair : Networks.BinaryRowProgram.Op (Fin arity)) (rows ell p : ℕ)
    (f : CompactSpectatorVisitGeometry.Array sh (rows/RC) ell)
    (v : Tapes (CompactComplexNonleafRoleEntry.tapes (10+s) RC) 2)
    (parentTarget n : ℕ) (headerStack pcStack liveStack : Fin s)
    (hh : pcStack≠headerStack) (hl : pcStack≠liveStack) (origin : ℤ)
    (h : History (CompactComplexCallReturn.addressWidth ComplexRecursiveCallSchema.sites.length (25^3))
      origin (v.tape (CompactComplexNonleafRoleReturnFrame.oldSlot (Fin.natAdd 10 pcStack)))
      (v.head (CompactComplexNonleafRoleReturnFrame.oldSlot (Fin.natAdd 10 pcStack)))) :
    let out := CompactComplexSourceReadyChildEntryPath.publicOutput call rho visit hactive pair rows ell p f v
      parentTarget n headerStack pcStack liveStack
    History (CompactComplexCallReturn.addressWidth ComplexRecursiveCallSchema.sites.length (25^3))
      origin (out.tape (storage (Fin.natAdd 10 pcStack)))
      (out.head (storage (Fin.natAdd 10 pcStack))) := by
  dsimp only [CompactComplexSourceReadyChildEntryPath.publicOutput]
  have hs := source_ready_pc (CompactComplexSourceReadyChildEntryPath.selected call) rho visit hactive pair rows ell p f v pcStack
  have ho := output_pc (sourceReady (CompactComplexSourceReadyChildEntryPath.selected call) rho visit hactive pair rows ell p f v)
    parentTarget n (k+2) headerStack pcStack liveStack hh hl call.site rho visit hactive pair call.slot
    (rows/RC) ell p (CompactNativeRoleReservedBridge.sourcePayload sh (rows/RC) ell f RC)
  dsimp only at ho
  change History _ origin
    ((output _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).tape (storage (Fin.natAdd 10 pcStack)))
    ((output _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).head (storage (Fin.natAdd 10 pcStack)))
  rw [ho.1,ho.2,hs.1,hs.2]
  simpa only [CompactComplexRecursiveGeometry.arity,CompactComplexCallReturn.code] using
    History.push h (CompactComplexCallReturn.code call)

end
end IntegerMultBounds.Machine.CompactComplexSourceReadyFullChildSavedStackHistory
