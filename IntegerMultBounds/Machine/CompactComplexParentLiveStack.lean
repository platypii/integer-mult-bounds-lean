import IntegerMultBounds.Machine.CompactComplexNonleafRoleReturnFrame
import IntegerMultBounds.Machine.BinaryDescriptorStackAt
import IntegerMultBounds.Machine.BinaryDescriptorCleanupList

/-! Save the actual parent event denominator on a distinct fixed unbounded
storage stack. Child entry inherits it unchanged. After child normalization,
copy its actual current denominator into blank target8 before popping the old
parent denominator back into live7. Spectator promotion can then read old cur7
and advanced tar8; numerical alignment and final commit are separate. -/
namespace IntegerMultBounds.Machine.CompactComplexParentLiveStack
noncomputable section
open SharedPlacementAlphabet (setTape)
open RecursiveChildQuotientsConstant (bits)
variable {s c : ℕ}

abbrev tapes (s c : ℕ) := CompactComplexNonleafRoleEntry.tapes (10+s) c

def current : Fin (tapes s c) := CompactComplexNonleafRoleReturnFrame.oldSlot ⟨7,by omega⟩
def target : Fin (tapes s c) := CompactComplexNonleafRoleReturnFrame.oldSlot ⟨8,by omega⟩
def liveStack (j : Fin s) : Fin (tapes s c) :=
  CompactComplexNonleafRoleReturnFrame.oldSlot (Fin.natAdd 10 j)

private theorem old_injective : Function.Injective
    (CompactComplexNonleafRoleReturnFrame.oldSlot (s:=10+s) (c:=c)) := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  simp only [CompactComplexNonleafRoleReturnFrame.oldSlot,CompactComplexSpectatorTargetBank.oldSlot,
    CompactComplexControllerNativeFrame.storageSlot,Fin.val_castAdd,Fin.val_natAdd] at hv
  omega

theorem current_target : current (s:=s) (c:=c)≠target := by
  intro h
  have hv := congrArg Fin.val (old_injective h)
  change 7=8 at hv
  omega

theorem current_stack (j : Fin s) : current (c:=c)≠liveStack j := by
  intro h
  have hv := congrArg Fin.val (old_injective h)
  change 7=10+j.val at hv
  omega

theorem target_stack (j : Fin s) : target (c:=c)≠liveStack j := by
  intro h
  have hv := congrArg Fin.val (old_injective h)
  change 8=10+j.val at hv
  omega

def saved (j : Fin s) (v : Tapes (tapes s c) 2) (n : ℕ) :=
  setTape v (liveStack j)
    (BinaryDescriptorStack.frame (v.tape (liveStack j)) (v.head (liveStack j)) (bits n))
    (v.head (liveStack j)+1+(bits n).length)

def saveProgram (j : Fin s) :=
  BinaryDescriptorStackAt.pushProgram (a:=2) (current (c:=c)) (liveStack j) (current_stack j)

/-- The saved bits come from the actual current tape; the same physical live7
word remains available as the inherited child denominator after the push. -/
theorem save (j : Fin s) (v : Tapes (tapes s c) 2) (n : ℕ)
    (ht : v.tape current=BinaryDescriptorStack.descriptor (bits n)) (hh : v.head current=1) :
    HoareTime (saveProgram j) (fun z => z=v) (fun z => z=saved j v n) (2*(bits n).length+7) :=
  BinaryDescriptorStackAt.push_hoare current (liveStack j) (current_stack j) v (bits n) ht hh

theorem saved_frame (j : Fin s) (v : Tapes (tapes s c) 2) (n : ℕ)
    (i : Fin (tapes s c)) (hi : i≠liveStack j) :
    (saved j v n).head i=v.head i ∧ (saved j v n).tape i=v.tape i := by
  simp only [saved,setTape,Function.update_of_ne hi,and_self]

theorem inherited (j : Fin s) (v : Tapes (tapes s c) 2) (n : ℕ)
    (ht : v.tape current=BinaryDescriptorStack.descriptor (bits n)) (hh : v.head current=1) :
    (saved j v n).tape current=BinaryDescriptorStack.descriptor (bits n) ∧
    (saved j v n).head current=1 := by
  have hf := saved_frame j v n current (current_stack j)
  exact ⟨hf.2.trans ht,hf.1.trans hh⟩

/-- Cells below the old stack head and above the newly appended descriptor are
literally retained; no depth-dependent tape allocation or supplied copy exists. -/
theorem saved_outside (j : Fin s) (v : Tapes (tapes s c) 2) (n : ℕ) (z : ℤ)
    (hz : z<v.head (liveStack j) ∨ v.head (liveStack j)+1+(bits n).length≤z) :
    (saved j v n).tape (liveStack j) z=v.tape (liveStack j) z := by
  simp only [saved,setTape,Function.update_self]
  exact BinaryDescriptorStack.frame_outside _ _ _ _ hz

def restoreProgram (j : Fin s) :=
  BinaryDescriptorStackAt.popProgram (a:=2) (liveStack (c:=c) j) current (current_stack j).symm

def restored (j : Fin s) (v : Tapes (tapes s c) 2) (f : ℤ → Fin 6) (p : ℤ) (n : ℕ) :=
  setTape (setTape v (liveStack j) f p) current (BinaryDescriptorStack.descriptor (bits n)) 1

/-- Pop a real previously saved parent descriptor into the physically blank
current port, preserving the separately retained advanced target. -/
theorem restore (j : Fin s) (v : Tapes (tapes s c) 2) (f : ℤ → Fin 6) (p : ℤ) (n : ℕ)
    (ht : v.tape (liveStack j)=BinaryDescriptorStack.frame f p (bits n))
    (hh : v.head (liveStack j)=p+1+(bits n).length)
    (hc : v.tape current=(fun _ => blank)) (hch : v.head current=0)
    (hf : ∀ z,p≤z → z<p+1+(bits n).length → f z=blank) :
    HoareTime (restoreProgram j) (fun z => z=v) (fun z => z=restored j v f p n) (2*(bits n).length+7) :=
  BinaryDescriptorStackAt.pop_hoare (liveStack j) current (current_stack j).symm v f p (bits n) ht hh hc hch hf

/-- Retain the actual normalized child live word in target8 first, then clear
live7 and restore the parent event word from the distinct physical stack. -/
def restoreWithTargetProgram (j : Fin s) := seq
  (seq (BinaryDescriptorInstall.program 2 (current (c:=c)) target current_target)
    (BinaryDescriptorCleanupList.oneProgram (a:=2) (current (s:=s) (c:=c))))
  (restoreProgram (c:=c) j)

def restoredWithTarget (j : Fin s) (v : Tapes (tapes s c) 2)
    (f : ℤ → Fin 6) (p : ℤ) (parent child : ℕ) :=
  setTape (setTape (setTape v target (BinaryDescriptorStack.descriptor (bits child)) 1)
    (liveStack j) f p) current (BinaryDescriptorStack.descriptor (bits parent)) 1

/-- Both denominator words have physical origins: child is read from live7;
parent is popped from the live stack. Target8 must be genuinely blank after the
child's normalized exact-return commit. This is tape mechanics, not Grid. -/
theorem restore_with_target (j : Fin s) (v : Tapes (tapes s c) 2)
    (f : ℤ → Fin 6) (p : ℤ) (parent child : ℕ)
    (hstack : v.tape (liveStack j)=BinaryDescriptorStack.frame f p (bits parent))
    (hstackHead : v.head (liveStack j)=p+1+(bits parent).length)
    (hcurrent : v.tape current=BinaryDescriptorStack.descriptor (bits child)) (hcurrentHead : v.head current=1)
    (htarget : v.tape target=(fun _ => blank)) (htargetHead : v.head target=0)
    (hfree : ∀ z,p≤z → z<p+1+(bits parent).length → f z=blank) :
    HoareTime (restoreWithTargetProgram j) (fun z => z=v)
      (fun z => z=restoredWithTarget j v f p parent child)
      (4*(bits child).length+2*(bits parent).length+18) := by
  let copied := setTape v target (BinaryDescriptorStack.descriptor (bits child)) 1
  let cleared := setTape copied current (fun _ => blank) 0
  have h0 := BinaryDescriptorInstall.install_hoare current target current_target v (bits child)
    (hcurrent.trans (BinaryDescriptorStackRoundtrip.descriptor_encoded _)) hcurrentHead htarget htargetHead
  rw [←BinaryDescriptorStackRoundtrip.descriptor_encoded] at h0
  have h1 := BinaryDescriptorCleanupList.one_hoare current copied (bits child)
    (by simp only [copied,setTape,Function.update_of_ne current_target,hcurrent])
    (by simp only [copied,setTape,Function.update_of_ne current_target,hcurrentHead])
  have h2 := restore j cleared f p parent
    (by simp only [cleared,copied,setTape,Function.update_of_ne (current_stack j).symm,
      Function.update_of_ne (target_stack j).symm,hstack])
    (by simp only [cleared,copied,setTape,Function.update_of_ne (current_stack j).symm,
      Function.update_of_ne (target_stack j).symm,hstackHead])
    (by simp only [cleared,setTape,Function.update_self])
    (by simp only [cleared,setTape,Function.update_self]) hfree
  refine ((h0.seq h1).seq h2).consequence (fun _ h => h) ?_ (by omega)
  rintro z rfl
  have hne := current_stack (c:=c) j
  apply congrArg₂ Tapes.mk <;> funext i <;>
    by_cases hc : i=current <;> by_cases hs : i=liveStack j <;>
    simp_all [restored,cleared,copied,setTape]

/-- Recover the parent word from the exact real saved frame retained by child
execution, while deriving the stored bits from `saved`, not an external word. -/
theorem restore_after_child (j : Fin s) (v u : Tapes (tapes s c) 2) (parent child : ℕ)
    (hstack : u.tape (liveStack j)=(saved j v parent).tape (liveStack j))
    (hstackHead : u.head (liveStack j)=(saved j v parent).head (liveStack j))
    (hcurrent : u.tape current=BinaryDescriptorStack.descriptor (bits child)) (hcurrentHead : u.head current=1)
    (htarget : u.tape target=(fun _ => blank)) (htargetHead : u.head target=0)
    (hfree : ∀ z,v.head (liveStack j)≤z →
      z<v.head (liveStack j)+1+(bits parent).length → v.tape (liveStack j) z=blank) :
    HoareTime (restoreWithTargetProgram j) (fun z => z=u)
      (fun z => z=restoredWithTarget j u (v.tape (liveStack j)) (v.head (liveStack j)) parent child)
      (4*(bits child).length+2*(bits parent).length+18) := by
  apply restore_with_target j u (v.tape (liveStack j)) (v.head (liveStack j)) parent child
    _ _ hcurrent hcurrentHead htarget htargetHead hfree
  · simpa only [saved,setTape,Function.update_self] using hstack
  · simpa only [saved,setTape,Function.update_self] using hstackHead

/-- The endpoint literally exposes parent-old and child-advanced words on the
two ports used by existing spectator promotion; both descriptors stay at head1. -/
theorem restored_ports (j : Fin s) (v : Tapes (tapes s c) 2)
    (f : ℤ → Fin 6) (p : ℤ) (parent child : ℕ) :
    (restoredWithTarget j v f p parent child).head current=1 ∧
    (restoredWithTarget j v f p parent child).tape current=BinaryDescriptorStack.descriptor (bits parent) ∧
    (restoredWithTarget j v f p parent child).head target=1 ∧
    (restoredWithTarget j v f p parent child).tape target=BinaryDescriptorStack.descriptor (bits child) ∧
    (restoredWithTarget j v f p parent child).head (liveStack j)=p ∧
    (restoredWithTarget j v f p parent child).tape (liveStack j)=f := by
  simp only [restoredWithTarget,setTape,Function.update_self,
    Function.update_of_ne current_target.symm,Function.update_of_ne (current_stack j).symm,
    Function.update_of_ne (target_stack j),and_self]

theorem restored_frame (j : Fin s) (v : Tapes (tapes s c) 2)
    (f : ℤ → Fin 6) (p : ℤ) (parent child : ℕ) (i : Fin (tapes s c))
    (hc : i≠current) (ht : i≠target) (hs : i≠liveStack j) :
    (restoredWithTarget j v f p parent child).head i=v.head i ∧
    (restoredWithTarget j v f p parent child).tape i=v.tape i := by
  simp only [restoredWithTarget,setTape,Function.update_of_ne hc,
    Function.update_of_ne ht,Function.update_of_ne hs,and_self]

/-- Every actual payload/master/role/header slot and the independent payload
stack/clock is disjoint from the new old-storage live stack. -/
theorem stack_payload_disjoint (j : Fin s) :
    (∀ k : Fin 43,liveStack (c:=c) j≠CompactComplexNonleafRoleEntry.numeric k) ∧
    liveStack (c:=c) j≠CompactComplexNonleafRoleEntry.stack ∧
    liveStack (c:=c) j≠CompactComplexNonleafRoleEntry.source ∧
    (∀ k : Fin c,liveStack (c:=c) j≠CompactComplexNonleafRoleEntry.roleTape k) ∧
    liveStack (c:=c) j≠CompactComplexNonleafRoleEntry.clock :=
  CompactComplexNonleafRoleReturnFrame.old_slot_disjoint (Fin.natAdd 10 j)

/-- In particular the independently nested certified-target stack9 is framed. -/
theorem target_stack_preserved (j : Fin s) (v : Tapes (tapes s c) 2)
    (f : ℤ → Fin 6) (p : ℤ) (parent child : ℕ) :
    let i := CompactComplexNonleafRoleReturnFrame.oldSlot (s:=10+s) (c:=c) ⟨9,by omega⟩
    (restoredWithTarget j v f p parent child).head i=v.head i ∧
    (restoredWithTarget j v f p parent child).tape i=v.tape i := by
  apply restored_frame
  all_goals
    intro h
    have hv := congrArg Fin.val (old_injective h)
    simp only [Fin.val_natAdd] at hv
    omega

end
end IntegerMultBounds.Machine.CompactComplexParentLiveStack
