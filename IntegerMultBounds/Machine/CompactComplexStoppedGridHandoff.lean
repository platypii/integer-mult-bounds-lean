import IntegerMultBounds.Machine.CompactComplexSpectatorTargetBank
import IntegerMultBounds.Machine.CompactComplexChildGridPromoted
import IntegerMultBounds.Machine.NativeSignedReturnPrecision

/-! The literal native spectator program's output is the promoted child-grid
array, with field capacity, stream nonemptiness and equal volumes derived from
the actual retained record widths and original visit geometry. -/
namespace IntegerMultBounds.Machine.CompactComplexStoppedGridHandoff
noncomputable section
open CompactGadgetReservationShape (Shape)
open CompactSpectatorVisitGeometry (Array)
open CompactSpectatorInheritedGrid
open ButterflyStreamData (Coefficient)
open NativeSignedReturnPrecision (fields)
open NativeSignedReturnStream (volume)
open NativeSignedGapPromoteReturn (word)
open CompactComplexChildGridPromoted (aligned promote coefficient)
open CompactComplexRecursiveGeometry (Visit arity)
open SharedPlacementAlphabet (setTape)
variable {s c : ℕ}

def words {N : ℕ} (f : Fin N → Coefficient) := fields (List.ofFn f)

theorem words_tape {N : ℕ} (f : Fin N → Coefficient) :
    word (words f)=ButterflyStreamData.full (fun _ => blank) 0 f := by
  unfold word words ButterflyStreamData.full
  rw [NativeSignedReturnPrecision.native_serialization,List.flatMap,List.map_ofFn]
  rfl

private theorem fields_map (cs : List Coefficient) (gap : ℕ) :
    (fields cs).map (NativeSignedGapPromoteWord.result gap) =
      fields (cs.map (coefficient gap)) := by
  induction cs with
  | nil => rfl
  | cons x xs ih =>
    simp only [fields] at ih
    simpa only [fields,List.flatMap_cons,List.map_append,List.map_cons,List.map_nil,coefficient,
      List.cons_append,List.nil_append,List.cons.injEq,true_and] using ih

theorem words_promote (sh : Shape) (rows ell gap : ℕ) (f : Array sh rows ell) :
    (words f).map (NativeSignedGapPromoteWord.result gap)=words (promote sh rows ell gap f) := by
  rw [words,fields_map,List.map_ofFn]
  rfl

private theorem fields_width (cs : List Coefficient) (w : ℕ)
    (hw : ∀ x∈cs,x.1.length=w ∧ x.2.length=w) : ∀ x∈fields cs,x.length=w := by
  intro x hx
  obtain ⟨z,hz,hx⟩ := List.mem_flatMap.mp hx
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl|rfl
  · exact (hw z hz).1
  · exact (hw z hz).2

theorem words_width (sh : Shape) (rows ell q : ℕ) (f : Array sh rows ell)
    (hw : Width sh rows ell q f) : ∀ x∈words f,x.length=half sh q+1 := by
  apply fields_width
  intro x hx
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
  simpa only [ButterflyGuard.width,ButterflyIndependentGuardSemantics.half_eq] using hw i

private theorem fields_volume (cs : List Coefficient) (w : ℕ)
    (hw : ∀ x∈cs,x.1.length=w ∧ x.2.length=w) :
    volume (fields cs)=cs.length*(2*(w+1)) := by
  induction cs with
  | nil => simp [volume,fields,NativeSignedReturnStream.encode]
  | cons x xs ih =>
    have hx := hw x List.mem_cons_self
    have ht := ih (fun y hy => hw y (List.mem_cons_of_mem x hy))
    simp only [volume,NativeSignedReturnPrecision.native_serialization,List.flatMap_cons,
      DelimitedRadixRecord.complex,List.length_append,DelimitedRadixRecord.field_length,
      hx.1,hx.2,List.length_cons] at ht ⊢
    simp only [Nat.add_mul] at ht ⊢
    omega

theorem words_volume (sh : Shape) (rows ell q : ℕ) (f : Array sh rows ell)
    (hw : Width sh rows ell q f) :
    volume (words f)=ButterflySpectatorGeometry.Size rows sh.bits (2^ell)*(2*(half sh q+2)) := by
  have h := fields_volume (List.ofFn f) (half sh q+1) (by
    intro x hx
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
    simpa only [ButterflyGuard.width,ButterflyIndependentGuardSemantics.half_eq] using hw i)
  simpa [words,Nat.add_assoc] using h

theorem words_nonempty (sh : Shape) (rows ell q : ℕ) (hr : 0<rows)
    (f : Array sh rows ell) (hw : Width sh rows ell q f) : words f≠[] := by
  have hpos : 0<ButterflySpectatorGeometry.Size rows sh.bits (2^ell) := by
    rw [CompactSpectatorVisitGeometry.coefficient_count]
    exact Nat.mul_pos (Nat.mul_pos hr (pow_pos (by decide) _)) (pow_pos (by decide) _)
  intro he
  have hv := words_volume sh rows ell q f hw
  rw [he] at hv
  have hlt := Nat.mul_pos hpos (by omega : 0<2*(half sh q+2))
  simp only [volume,NativeSignedReturnStream.encode,List.map_nil,List.flatten_nil,List.length_nil] at hv
  omega

def payload (sh : Shape) (rows ell : ℕ) (source : ℤ → Fin 6) (head : ℤ)
    (before : Fin c → Array sh rows ell) : Tapes (1+c) 2 :=
  CyclicRowCopy.payload source (fun j => word (words (before j))) head (fun _ => 0)

def childPayload (sh : Shape) (rows ell q : ℕ) (rho : Fin sh.chunk) {left k : ℕ}
    (visit : Visit sh.active left k) (dir : CompactSpectatorLeafGuardOriginal.Direction)
    (selected : Fin c) (source : ℤ → Fin 6) (head : ℤ) (before : Fin c → Array sh rows ell) :=
  CompactNativeRoleGuardedChildCaller.setRole (payload sh rows ell source head before) selected
    (CompactSpectatorLeafAxis.word
      (CompactSpectatorLeafGuardOriginal.result dir sh rows ell q rho visit (before selected)))

/-- This encoding is precisely the actual globally padded role bank used
by the stopped caller, including its retained source/head. -/
theorem reserved_payload (sh : Shape) (rows ell : ℕ) (hdiv : c∣rows)
    (f : Array sh rows ell) :
    CompactNativeRoleReservedBridge.rolePayload sh rows c ell hdiv f =
      payload sh (rows/c) ell (fun _ => blank) 0
        (fun j => CompactNativeRoleReservedBridge.role sh rows c ell hdiv f j) := by
  simp only [CompactNativeRoleReservedBridge.rolePayload,payload,words_tape]
  rfl

theorem reserved_rows_pos (rows : ℕ) (hc : 0<c) (hr : 0<rows) (hdiv : c∣rows) : 0<rows/c :=
  Nat.div_pos (Nat.le_of_dvd hr hdiv) hc

theorem reserved_width (sh : Shape) (rows ell q : ℕ) (hdiv : c∣rows)
    (f : Array sh rows ell) (hw : Width sh rows ell q f) :
    ∀ j,Width sh (rows/c) ell q (CompactNativeRoleReservedBridge.role sh rows c ell hdiv f j) := by
  intro j i
  exact hw _

theorem reserved_grid (sh : Shape) (rows ell q n M : ℕ) (hdiv : c∣rows)
    (f : Array sh rows ell) (hg : Grid sh rows ell q n M f) :
    ∀ j,Grid sh (rows/c) ell q n M (CompactNativeRoleReservedBridge.role sh rows c ell hdiv f j) := by
  intro j i
  exact hg _

/-- Exact compatibility with the real stopped caller's selected output.
The codec's polynomial payload expansion changes no address or row index. -/
theorem reserved_child (sh : Shape) (rows ell metadataP : ℕ) (hdiv : c∣rows)
    (rho : Fin sh.chunk) {left k : ℕ} (visit : Visit sh.active left k)
    (dir : CompactSpectatorLeafGuardOriginal.Direction) (selected : Fin c)
    (f : Array sh rows ell) :
    childPayload (NativePolynomialStageShape.shape sh ell metadataP) (rows/c) ell
      (metadataP-2*sh.bits) rho visit dir selected (fun _ => blank) 0
      (fun j => CompactNativeRoleReservedBridge.role sh rows c ell hdiv f j) =
      CompactNativeRoleGuardedChildCaller.setRole
        (CompactNativeRoleReservedBridge.rolePayload sh rows c ell hdiv f) selected
        (CompactNativeRoleGuardedChildCaller.resultWord dir sh rows c ell metadataP rho visit hdiv f selected) := by
  unfold childPayload CompactNativeRoleGuardedChildCaller.resultWord
  exact congrArg (fun pay => CompactNativeRoleGuardedChildCaller.setRole pay selected
    (CompactSpectatorLeafAxis.word (CompactSpectatorLeafGuardOriginal.result dir
      (NativePolynomialStageShape.shape sh ell metadataP) (rows/c) ell (metadataP-2*sh.bits) rho visit
      (CompactNativeRoleReservedBridge.role sh rows c ell hdiv f selected))))
    (reserved_payload sh rows ell hdiv f).symm

theorem payload_execute (sh : Shape) (rows ell q : ℕ) (rho : Fin sh.chunk) {left k : ℕ}
    (visit : Visit sh.active left k) (dir : CompactSpectatorLeafGuardOriginal.Direction)
    (selected : Fin c) (source : ℤ → Fin 6) (head : ℤ) (before : Fin c → Array sh rows ell) :
    CompactComplexSpectatorRoleSchedule.execute
      (fun j => word ((words (before j)).map (NativeSignedGapPromoteWord.result (arity^k))))
      (CompactComplexSpectatorPromoteFamily.spectatorList selected)
      (childPayload sh rows ell q rho visit dir selected source head before) =
      payload sh rows ell source head (aligned sh rows ell q rho visit dir selected before) := by
  have hs := CompactComplexSpectatorRoleSchedule.execute_source
    (fun j => word ((words (before j)).map (NativeSignedGapPromoteWord.result (arity^k))))
    (CompactComplexSpectatorPromoteFamily.spectatorList selected)
    (childPayload sh rows ell q rho visit dir selected source head before)
  have hzero : (0 : Fin (1+c))≠Fin.natAdd 1 selected := by
    intro he
    have hv := congrArg Fin.val he
    simp only [Fin.val_zero,Fin.val_natAdd] at hv
    omega
  apply congrArg₂ Tapes.mk
  · funext i
    induction i using Fin.addCases (m:=1) (n:=c) with
    | left i =>
      fin_cases i
      change _ = head
      exact hs.1.trans (by
        unfold childPayload CompactNativeRoleGuardedChildCaller.setRole setTape
        simp only [Function.update_of_ne hzero]
        rfl)
    | right j =>
      have h := CompactComplexSpectatorRoleSchedule.execute_slot
        (fun j => word ((words (before j)).map (NativeSignedGapPromoteWord.result (arity^k))))
        (CompactComplexSpectatorPromoteFamily.spectatorList selected)
        (childPayload sh rows ell q rho visit dir selected source head before) j
      simpa only [CompactComplexSpectatorPromoteFamily.spectatorList_mem,childPayload,payload,
        CyclicRowCopy.payload,CompactNativeRoleGuardedChildCaller.setRole,setTape,Function.update_apply,
        Tapes.append,Fin.addCases_right,ite_self] using h.1
  · funext i
    induction i using Fin.addCases (m:=1) (n:=c) with
    | left i =>
      fin_cases i
      change _ = source
      exact hs.2.trans (by
        unfold childPayload CompactNativeRoleGuardedChildCaller.setRole setTape
        simp only [Function.update_of_ne hzero]
        rfl)
    | right j =>
      have h := CompactComplexSpectatorRoleSchedule.execute_slot
        (fun j => word ((words (before j)).map (NativeSignedGapPromoteWord.result (arity^k))))
        (CompactComplexSpectatorPromoteFamily.spectatorList selected)
        (childPayload sh rows ell q rho visit dir selected source head before) j
      simp only [Fin.addCases_right]
      by_cases hj : j=selected
      · subst j
        simpa only [CompactComplexSpectatorPromoteFamily.spectatorList_mem,ne_self_iff_false,ite_false,
          childPayload,CompactNativeRoleGuardedChildCaller.setRole,setTape,Function.update_self,
          aligned,ite_true,words_tape,CompactSpectatorLeafAxis.word] using h.2
      · simpa [CompactComplexSpectatorPromoteFamily.spectatorList_mem,hj,
          aligned,ite_false,words_promote] using h.2

/-- All machine premises about the spectator fields are consequences of
the actual width and Visit; the output is the literal array whose common
grid was proved by stopped_from_path. The old live denominator is still
retained, ready for its paid installation only after this theorem. -/
theorem stopped_handoff (sh : Shape) (rows ell q : ℕ) (hr : 0<rows) (rho : Fin sh.chunk)
    {left k levels frames returned : ℕ}
    (path : CompactRecursiveDependencyBudget.Path sh.active left k levels frames returned)
    (dir : CompactSpectatorLeafGuardOriginal.Direction) (selected : Fin c)
    (before : Fin c → Array sh rows ell) (p C n : ℕ) (hp : p≤q)
    (hchunk : dependencyCoefficient C≤sh.chunk)
    (hwidth : ∀ role,Width sh rows ell q (before role))
    (hbefore : ∀ role,Grid sh rows ell q n
      (CompactRecursiveGridBudget.bound p C levels (frames+2*returned)) (before role))
    (cur tar : Fin s) (hne : cur≠tar) (len : Fin 66)
    (control : Tapes 43 2) (queue : Tapes 1 2)
    (scalar stage : ActiveRepairRankHeadersCommands.State) (tail : Tapes 22 2) (storage : Tapes s 2)
    (source : ℤ → Fin 6) (head : ℤ)
    (hcurrent : storage.head cur=1 ∧ storage.tape cur=RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits n))
    (htarget : storage.head tar=1 ∧ storage.tape tar=
      RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits (n+arity^k)))
    (hlength :
      (CompactComplexNativeCodecFrame.bank control queue scalar stage tail storage
        (childPayload sh rows ell q rho path.visit dir selected source head before)).head
          (CompactComplexSpectatorTargetBank.numericSlot len)=1 ∧
      (CompactComplexNativeCodecFrame.bank control queue scalar stage tail storage
        (childPayload sh rows ell q rho path.visit dir selected source head before)).tape
          (CompactComplexSpectatorTargetBank.numericSlot len)=
        RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits
          (ButterflySpectatorGeometry.Size rows sh.bits (2^ell)*(2*(half sh q+2))))) :
    let after := aligned sh rows ell q rho path.visit dir selected before
    let V := ButterflySpectatorGeometry.Size rows sh.bits (2^ell)*(2*(half sh q+2))
    HoareTime (CompactComplexSpectatorTargetFamily.compile CompactComplexSpectatorTargetBank.roleSlot
      (CompactComplexSpectatorTargetBank.oldSlot cur) (CompactComplexSpectatorTargetBank.oldSlot tar)
      (CompactComplexSpectatorTargetBank.numericSlot len)
      (CompactComplexSpectatorTargetBank.ports_injective cur tar hne len)
      (CompactComplexSpectatorPromoteFamily.spectatorList selected)).2
      (fun z => z=CompactComplexSpectatorTargetFamily.ready
        (CompactComplexNativeCodecFrame.bank control queue scalar stage tail storage
          (childPayload sh rows ell q rho path.visit dir selected source head before)))
      (fun z => z=CompactComplexSpectatorTargetFamily.ready
        (CompactComplexNativeCodecFrame.bank control queue scalar stage tail storage
          (payload sh rows ell source head after)))
      ((CompactComplexSpectatorPromoteFamily.spectatorList selected).length*(130*V+8*(n+arity^k)+360)) ∧
    (∀ role,Grid sh rows ell q (n+arity^k)
      (CompactRecursiveGridBudget.bound p C levels (frames+2*returned)*4^(arity^k)) (after role)) ∧
    (∀ role,Grid sh rows ell q (n+arity^k)
      (CompactRecursiveGridBudget.bound p C levels (frames+2*(returned+arity^k))) (after role)) ∧
    (∀ role,role≠selected → decoded sh rows ell q (n+arity^k) (after role)=
      decoded sh rows ell q n (before role)) := by
  dsimp only
  let V := ButterflySpectatorGeometry.Size rows sh.bits (2^ell)*(2*(half sh q+2))
  let child := childPayload sh rows ell q rho path.visit dir selected source head before
  have hgap : arity^k≤half sh q+1 := by
    have hbits := CompactSpectatorLeafSemantics.count_le_bits sh rho path.visit
    unfold half ButterflyGuard.halfWidth
    omega
  have hcur := CompactComplexSpectatorTargetBank.old_bank control queue scalar stage tail storage child cur
  have htar := CompactComplexSpectatorTargetBank.old_bank control queue scalar stage tail storage child tar
  have hrun := CompactComplexSpectatorTargetBank.spectators_runs cur tar hne len selected
    control queue scalar stage tail storage child (fun j => words (before j)) n (n+arity^k) V
    (by omega) (RecursiveChildQuotientsConstant.bits V)
    (by
      intro j w hw
      have hlen := words_width sh rows ell q (before j) (hwidth j) w hw
      omega)
    (fun j => words_nonempty sh rows ell q hr (before j) (hwidth j))
    (fun j => words_volume sh rows ell q (before j) (hwidth j))
    (RecursiveChildQuotientsConstant.bits_value V) (RecursiveChildQuotientsConstant.bits_canonical V)
    ⟨hcur.1.trans hcurrent.1,hcur.2.trans hcurrent.2⟩
    ⟨htar.1.trans htarget.1,htar.2.trans htarget.2⟩ hlength
    (by
      intro j hj
      have h := CompactComplexSpectatorTargetBank.role_bank control queue scalar stage tail storage child j
      have hne' : Fin.natAdd 1 j≠Fin.natAdd 1 selected := fun he => hj (Fin.natAdd_injective _ _ he)
      refine ⟨h.1.trans ?_,h.2.trans ?_⟩
      all_goals simp only [child,childPayload,CompactNativeRoleGuardedChildCaller.setRole,setTape,
        Function.update_of_ne hne',payload,CyclicRowCopy.payload,Tapes.append,Fin.addCases_right])
  have he := payload_execute sh rows ell q rho path.visit dir selected source head before
  simp only [Nat.add_sub_cancel_left] at hrun
  have hout := congrArg (fun pay => CompactComplexSpectatorTargetFamily.ready
    (CompactComplexNativeCodecFrame.bank control queue scalar stage tail storage pay)) he
  refine ⟨hrun.consequence (fun _ h => h) (fun _ h => h.trans hout) le_rfl,?_⟩
  exact CompactComplexChildGridPromoted.stopped_from_path sh rows ell q rho path path.visit dir selected before
    p C n hp hchunk hwidth hbefore

end
end IntegerMultBounds.Machine.CompactComplexStoppedGridHandoff
