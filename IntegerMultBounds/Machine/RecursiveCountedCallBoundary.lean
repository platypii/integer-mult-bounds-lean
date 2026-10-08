import IntegerMultBounds.Machine.RecursiveCallCount
import IntegerMultBounds.Machine.RoleArrayCallBoundary
import IntegerMultBounds.Machine.SharedBankFamily

/-! Actual count lifecycle around the separate payload-call blocks. Volume is
computed from six canonical headers; both controls are blank at recursive
boundaries. Recovery recomputes the count from the restored role-parent headers. -/
namespace IntegerMultBounds.Machine.RecursiveCountedCallBoundary
noncomputable section
open RoleArrayFrames
open RoleArrayCall (entered)
open RecursiveInterchangeLayout (Descriptor volume)
open SharedPlacementAlphabet (setTape)
variable {q t : ℕ}

private theorem saveOne_count (L : Layout t) (i : Role L) (n : ℕ) (v : Tapes t q)
    (f : ℤ → Fin (q+4)) (p : ℤ) :
    saveOne L i n (setTape v L.count f p) = setTape (saveOne L i n v) L.count f p := by
  apply congrArg₂ Tapes.mk <;> funext j <;>
    by_cases hs : j = L.stack <;> by_cases hi : j = i.val <;> by_cases hc : j = L.count <;>
      simp_all [saveOne,RoleArrayStackAt.pushed,slots,setTape,L.stack_count,L.stack_count.symm,i.property.2.2,i.property.2.2.symm,i.property.1]

private theorem saved_count (L : Layout t) (ops : List (Role L)) (n : ℕ) (v : Tapes t q)
    (f : ℤ → Fin (q+4)) (p : ℤ) :
    saved L ops n (setTape v L.count f p) = setTape (saved L ops n v) L.count f p := by
  induction ops generalizing v with
  | nil => rfl
  | cons i ops ih => rw [saved,saveOne_count,ih,saved]

theorem entered_count (L : Layout t) (ops : List (Role L)) (src dst : Role L)
    (n : ℕ) (v : Tapes t q) (f : ℤ → Fin (q+4)) (p : ℤ) :
    entered L ops src dst n (setTape v L.count f p) = setTape (entered L ops src dst n v) L.count f p := by
  unfold entered
  rw [saved_count]
  apply congrArg₂ Tapes.mk <;> funext j <;>
    by_cases hs : j = src.val <;> by_cases hd : j = dst.val <;> by_cases hc : j = L.count <;>
      simp_all [RoleArrayMove.moved,RoleArrayCall.slots,setTape,src.property.2.2,dst.property.2.2,src.property.2.2.symm,dst.property.2.2.symm]

theorem entered_control_frame (L : Layout t) (ops : List (Role L)) (src dst : Role L)
    (n : ℕ) (v : Tapes t q) :
    (entered L ops src dst n v).head L.count = v.head L.count ∧
    (entered L ops src dst n v).tape L.count = v.tape L.count := by
  have hf := saved_frame L ops n v L.count L.stack_count.symm (fun i _ => i.property.2.2.symm)
  simpa [entered,RoleArrayMove.moved,RoleArrayCall.slots,setTape,src.property.2.2.symm,dst.property.2.2.symm] using hf

def program (hq : 2 ≤ q) (slot : Fin 8 → Fin t) (hi : Function.Injective slot)
    (L : Layout t) (ops : List (Role L)) (src dst : Role L) (hne : src ≠ dst) :=
  seq (seq (RecursiveCallCount.program hq slot hi)
    (extend (RoleArrayCallBoundary.entryProgram L ops src dst hne) 34))
    (extend (BinaryDescriptorCleanupList.oneProgram L.count) 34)

def recoverProgram (hq : 2 ≤ q) (slot : Fin 8 → Fin t) (hi : Function.Injective slot)
    (L : Layout t) (ops : List (Role L)) (src dst : Role L) (hne : src ≠ dst) :=
  seq (seq (RecursiveCallCount.program hq slot hi)
    (extend (RoleArrayCallBoundary.returnProgram L ops src dst hne) 34))
    (extend (BinaryDescriptorCleanupList.oneProgram L.count) 34)

private theorem controls_counted (L : Layout t) (slot : Fin 8 → Fin t)
    (hclock : slot 0 = L.clock) (hcount : slot 1 = L.count) (v : Tapes t q)
    (hs : Fin 6 → List Bool) (hr : RecursiveCallCount.Ready slot hs v) (bs : List Bool) :
    Controls L bs (RecursiveCallCount.counted slot v bs) := by
  obtain ⟨hc,tc,_,_,_⟩ := hr
  rw [hclock] at hc tc
  have hb : RadixZeroFill.encodedBinary (q := q) bs = CountedLoopReuseAlphabet.binary bs := by
    rw [← BinaryDescriptorStackRoundtrip.descriptor_encoded,RoleArrayStackMoves.binary_descriptor]
  simp [Controls,RecursiveCallCount.counted,hcount,setTape,L.clock_count,hc,tc,hb]

private theorem clears_count (L : Layout t) (v : Tapes t q) (bs : List Bool)
    (hh : v.head L.count = 0) (ht : v.tape L.count = fun _ => blank) :
    HoareTime (BinaryDescriptorCleanupList.oneProgram L.count)
      (fun w => w = setTape v L.count (RadixZeroFill.encodedBinary bs) 1) (fun w => w = v) (2*bs.length+4) := by
  have h := BinaryDescriptorCleanupList.one_hoare L.count (setTape v L.count (RadixZeroFill.encodedBinary bs) 1) bs
    (by simp [setTape,BinaryDescriptorStackRoundtrip.descriptor_encoded]) (by simp [setTape])
  apply h.consequence (fun _ h => h) _ le_rfl
  intro w hw
  rw [hw,SharedPlacementAlphabet.setTape_setTape,← ht,← hh,SharedPlacementAlphabet.setTape_self]

/-- Count construction, actual payload entry, and count erasure are all paid;
no initialized length descriptor survives the recursive boundary. -/
theorem enter_hoare (hq : 2 ≤ q) (slot : Fin 8 → Fin t) (hi : Function.Injective slot)
    (L : Layout t) (hclock : slot 0 = L.clock) (hcount : slot 1 = L.count)
    (ops : List (Role L)) (hu : ops.Nodup) (src dst : Role L) (hne : src ≠ dst)
    (hsrc : src ∉ ops) (hdst : dst ∉ ops) (v : Tapes t q)
    (d : Descriptor) (hs : Fin 6 → List Bool) (hready : RecursiveCallCount.Ready slot hs v)
    (hv : RecursiveDimensionBank.Headers d hs) (hp : d.Positive)
    (hr : ∀ i ∈ ops, v.head i = 0 ∧ RoleArrayStack.Supported (v.tape i) (volume q d))
    (hsource : v.head src.val = 0 ∧ RoleArrayStack.Supported (v.tape src.val) (volume q d))
    (hcommon : v.head dst.val = 0 ∧ v.tape dst.val = fun _ => blank) :
    HoareTime (program hq slot hi L ops src dst hne) (fun w => w = CleanSubbank.bank v)
      (fun w => w = CleanSubbank.bank (entered L ops src dst (volume q d) v))
      ((88*ops.length+51883)*volume q d) := by
  let bs := RecursiveVolumeConstruct.bits (q := q) d
  have hV := RecursiveAffinePrepare.volume_positive hq d hp
  have hc := controls_counted L slot hclock hcount v hs hready bs
  have hgen := RecursiveCallCount.realizes hq slot hi v d hs hready hv hp
  have hentry := RoleArrayCallBoundary.entry_hoare L ops hu src dst hne hsrc hdst
    (RecursiveCallCount.counted slot v bs) bs (volume q d) (RecursiveVolumeConstruct.bits_value d)
    (RecursiveVolumeConstruct.bits_canonical d) hV hc
    (by intro i hi; simpa [RecursiveCallCount.counted,hcount,setTape,i.property.2.2] using hr i hi)
    (by simpa [RecursiveCallCount.counted,hcount,setTape,src.property.2.2] using hsource)
    (by simpa [RecursiveCallCount.counted,hcount,setTape,dst.property.2.2] using hcommon)
  have he : entered L ops src dst (volume q d) (RecursiveCallCount.counted slot v bs) =
      setTape (entered L ops src dst (volume q d) v) L.count (RadixZeroFill.encodedBinary bs) 1 := by
    rw [RecursiveCallCount.counted,hcount,entered_count]
  rw [he] at hentry
  have hf := entered_control_frame L ops src dst (volume q d) v
  have hh := hready.2.2.1
  have ht := hready.2.2.2.1
  rw [hcount] at hh ht
  have hclear := clears_count L (entered L ops src dst (volume q d) v) bs (hf.1.trans hh) (hf.2.trans ht)
  have hext := hoare_extend_eq hentry (SharedBank.empty 34 q)
  have hcext := hoare_extend_eq hclear (SharedBank.empty 34 q)
  have hall := (hgen.seq hext).seq hcext
  have hlen := RecursiveVolumeClean.bits_length (q := q) d
  exact hall.consequence (fun _ h => h) (fun _ h => h) (by dsimp [bs] at *; nlinarith)

/-- After header restoration and PC pop, regenerate the original role volume,
recover the payload frame, and erase the count again. -/
theorem recover_hoare (hq : 2 ≤ q) (slot : Fin 8 → Fin t) (hi : Function.Injective slot)
    (L : Layout t) (hclock : slot 0 = L.clock) (hcount : slot 1 = L.count)
    (ops : List (Role L)) (hu : ops.Nodup) (src dst : Role L) (hne : src ≠ dst)
    (hsrc : src ∉ ops) (hdst : dst ∉ ops) (v : Tapes t q)
    (d : Descriptor) (hs : Fin 6 → List Bool) (hready : RecursiveCallCount.Ready slot hs v)
    (hentered : RecursiveCallCount.Ready slot hs (entered L ops src dst (volume q d) v))
    (hv : RecursiveDimensionBank.Headers d hs) (hp : d.Positive)
    (hr : ∀ i ∈ ops, v.head i = 0 ∧ RoleArrayStack.Supported (v.tape i) (volume q d))
    (hfree : Free L ops (volume q d) v)
    (hsource : v.head src.val = 0 ∧ RoleArrayStack.Supported (v.tape src.val) (volume q d))
    (hcommon : v.head dst.val = 0 ∧ v.tape dst.val = fun _ => blank) :
    HoareTime (recoverProgram hq slot hi L ops src dst hne)
      (fun w => w = CleanSubbank.bank (entered L ops src dst (volume q d) v))
      (fun w => w = CleanSubbank.bank v) ((92*ops.length+51883)*volume q d) := by
  let bs := RecursiveVolumeConstruct.bits (q := q) d
  have hV := RecursiveAffinePrepare.volume_positive hq d hp
  have hc := controls_counted L slot hclock hcount v hs hready bs
  have hgen := RecursiveCallCount.realizes hq slot hi (entered L ops src dst (volume q d) v) d hs hentered hv hp
  have hreturn := RoleArrayCallBoundary.return_hoare L ops hu src dst hne hsrc hdst
    (RecursiveCallCount.counted slot v bs) bs (volume q d) (RecursiveVolumeConstruct.bits_value d)
    (RecursiveVolumeConstruct.bits_canonical d) hV hc
    (by intro i hi; simpa [RecursiveCallCount.counted,hcount,setTape,i.property.2.2] using hr i hi)
    (by simpa [Free,RecursiveCallCount.counted,hcount,setTape,L.stack_count] using hfree)
    (by simpa [RecursiveCallCount.counted,hcount,setTape,src.property.2.2] using hsource)
    (by simpa [RecursiveCallCount.counted,hcount,setTape,dst.property.2.2] using hcommon)
  have he : entered L ops src dst (volume q d) (RecursiveCallCount.counted slot v bs) =
      RecursiveCallCount.counted slot (entered L ops src dst (volume q d) v) bs := by
    simp only [RecursiveCallCount.counted,hcount,entered_count]
  rw [he] at hreturn
  have hh := hready.2.2.1
  have ht := hready.2.2.2.1
  rw [hcount] at hh ht
  have hclear := clears_count L v bs hh ht
  have hclear' : HoareTime (BinaryDescriptorCleanupList.oneProgram L.count)
      (fun w => w = RecursiveCallCount.counted slot v bs) (fun w => w = v) (2*bs.length+4) := by
    simpa only [RecursiveCallCount.counted,hcount] using hclear
  have hreturn' := hoare_extend_eq hreturn (SharedBank.empty 34 q)
  have hclear'' := hoare_extend_eq hclear' (SharedBank.empty 34 q)
  have hall := (hgen.seq hreturn').seq hclear''
  have hlen := RecursiveVolumeClean.bits_length (q := q) d
  exact hall.consequence (fun _ h => h) (fun _ h => h) (by dsimp [bs] at *; nlinarith)

/-- Leading permanent slots are suitable for a Shared50 cyclic implementation. -/
def entrySkeleton (hq : 2 ≤ q) (slot : Fin 8 → Fin t) (hi : Function.Injective slot)
    (L : Layout t) (ops : List (Role L)) (src dst : Role L) (hne : src ≠ dst) :=
  SharedBankFamily.ofProgram (program hq slot hi L ops src dst hne)

def recoverSkeleton (hq : 2 ≤ q) (slot : Fin 8 → Fin t) (hi : Function.Injective slot)
    (L : Layout t) (ops : List (Role L)) (src dst : Role L) (hne : src ≠ dst) :=
  SharedBankFamily.ofProgram (recoverProgram hq slot hi L ops src dst hne)


end
end IntegerMultBounds.Machine.RecursiveCountedCallBoundary
