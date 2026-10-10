import IntegerMultBounds.Machine.CompactComplexSpectatorTargetBank
import IntegerMultBounds.Machine.CompactComplexControllerDenominator

/-! Physically install the certified common grid only after spectator promotion.
The existing denominator commit routine occupies the fixed original root prefix;
all later controller stacks, immutable scalar descriptors and role streams are
outside its placement. This is descriptor execution, not a claim that changing
a header alone aligns the coefficients. -/
namespace IntegerMultBounds.Machine.CompactComplexControllerAlignedCommit
noncomputable section
open CompactComplexNativeCodecFrame (permanentTapes bank)
open CompactComplexSpectatorTargetBank (oldSlot)
open CompactComplexControllerDenominator (size)
open SharedPlacementAlphabet (setTape)
open RecursiveChildQuotientsConstant (bits)
variable {s c : ℕ}

private def slot (i : Fin (size 0)) : Fin (permanentTapes (10+s) c) :=
  ⟨i.val,by have := i.isLt; unfold size permanentTapes CompactComplexNativeRoleBridge.publicTapes CompactComplexControllerNativeFrame.tapes at *; omega⟩
private theorem slot_injective : Function.Injective (slot (s:=s) (c:=c)) := by
  intro i j h
  exact Fin.ext (congrArg (fun x : Fin (permanentTapes (10+s) c) => x.val) h)
private def placement := InjectivePlacement.placement (slot (s:=s) (c:=c)) slot_injective
  (by unfold size permanentTapes CompactComplexNativeRoleBridge.publicTapes CompactComplexControllerNativeFrame.tapes; omega :
    size 0+(permanentTapes (10+s) c-size 0)=permanentTapes (10+s) c)

def current : Fin (permanentTapes (10+s) c) := oldSlot ⟨7,by omega⟩
def target : Fin (permanentTapes (10+s) c) := oldSlot ⟨8,by omega⟩
def program := Placement.placed (CompactComplexControllerDenominator.commitProgram (s:=0))
  (placement (s:=s) (c:=c))
def output (v : Tapes (permanentTapes (10+s) c) 2) (n : ℕ) :=
  setTape (setTape v current (RadixZeroFill.encodedBinary (bits n)) 1) target (fun _ => blank) 0

private theorem current_slot : slot (CompactComplexControllerDenominator.current (s:=0))=
    (current : Fin (permanentTapes (10+s) c)) := by
  apply Fin.ext
  rfl
private theorem target_slot : slot (CompactComplexControllerDenominator.target (s:=0))=
    (target : Fin (permanentTapes (10+s) c)) := by
  apply Fin.ext
  rfl

private theorem replace_two {m u t a : ℕ} (e : Fin (m+u) ≃ Fin t) (v : Tapes t a)
    (i j : Fin m) (f g : ℤ → Fin (a+4)) (p q : ℤ) :
    Placement.replace e v (setTape (setTape (Placement.active e v) i f p) j g q)=
      setTape (setTape v (e (Fin.castAdd u i)) f p) (e (Fin.castAdd u j)) g q := by
  apply congrArg₂ Tapes.mk
  · funext z
    obtain ⟨z,rfl⟩ := e.surjective z
    induction z using Fin.addCases with
    | left k =>
      simp only [Equiv.symm_apply_apply,Tapes.append,Fin.addCases_left]
      simp [setTape,Placement.active,Function.update_apply,e.injective.eq_iff]
    | right k =>
      simp only [Equiv.symm_apply_apply,Tapes.append,Fin.addCases_right]
      have hi : e (Fin.natAdd m k)≠e (Fin.castAdd u i) := by
        intro h; have hv := congrArg Fin.val (e.injective h); simp only [Fin.val_natAdd,Fin.val_castAdd] at hv; omega
      have hj : e (Fin.natAdd m k)≠e (Fin.castAdd u j) := by
        intro h; have hv := congrArg Fin.val (e.injective h); simp only [Fin.val_natAdd,Fin.val_castAdd] at hv; omega
      simp only [setTape,Function.update_of_ne hi,Function.update_of_ne hj,Placement.extra]
  · funext z x
    obtain ⟨z,rfl⟩ := e.surjective z
    induction z using Fin.addCases with
    | left k =>
      simp only [Equiv.symm_apply_apply,Tapes.append,Fin.addCases_left]
      simp [setTape,Placement.active,Function.update_apply,e.injective.eq_iff]
    | right k =>
      simp only [Equiv.symm_apply_apply,Tapes.append,Fin.addCases_right]
      have hi : e (Fin.natAdd m k)≠e (Fin.castAdd u i) := by
        intro h; have hv := congrArg Fin.val (e.injective h); simp only [Fin.val_natAdd,Fin.val_castAdd] at hv; omega
      have hj : e (Fin.natAdd m k)≠e (Fin.castAdd u j) := by
        intro h; have hv := congrArg Fin.val (e.injective h); simp only [Fin.val_natAdd,Fin.val_castAdd] at hv; omega
      simp only [setTape,Function.update_of_ne hi,Function.update_of_ne hj,Placement.extra]

/-- Exact execution on the actual bank with no copied role data or inserted
storage. Both descriptor inputs are genuine runtime words. -/
theorem runs (v : Tapes (permanentTapes (10+s) c) 2) (n targetN : ℕ)
    (hc : v.tape current=RadixZeroFill.encodedBinary (bits n)) (hch : v.head current=1)
    (ht : v.tape target=RadixZeroFill.encodedBinary (bits targetN)) (hth : v.head target=1) :
    HoareTime program (fun z => z=v) (fun z => z=output v targetN)
      (2*(bits n).length+4*(bits targetN).length+15) := by
  let active := Placement.active placement v
  have ha : active.tape (CompactComplexControllerDenominator.current (s:=0))=
      BinaryDescriptorStack.descriptor (bits n) := by
    simpa only [active,Placement.active,placement,InjectivePlacement.active_slot,current_slot,
      BinaryDescriptorStackRoundtrip.descriptor_encoded] using hc
  have hah : active.head (CompactComplexControllerDenominator.current (s:=0))=1 := by
    simpa only [active,Placement.active,placement,InjectivePlacement.active_slot,current_slot] using hch
  have hb : active.tape (CompactComplexControllerDenominator.target (s:=0))=
      BinaryDescriptorStack.descriptor (bits targetN) := by
    simpa only [active,Placement.active,placement,InjectivePlacement.active_slot,target_slot,
      BinaryDescriptorStackRoundtrip.descriptor_encoded] using ht
  have hbh : active.head (CompactComplexControllerDenominator.target (s:=0))=1 := by
    simpa only [active,Placement.active,placement,InjectivePlacement.active_slot,target_slot] using hth
  have h := Placement.hoare_at (CompactComplexControllerDenominator.commit active n targetN ha hah hb hbh)
    placement v rfl
  apply h.consequence (fun _ h => h) _ le_rfl
  rintro z ⟨small,rfl,rfl⟩
  unfold CompactComplexControllerDenominator.committed
  dsimp only [active]
  rw [replace_two]
  simp only [placement,InjectivePlacement.active_slot,current_slot,target_slot,output]

/-- Copying/erasing both headers is linear in their actual values. -/
theorem cost_le (n targetN : ℕ) :
    2*(bits n).length+4*(bits targetN).length+15≤2*n+4*targetN+21 := by
  have hn := ActiveRepairRankHeadersCommands.bits_length n
  have ht := ActiveRepairRankHeadersCommands.bits_length targetN
  omega

theorem outside (v : Tapes (permanentTapes (10+s) c) 2) (n : ℕ)
    (i : Fin (permanentTapes (10+s) c)) (hc : i≠current) (ht : i≠target) :
    (output v n).head i=v.head i ∧ (output v n).tape i=v.tape i := by
  simp only [output,setTape,Function.update_of_ne hc,Function.update_of_ne ht,and_self]

theorem installed (v : Tapes (permanentTapes (10+s) c) 2) (n : ℕ) :
    (output v n).head current=1 ∧
      (output v n).tape current=RadixZeroFill.encodedBinary (bits n) := by
  have hne : (current : Fin (permanentTapes (10+s) c))≠target := by
    intro h; have hv := congrArg Fin.val h
    simp [current,target,oldSlot,CompactComplexControllerNativeFrame.storageSlot] at hv
  simp only [output,setTape,Function.update_of_ne hne,Function.update_self,and_self]


open RadixSignedShiftRight (Word)
open NativeSignedReturnStream (volume)
open NativeSignedGapPromoteReturn (word)
open CompactComplexSpectatorTargetBank (roleSlot numericSlot ports_injective)
open CompactComplexSpectatorPromoteFamily (spectatorList)

private theorem old_current_target : (⟨7,by omega⟩ : Fin (10+s))≠⟨8,by omega⟩ := by
  intro h
  have hv := congrArg Fin.val h
  norm_num at hv

private def compose {t : ℕ} (p q : Σ r,Program t r 2) : Σ r,Program t r 2 :=
  ⟨_,seq p.2 q.2⟩
private theorem compose_runs {t : ℕ} (p q : Σ r,Program t r 2)
    {pre mid post : TapePred t 2} {b d : ℕ}
    (hp : HoareTime p.2 pre mid b) (hq : HoareTime q.2 mid post d) :
    HoareTime (compose p q).2 pre post (b+1+d) := hp.seq hq

def promoteProgram (len : Fin 66) (selected : Fin c) :=
  compose (CompactComplexSpectatorTargetFamily.compile (roleSlot (s:=10+s) (c:=c))
    (current (s:=s) (c:=c)) target (numericSlot len)
    (ports_injective (s:=10+s) (c:=c) ⟨7,by omega⟩ ⟨8,by omega⟩ old_current_target len) (spectatorList selected))
    ⟨_,extend (program (s:=s) (c:=c)) 10⟩

private theorem runs_framed (v : Tapes (permanentTapes (10+s) c) 2) (n targetN : ℕ)
    (hc : v.tape current=RadixZeroFill.encodedBinary (bits n)) (hch : v.head current=1)
    (ht : v.tape target=RadixZeroFill.encodedBinary (bits targetN)) (hth : v.head target=1) :
    HoareTime (extend (program (s:=s) (c:=c)) 10)
      (fun z => z=CompactComplexSpectatorTargetFamily.ready v)
      (fun z => z=CompactComplexSpectatorTargetFamily.ready (output v targetN))
      (2*(bits n).length+4*(bits targetN).length+15) := by
  have h := (runs v n targetN hc hch ht hth).extend (SharedBank.empty 10 2)
  apply h.consequence _ _ le_rfl
  · rintro z rfl
    exact ⟨v,rfl,rfl⟩
  · rintro z ⟨small,rfl,rfl⟩
    rfl

attribute [local irreducible] CompactComplexSpectatorTargetFamily.compile seq

/-- The selected child remains untouched while every spectator is physically
promoted. Only then is the true live header installed and the target erased;
all private storage is blank again at the final endpoint. -/
theorem promote_commit_runs (len : Fin 66) (selected : Fin c)
    (control : Tapes 43 2) (queue : Tapes 1 2)
    (scalar stage : ActiveRepairRankHeadersCommands.State) (tail : Tapes 22 2)
    (storage : Tapes (10+s) 2) (payload : Tapes (1+c) 2) (ws : Fin c → List Word)
    (n targetN V : ℕ) (hle : n≤targetN) (ls : List Bool)
    (hd : ∀ j w,w∈ws j → targetN-n≤w.length) (hn : ∀ j,ws j≠[])
    (hv : ∀ j,volume (ws j)=V) (hlen : Counter.value ls=V)
    (hcanonical : GrowingCounterData.Canonical ls)
    (hc : storage.head ⟨7,by omega⟩=1 ∧
      storage.tape ⟨7,by omega⟩=RadixZeroFill.encodedBinary (bits n))
    (ht : storage.head ⟨8,by omega⟩=1 ∧
      storage.tape ⟨8,by omega⟩=RadixZeroFill.encodedBinary (bits targetN))
    (hlength : (bank control queue scalar stage tail storage payload).head (numericSlot len)=1 ∧
      (bank control queue scalar stage tail storage payload).tape (numericSlot len)=RadixZeroFill.encodedBinary ls)
    (hsource : ∀ j,j≠selected →
      (bank control queue scalar stage tail storage payload).head (roleSlot j)=0 ∧
      (bank control queue scalar stage tail storage payload).tape (roleSlot j)=word (ws j)) :
    HoareTime (promoteProgram (s:=s) len selected).2
      (fun z => z=CompactComplexSpectatorTargetFamily.ready
        (bank control queue scalar stage tail storage payload))
      (fun z => z=CompactComplexSpectatorTargetFamily.ready
        (output (bank control queue scalar stage tail storage
          (CompactComplexSpectatorRoleSchedule.execute
            (fun j => word ((ws j).map (NativeSignedGapPromoteWord.result (targetN-n))))
              (spectatorList selected) payload)) targetN))
      ((spectatorList selected).length*(130*V+8*targetN+360)+1+
        (2*(bits n).length+4*(bits targetN).length+15)) := by
  have current_word (payload' : Tapes (1+c) 2) :
      (bank control queue scalar stage tail storage payload').head current=1 ∧
      (bank control queue scalar stage tail storage payload').tape current=
        RadixZeroFill.encodedBinary (bits n) := by
    have h := CompactComplexSpectatorTargetBank.old_bank control queue scalar stage tail storage payload' ⟨7,by omega⟩
    exact ⟨h.1.trans hc.1,h.2.trans hc.2⟩
  have target_word (payload' : Tapes (1+c) 2) :
      (bank control queue scalar stage tail storage payload').head target=1 ∧
      (bank control queue scalar stage tail storage payload').tape target=
        RadixZeroFill.encodedBinary (bits targetN) := by
    have h := CompactComplexSpectatorTargetBank.old_bank control queue scalar stage tail storage payload' ⟨8,by omega⟩
    exact ⟨h.1.trans ht.1,h.2.trans ht.2⟩
  have h0 := CompactComplexSpectatorTargetBank.spectators_runs ⟨7,by omega⟩ ⟨8,by omega⟩
    old_current_target len selected control queue scalar stage tail storage payload ws n targetN V hle ls
    hd hn hv hlen hcanonical (current_word payload) (target_word payload) hlength hsource
  let finalPayload := CompactComplexSpectatorRoleSchedule.execute
    (fun j => word ((ws j).map (NativeSignedGapPromoteWord.result (targetN-n)))) (spectatorList selected) payload
  have h1 := runs_framed (bank control queue scalar stage tail storage finalPayload) n targetN
    (current_word finalPayload).2 (current_word finalPayload).1
    (target_word finalPayload).2 (target_word finalPayload).1
  have combined := compose_runs _ ⟨_,extend (program (s:=s) (c:=c)) 10⟩ h0 h1
  exact combined

end
end IntegerMultBounds.Machine.CompactComplexControllerAlignedCommit
