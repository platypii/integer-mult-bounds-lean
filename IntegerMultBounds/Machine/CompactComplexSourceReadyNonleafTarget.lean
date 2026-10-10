import IntegerMultBounds.Machine.CompactComplexSourceReadyStoppedLeafCountBudget
import IntegerMultBounds.Machine.CompactComplexSourceReadyFullNodeControls
import IntegerMultBounds.Machine.CompactComplexControllerExactReturnBudget

/-! A genuine positive nonleaf constructs its fixed return target from the
incoming live word and physical count. Count expansion/restoration retain the
original child geometry; no final advanced-live value is mistaken for input. -/
namespace IntegerMultBounds.Machine.CompactComplexSourceReadyNonleafTarget
noncomputable section
open CompactGadgetReservationShape (Shape)
open CompactComplexRecursiveGeometry
open CompactComplexSourceReadyLeafCodec (headers numericProgram numeric_runs headers_active headers_headers headers_original)
open CompactComplexSourceReadyWorkspace (publicTapes ready)
open CompactComplexNonleafRoleSourceReturn (base)
open CompactComplexNonleafRoleEntry (headerPlacement)
open CompactSpectatorLeafCountBudget (expand restore expanded)
open SharedPlacementAlphabet (setTape)
open RecursiveChildQuotientsConstant (bits)
variable {s c : ℕ}
namespace Ports
export CompactComplexSourceReadyLeafDenominator (current target volume work placement active installed)
end Ports

def installProgram := Placement.placed CompactNativeDenominatorTarget.networkProgram (Ports.placement (s:=s) (c:=c))
def targeted (v : Tapes (publicTapes s c) 2) (n : ℕ) :=
  setTape v CompactComplexNonleafRoleChildBank.target (RadixZeroFill.encodedBinary (bits n)) 1

/-- Physical addition of the complete node count twice leaves incoming live
unchanged and stores the genuine nonleaf target, with private work erased. -/
theorem install (v : Tapes (publicTapes s c) 2) (n fullVolume : ℕ)
    (hn : v.head CompactComplexNonleafRoleChildBank.current=1 ∧
      v.tape CompactComplexNonleafRoleChildBank.current=RadixZeroFill.encodedBinary (bits n))
    (hv : v.head (CompactComplexNonleafRoleChildBank.numeric 7)=1 ∧
      v.tape (CompactComplexNonleafRoleChildBank.numeric 7)=RadixZeroFill.encodedBinary (bits fullVolume))
    (ht : v.head CompactComplexNonleafRoleChildBank.target=0 ∧
      v.tape CompactComplexNonleafRoleChildBank.target=(fun _ => blank)) :
    HoareTime (installProgram (s:=s) (c:=c)) (fun z => z=ready v)
      (fun z => z=ready (targeted v (n+2*fullVolume)))
      (CompactNativeDenominatorTarget.networkCost n fullVolume) := by
  have ha : Placement.active Ports.placement (ready v)=CompactNativeDenominatorTarget.input n fullVolume := by
    apply Ports.active (ready v) n fullVolume
    · simpa only [CompactComplexSourceReadyLeafDenominator.current,
        CompactComplexSourceReadyWorkspace.ready,CompactComplexSourceReadyWorkspace.bank,
        Tapes.append,Fin.addCases_left] using hn
    · simpa only [CompactComplexSourceReadyLeafDenominator.volume,
        CompactComplexSourceReadyWorkspace.ready,CompactComplexSourceReadyWorkspace.bank,
        Tapes.append,Fin.addCases_left] using hv
    · simpa only [CompactComplexSourceReadyLeafDenominator.target,
        CompactComplexSourceReadyWorkspace.ready,CompactComplexSourceReadyWorkspace.bank,
        Tapes.append,Fin.addCases_left] using ht
    · simp only [CompactComplexSourceReadyLeafDenominator.work,
        CompactComplexSourceReadyWorkspace.ready,CompactComplexSourceReadyWorkspace.bank,
        Tapes.append,Fin.addCases_right,SharedBank.empty,and_self]
  have h := Placement.hoare_at (CompactNativeDenominatorTarget.network_runs n fullVolume)
    Ports.placement (ready v) ha
  apply h.consequence (fun _ hz => hz) _ le_rfl
  rintro z ⟨w,rfl,rfl⟩
  have he : CompactNativeDenominatorTarget.bank n fullVolume (some (n+2*fullVolume))=
      setTape (CompactNativeDenominatorTarget.input n fullVolume) (2:Fin 4)
        (RadixZeroFill.encodedBinary (bits (n+2*fullVolume))) 1 := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  rw [he,←ha,PlacedDescriptorConstruction.replace_setTape]
  simp only [CompactComplexSourceReadyLeafDenominator.placement,InjectivePlacement.active_slot,
    CompactComplexSourceReadyLeafDenominator.slots,Matrix.cons_val_two]
  change setTape ((v.append (SharedBank.empty CompactComplexSourceReadyWorkspace.leafTapes 2)).append
    (SharedBank.empty 10 2)) (Fin.castAdd 10 (Fin.castAdd CompactComplexSourceReadyWorkspace.leafTapes
      CompactComplexNonleafRoleChildBank.target)) _ _=ready (targeted v (n+2*fullVolume))
  rw [SharedPlacementAlphabet.setTape_append_left,SharedPlacementAlphabet.setTape_append_left]
  rfl

private theorem current_outside (j : Fin 43) :
    CompactComplexNonleafRoleChildBank.current (s:=s) (c:=c)≠CompactComplexSourceReadyLeafCodec.slot (s:=10+s) j := by
  intro h
  have hv := congrArg Fin.val h
  have hj := j.isLt
  simp only [CompactComplexNonleafRoleChildBank.current,CompactComplexNonleafRoleChildBank.storage,
    CompactComplexSourceReadyLeafCodec.slot,CompactComplexNonleafRoleEntry.numeric,
    CompactComplexNativeCodecFrame.headerSlot,CompactComplexSpectatorTargetBank.oldSlot,
    CompactComplexControllerNativeFrame.storageSlot,CompactComplexControllerNativeFrame.nativeSlot,
    Fin.val_castAdd,Fin.val_natAdd] at hv
  omega
private theorem target_outside (j : Fin 43) :
    CompactComplexNonleafRoleChildBank.target (s:=s) (c:=c)≠CompactComplexSourceReadyLeafCodec.slot (s:=10+s) j := by
  intro h
  have hv := congrArg Fin.val h
  have hj := j.isLt
  simp only [CompactComplexNonleafRoleChildBank.target,CompactComplexNonleafRoleChildBank.storage,
    CompactComplexSourceReadyLeafCodec.slot,CompactComplexNonleafRoleEntry.numeric,
    CompactComplexNativeCodecFrame.headerSlot,CompactComplexSpectatorTargetBank.oldSlot,
    CompactComplexControllerNativeFrame.storageSlot,CompactComplexControllerNativeFrame.nativeSlot,
    Fin.val_castAdd,Fin.val_natAdd] at hv
  omega

private theorem replace_setTape {n u t a : ℕ} (e : Fin (n+u) ≃ Fin t)
    (v : Tapes t a) (small : Tapes n a) (i : Fin t)
    (hi : ∀ j,i≠e (Fin.castAdd u j)) (f : ℤ → Fin (a+4)) (p : ℤ) :
    Placement.replace e (setTape v i f p) small=setTape (Placement.replace e v small) i f p := by
  obtain ⟨j,rfl⟩ := e.surjective i
  induction j using Fin.addCases with
  | left j => exact False.elim (hi j rfl)
  | right j =>
    apply congrArg₂ Tapes.mk <;> funext k
    all_goals obtain ⟨k,rfl⟩ := e.surjective k
    all_goals induction k using Fin.addCases with
    | left k =>
      have hn : e (Fin.castAdd u k)≠e (Fin.natAdd n j) := by
        intro h;have hv := congrArg Fin.val (e.injective h);simp only [Fin.val_castAdd,Fin.val_natAdd] at hv;omega
      simp [Placement.replace,Placement.combine,Tapes.reindex,Tapes.append,setTape,hn]
    | right k =>
      by_cases hk : k=j
      · subst k;simp [Placement.replace,Placement.combine,Placement.extra,Tapes.reindex,Tapes.append,setTape]
      · have hn : e (Fin.natAdd n k)≠e (Fin.natAdd n j) := fun h => hk (Fin.natAdd_injective _ _ (e.injective h))
        simp [Placement.replace,Placement.combine,Placement.extra,Tapes.reindex,Tapes.append,setTape,hn]

private theorem headers_setTape (v : Tapes (publicTapes s c) 2)
    (st : ActiveRepairRankHeadersCommands.State) (i : Fin (publicTapes s c))
    (hi : ∀ j,i≠CompactComplexSourceReadyLeafCodec.slot (s:=10+s) j) (f : ℤ → Fin 6) (p : ℤ) :
    headers (setTape v i f p) st=setTape (headers v st) i f p :=
  replace_setTape CompactComplexSourceReadyLeafCodec.placement v _ i
    (by intro j;simpa only [CompactComplexSourceReadyLeafCodec.placement,InjectivePlacement.active_slot] using hi j) f p

private theorem active_setTape (v : Tapes (publicTapes s c) 2) (i : Fin (publicTapes s c))
    (hi : ∀ j,i≠CompactComplexSourceReadyLeafCodec.slot (s:=10+s) j) (f : ℤ → Fin 6) (p : ℤ) :
    Placement.active headerPlacement (base (setTape v i f p))=Placement.active headerPlacement (base v) := by
  rw [←CompactComplexSourceReadyLeafCodec.active,←CompactComplexSourceReadyLeafCodec.active]
  apply congrArg₂ Tapes.mk <;> funext j <;>
    simp only [CompactComplexSourceReadyLeafCodec.placement,InjectivePlacement.active_slot,setTape,
      Function.update_of_ne (hi j).symm]


private theorem headers_targeted (v : Tapes (publicTapes s c) 2)
    (st : ActiveRepairRankHeadersCommands.State) (n : ℕ) :
    headers (targeted v n) st=targeted (headers v st) n :=
  headers_setTape v st _ target_outside _ 1

private theorem targeted_headers (v : Tapes (publicTapes s c) 2) (n : ℕ) :
    Placement.active headerPlacement (base (targeted v n))=Placement.active headerPlacement (base v) :=
  active_setTape v _ target_outside _ 1

private theorem count_header (v : Tapes (publicTapes s c) 2)
    (st : ActiveRepairRankHeadersCommands.State) (V : ℕ) (hst : st 7=some V)
    (h : Placement.active headerPlacement (base v)=ActiveRepairRankHeadersCommands.bank st) :
    v.head (CompactComplexNonleafRoleChildBank.numeric 7)=1 ∧
      v.tape (CompactComplexNonleafRoleChildBank.numeric 7)=RadixZeroFill.encodedBinary (bits V) := by
  have he := (CompactComplexSourceReadyLeafCodec.active v).trans h
  have hh := congrArg (fun w : Tapes 43 2 => w.head (Fin.castAdd 15 (7 : Fin 28))) he
  have ht := congrArg (fun w : Tapes 43 2 => w.tape (Fin.castAdd 15 (7 : Fin 28))) he
  simp only [CompactComplexSourceReadyLeafCodec.placement,InjectivePlacement.active_bank,
    ActiveRepairRankHeadersCommands.bank,CleanSubbank.bank,Tapes.append,Fin.addCases_left] at hh ht
  change v.head (CompactComplexNonleafRoleChildBank.numeric 7)=(if (st 7).isSome then 1 else 0) at hh
  change v.tape (CompactComplexNonleafRoleChildBank.numeric 7)=
    (match st 7 with | none => fun _ => blank | some n => RadixZeroFill.encodedBinary (bits n)) at ht
  rw [hst] at hh ht
  exact ⟨hh,ht⟩

def program := seq (seq (CompactComplexSourceReadyStoppedLeafCount.countProgram (s:=s) (c:=c) expand)
  (installProgram (s:=s) (c:=c)))
  (CompactComplexSourceReadyStoppedLeafCount.countProgram (s:=s) (c:=c) restore)

def cost (sh : Shape) (rows ell p rho left k right src dst n : ℕ) :=
  let st := CompactSpectatorLeafSetup.raw sh rows ell p rho left (arity^k) arity right src dst
  CompactChildHeadersArithmetic.scheduleCost expand st+
    CompactNativeDenominatorTarget.networkCost n (arity^(k+1))+
    CompactChildHeadersArithmetic.scheduleCost restore (expanded st arity (arity^k))+2

/-- Positive-node target generation expands the ACTUAL child count, adds its
whole volume twice, restores the original count and retains every source/frame. -/
theorem runs (sh : Shape) (rows ell p rho left k right src dst n : ℕ)
    (v : Tapes (publicTapes s c) 2)
    (hraw : Placement.active headerPlacement (base v)=ActiveRepairRankHeadersCommands.bank
      (CompactSpectatorLeafSetup.raw sh rows ell p rho left (arity^k) arity right src dst))
    (hn : v.head CompactComplexNonleafRoleChildBank.current=1 ∧
      v.tape CompactComplexNonleafRoleChildBank.current=RadixZeroFill.encodedBinary (bits n))
    (ht : v.head CompactComplexNonleafRoleChildBank.target=0 ∧
      v.tape CompactComplexNonleafRoleChildBank.target=(fun _ => blank)) :
    HoareTime (program (s:=s) (c:=c)) (fun z => z=ready v)
      (fun z => z=ready (targeted v (n+2*arity^(k+1))))
      (cost sh rows ell p rho left k right src dst n) := by
  let st := CompactSpectatorLeafSetup.raw sh rows ell p rho left (arity^k) arity right src dst
  let ex := expanded st arity (arity^k)
  have heq : ex=CompactSpectatorLeafSetup.raw sh rows ell p rho left (arity^(k+1)) arity right src dst := by
    funext i
    fin_cases i <;> simp [ex,st,expanded,CompactSpectatorLeafSetup.raw,ActiveRepairRankHeadersCommands.put,pow_succ]
  have hex := CompactSpectatorLeafCountBudget.expand_runs (a:=2) st arity (arity^k) rfl rfl rfl (pow_pos (by decide) _)
  have h0 := hoare_extend_eq (hoare_extend_eq (numeric_runs _ v st ex _ hraw hex)
    (SharedBank.empty CompactComplexSourceReadyWorkspace.leafTapes 2)) (SharedBank.empty 10 2)
  have hn' := CompactComplexSourceReadyLeafCodec.headers_frame v ex CompactComplexNonleafRoleChildBank.current current_outside
  have ht' := CompactComplexSourceReadyLeafCodec.headers_frame v ex CompactComplexNonleafRoleChildBank.target target_outside
  have hvol : ex 7=some (arity^(k+1)) := by rw [heq];rfl
  have hv := count_header (headers v ex) ex (arity^(k+1)) hvol (headers_active v ex)
  have h1 := install (headers v ex) n (arity^(k+1))
    ⟨hn'.1.trans hn.1,hn'.2.trans hn.2⟩ hv ⟨ht'.1.trans ht.1,ht'.2.trans ht.2⟩
  have hrst := CompactSpectatorLeafCountBudget.restore_runs (a:=2) st arity (arity^k) rfl rfl rfl (by decide : 0<arity)
  have h2 := hoare_extend_eq (hoare_extend_eq
    (numeric_runs _ (targeted (headers v ex) (n+2*arity^(k+1))) ex st _
      ((targeted_headers _ _).trans (headers_active _ _)) hrst)
      (SharedBank.empty CompactComplexSourceReadyWorkspace.leafTapes 2)) (SharedBank.empty 10 2)
  rw [headers_targeted,headers_headers,headers_original v st hraw] at h2
  exact ((h0.seq h1).seq h2).consequence (fun _ hz => hz) (fun _ hz => hz)
    (by dsimp only [cost,st,ex];omega)

def constant := CompactComplexSourceReadyStoppedLeafCountBudget.countConstant+127

/-- Incoming true-live traffic and both real count lifecycles are paid by
native volume using the actual dependency Path, not a supplied cost allowance. -/
theorem cost_native {sh : Shape} {left k levels frames returned : ℕ}
    (path : CompactRecursiveDependencyBudget.Path sh.active left (k+1) levels frames returned)
    (rows ell p : ℕ) (rho : Fin sh.chunk) (right src dst n R baseline usedRows : ℕ)
    (hr : 0<rows) (hK : 0<sh.chunk) (hP : 2*sh.bits≤p)
    (hb : baseline≤p-2*sh.bits) (hu : usedRows≤R)
    (hroom : CompactComplexDenominatorCapacity.room R≤sh.chunk)
    (hlive : n≤CompactComplexDenominatorCapacity.ledger R baseline levels frames returned usedRows) :
    cost sh rows ell p rho.val left k right src dst n≤constant*CompactNativeRoleTransferBudget.volume rows sh ell p := by
  let V := CompactNativeRoleTransferBudget.volume rows sh ell p
  have hn := CompactComplexDenominatorCapacity.target_volume path R baseline (p-2*sh.bits) usedRows n n rows ell
    hb hu hroom hlive (Nat.le_add_right _ _) hr
  have he := CompactComplexSpectatorVolumeHeaders.volume_semantic sh 1 rows ell p false hP
  simp only [CompactComplexSpectatorVolumeHeaders.roleRows,Bool.false_eq_true,ite_false] at he
  rw [←he] at hn
  have hn := hn.trans (CompactComplexControllerExactReturnBudget.stream_le_native sh 1 rows ell p false)
  have hbits := (CompactNativeRoleHeaderBudget.values_le sh rows ell p hr).1
  have hactive : sh.active≤sh.bits := by
    have h := Nat.le_mul_of_pos_right sh.active hK
    unfold Shape.bits
    omega
  have hfit := path.visit.fits
  have hN : arity^(k+1)≤V := (show arity^(k+1)≤sh.bits by omega).trans hbits
  have hcount := CompactComplexSourceReadyStoppedLeafCountBudget.count_linear
    (sh:=sh) (left:=left) (k:=k) rows ell p rho right src dst
  have hc := hcount.trans (Nat.mul_le_mul_left _ hN)
  have hnet := CompactComplexControllerDenominatorTarget.network_cost_le n (arity^(k+1))
  have hV : 0<V := Nat.mul_pos hr (CompactNativeRoleTransferBudget.symbols_pos sh ell p)
  unfold cost constant
  dsimp only [V] at *
  nlinarith

end
end IntegerMultBounds.Machine.CompactComplexSourceReadyNonleafTarget
