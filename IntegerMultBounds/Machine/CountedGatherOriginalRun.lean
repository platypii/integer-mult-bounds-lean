import IntegerMultBounds.Machine.CountedGatherRun
import IntegerMultBounds.Machine.CountedGatherMetadata
import IntegerMultBounds.Machine.PlacementBank
import IntegerMultBounds.Machine.FixedHeaderBankCopy
import IntegerMultBounds.Machine.CountedGatherClockPair

/-! Uniform gather from the six original runtime headers, sharing three
caller payload tapes and starting every generated descriptor and clock blank. -/
namespace IntegerMultBounds.Machine.CountedGatherOriginalRun
noncomputable section
variable {t a : ℕ}
open SharedPlacementAlphabet (setTape)

def allSlot (focus : Fin 9 → Fin t) : Fin (9+6) → Fin (t+6) :=
  fun z => Fin.addCases (fun i => Fin.castAdd 6 (focus i)) (fun i : Fin 6 => Fin.natAdd t i) z
theorem allSlot_injective (focus : Fin 9 → Fin t) (hi : Function.Injective focus) :
    Function.Injective (allSlot focus) := by
  intro i j h
  induction i using Fin.addCases with
  | left i =>
    induction j using Fin.addCases with
    | left j => simp only [allSlot,Fin.addCases_left] at h; exact congrArg (Fin.castAdd 6) (hi (Fin.castAdd_injective _ _ h))
    | right j => have hv := congrArg Fin.val h; simp only [allSlot,Fin.addCases_left,Fin.addCases_right,Fin.val_castAdd,Fin.val_natAdd] at hv; have := (focus i).isLt; omega
  | right i =>
    induction j using Fin.addCases with
    | left j => have hv := congrArg Fin.val h; simp only [allSlot,Fin.addCases_left,Fin.addCases_right,Fin.val_castAdd,Fin.val_natAdd] at hv; have := (focus j).isLt; omega
    | right j => simp only [allSlot,Fin.addCases_right] at h; apply Fin.ext; have hv := congrArg Fin.val h; simp only [Fin.val_natAdd] at hv ⊢; omega

def metaMap (i : Fin 10) : Fin 15 := Fin.natAdd 3 (Fin.castAdd 2 i)
def gatherMap : Fin 11 → Fin 15 := ![0,1,2,13,4,7,5,10,12,14,8]
def metaSlot (focus : Fin 9 → Fin t) := allSlot focus ∘ metaMap
def gatherSlot (focus : Fin 9 → Fin t) := allSlot focus ∘ gatherMap

theorem metaMap_injective : Function.Injective metaMap := by
  intro i j h; apply Fin.ext; have hv := congrArg Fin.val h; simp only [metaMap,Fin.val_natAdd,Fin.val_castAdd] at hv; omega
theorem gatherMap_injective : Function.Injective gatherMap := by
  intro i j h; fin_cases i <;> fin_cases j <;> first | rfl | norm_num [gatherMap] at h

theorem room (focus : Fin 9 → Fin t) (hi : Function.Injective focus) : 9 ≤ t := by
  have hh := Fintype.card_le_of_injective focus hi
  simpa only [Fintype.card_fin] using hh

theorem metaSlot_injective (focus : Fin 9 → Fin t) (hi : Function.Injective focus) :
    Function.Injective (metaSlot focus) := (allSlot_injective focus hi).comp metaMap_injective
theorem gatherSlot_injective (focus : Fin 9 → Fin t) (hi : Function.Injective focus) :
    Function.Injective (gatherSlot focus) := (allSlot_injective focus hi).comp gatherMap_injective

def metaPlacement (focus : Fin 9 → Fin t) (hi : Function.Injective focus) : Fin (10+(t-4)) ≃ Fin (t+6) :=
  InjectivePlacement.placement (metaSlot focus) (metaSlot_injective focus hi)
    (by have := room focus hi; omega)
def gatherPlacement (focus : Fin 9 → Fin t) (hi : Function.Injective focus) : Fin (11+(t-5)) ≃ Fin (t+6) :=
  InjectivePlacement.placement (gatherSlot focus) (gatherSlot_injective focus hi)
    (by have := room focus hi; omega)

def work (S : Gather.Shape) (kind : ℕ) : Tapes 6 a :=
  ⟨fun i => if i.val < 4 then (if kind = 0 then 0 else 1) else (if kind = 2 then 1 else 0),
   fun i => if h : i.val < 4 then (if kind = 0 then fun _ => blank
     else RadixZeroFill.encodedBinary (CountedGatherMetadata.words S ⟨i.val,h⟩))
     else if kind = 2 then CountedLoopReuseAlphabet.empty else fun _ => blank⟩
def bank (caller : Tapes t a) (S : Gather.Shape) (kind : ℕ) := caller.append (work S kind)
def input (caller : Tapes t a) := caller.append (FixedHeaderBankCopy.empty 6)

theorem bank_zero (caller : Tapes t a) (S : Gather.Shape) : bank caller S 0 = input caller := by
  change caller.append (work S 0) = caller.append (FixedHeaderBankCopy.empty 6)
  apply congrArg (fun w : Tapes 6 a => caller.append w)
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

def clockSlot (t : ℕ) (i : Fin 2) : Fin (t+6) := Fin.natAdd t (Fin.natAdd 4 i)
theorem clockSlot_injective (t : ℕ) : Function.Injective (clockSlot t) := by
  intro i j hh; apply Fin.ext; have hv := congrArg Fin.val hh
  simp only [clockSlot,Fin.val_natAdd] at hv
  omega
def clockPlacement (t : ℕ) : Fin (2+(t+4)) ≃ Fin (t+6) :=
  InjectivePlacement.placement (clockSlot t) (clockSlot_injective t) (by omega)
def clockInit (a t : ℕ) : Program (t+6) 2 a :=
  Placement.placed (CountedGatherClockPair.init a) (clockPlacement t)
def clockClean (a t : ℕ) : Program (t+6) 3 a :=
  Placement.placed (CountedGatherClockPair.clear a) (clockPlacement t)

def program (op : Bool → Bool → Bool) (focus : Fin 9 → Fin t) (hi : Function.Injective focus) :=
  seq (seq (seq (seq
    (Placement.placed (CountedGatherMetadata.program (a := a)) (metaPlacement focus hi))
    (clockInit a t))
    (Placement.placed (CountedGatherRun.program op a) (gatherPlacement focus hi)))
    (clockClean a t))
    (Placement.placed (CountedGatherMetadata.cleanup (a := a)) (metaPlacement focus hi))

def result (caller : Tapes t a) (focus : Fin 9 → Fin t)
    (target : ℤ → Fin (a+4)) (px pz pt : ℤ) :=
  setTape (setTape (setTape caller (focus 0) (caller.tape (focus 0)) px)
    (focus 1) (caller.tape (focus 1)) pz) (focus 2) target pt

private theorem placed_hoare {s u q c : ℕ} {M : Program s q a}
    (slot : Fin s → Fin (t+6)) (hi : Function.Injective slot) (hsize : s+u=t+6)
    (v w : Tapes (t+6) a) (X Y : Tapes s a)
    (hr : HoareTime M (fun z => z = X) (fun z => z = Y) c)
    (ha : Placement.active (InjectivePlacement.placement slot hi hsize) v = X)
    (hb : Placement.active (InjectivePlacement.placement slot hi hsize) w = Y)
    (hf : ∀ j, (∀ i, j ≠ slot i) → v.head j = w.head j ∧ v.tape j = w.tape j) :
    HoareTime (Placement.placed M (InjectivePlacement.placement slot hi hsize))
      (fun z => z = v) (fun z => z = w) c := by
  apply InjectivePlacement.hoare_exact hr slot hi hsize v w ha
  rw [← hb,Placement.replace]
  have hn (j : Fin u) : ∀ i, InjectivePlacement.placement slot hi hsize (Fin.natAdd s j) ≠ slot i := by
    intro i hh
    rw [← InjectivePlacement.active_slot slot hi hsize i] at hh
    have hv := congrArg Fin.val ((InjectivePlacement.placement slot hi hsize).injective hh)
    simp only [Fin.val_natAdd,Fin.val_castAdd] at hv
    have := i.isLt
    omega
  have he : Placement.extra (InjectivePlacement.placement slot hi hsize) v =
      Placement.extra (InjectivePlacement.placement slot hi hsize) w := by
    apply congrArg₂ Tapes.mk
    · funext j; exact (hf _ (hn j)).1
    · funext j; exact (hf _ (hn j)).2
  rw [he]
  exact Placement.view _ _

theorem metaSlot_original (focus : Fin 9 → Fin t) (i : Fin 6) :
    metaSlot focus (Fin.castAdd 4 i) = Fin.castAdd 6 (focus (Fin.natAdd 3 i)) := by
  fin_cases i <;> rfl

theorem metaSlot_private (focus : Fin 9 → Fin t) (i : Fin 4) :
    metaSlot focus (Fin.natAdd 6 i) = Fin.natAdd t (Fin.castAdd 2 i) := by
  fin_cases i <;> rfl

private theorem meta_active (caller : Tapes t a) (focus : Fin 9 → Fin t)
    (hi : Function.Injective focus) (S : Gather.Shape) (hs : Fin 6 → List Bool)
    (ht : ∀ i : Fin 6, caller.tape (focus (Fin.natAdd 3 i)) = RadixZeroFill.encodedBinary (hs i))
    (hh : ∀ i : Fin 6, caller.head (focus (Fin.natAdd 3 i)) = 1) (kind : Fin 2) :
    Placement.active (metaPlacement focus hi) (bank caller S kind.val) =
      if kind.val = 0 then CountedGatherMetadata.input hs else CountedGatherMetadata.output S hs := by
  unfold metaPlacement
  rw [InjectivePlacement.active_bank]
  apply congrArg₂ Tapes.mk
  · funext i
    induction i using Fin.addCases (m := 6) (n := 4) with
    | left i =>
      rw [metaSlot_original]
      simp only [bank,Tapes.append,Fin.addCases_left,hh]
      fin_cases kind <;> fin_cases i <;> rfl
    | right i =>
      rw [metaSlot_private]
      simp only [bank,Tapes.append,Fin.addCases_right]
      fin_cases kind <;> fin_cases i <;> rfl
  · funext i
    induction i using Fin.addCases (m := 6) (n := 4) with
    | left i =>
      rw [metaSlot_original]
      simp only [bank,Tapes.append,Fin.addCases_left,ht]
      fin_cases kind <;> fin_cases i <;> rfl
    | right i =>
      rw [metaSlot_private]
      simp only [bank,Tapes.append,Fin.addCases_right]
      fin_cases kind <;> fin_cases i <;> rfl

private theorem meta_frame (caller : Tapes t a) (focus : Fin 9 → Fin t) (S : Gather.Shape)
    (j : Fin (t+6)) (hj : ∀ i, j ≠ metaSlot focus i) :
    (bank caller S 0).head j = (bank caller S 1).head j ∧
    (bank caller S 0).tape j = (bank caller S 1).tape j := by
  induction j using Fin.addCases with
  | left j => simp only [bank,Tapes.append,Fin.addCases_left]; trivial
  | right j =>
    simp only [bank,Tapes.append,Fin.addCases_right]
    fin_cases j
    all_goals first | exact ⟨rfl,rfl⟩ | exact (hj 6 rfl).elim | exact (hj 7 rfl).elim |
      exact (hj 8 rfl).elim | exact (hj 9 rfl).elim

private theorem metadata_constructs (caller : Tapes t a) (focus : Fin 9 → Fin t)
    (hi : Function.Injective focus) (S : Gather.Shape) (n : ℕ) (hs : Fin 6 → List Bool)
    (hv : ∀ i, Counter.value (hs i) = CountedGatherMetadata.originalValues S n i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i))
    (ht : ∀ i : Fin 6, caller.tape (focus (Fin.natAdd 3 i)) = RadixZeroFill.encodedBinary (hs i))
    (hh : ∀ i : Fin 6, caller.head (focus (Fin.natAdd 3 i)) = 1) :
    HoareTime (Placement.placed (CountedGatherMetadata.program (a := a)) (metaPlacement focus hi))
      (fun z => z = bank caller S 0) (fun z => z = bank caller S 1) (CountedGatherMetadata.constructCost S) := by
  exact placed_hoare _ _ _ _ _ _ _ (CountedGatherMetadata.constructs S n hs hv hc)
    (meta_active caller focus hi S hs ht hh 0) (meta_active caller focus hi S hs ht hh 1)
    (meta_frame caller focus S)

private theorem metadata_cleans (caller : Tapes t a) (focus : Fin 9 → Fin t)
    (hi : Function.Injective focus) (S : Gather.Shape) (hs : Fin 6 → List Bool)
    (ht : ∀ i : Fin 6, caller.tape (focus (Fin.natAdd 3 i)) = RadixZeroFill.encodedBinary (hs i))
    (hh : ∀ i : Fin 6, caller.head (focus (Fin.natAdd 3 i)) = 1) :
    HoareTime (Placement.placed (CountedGatherMetadata.cleanup (a := a)) (metaPlacement focus hi))
      (fun z => z = bank caller S 1) (fun z => z = bank caller S 0) (CountedGatherMetadata.cleanupCost S) := by
  exact placed_hoare _ _ _ _ _ _ _ (CountedGatherMetadata.cleans S hs)
    (meta_active caller focus hi S hs ht hh 1) (meta_active caller focus hi S hs ht hh 0)
    (fun j hj => ⟨(meta_frame caller focus S j hj).1.symm,(meta_frame caller focus S j hj).2.symm⟩)

theorem gatherSlot_eq (focus : Fin 9 → Fin t) : gatherSlot focus =
    ![Fin.castAdd 6 (focus 0),Fin.castAdd 6 (focus 1),Fin.castAdd 6 (focus 2),
      Fin.natAdd t 4,Fin.castAdd 6 (focus 4),Fin.castAdd 6 (focus 7),Fin.castAdd 6 (focus 5),
      Fin.natAdd t 1,Fin.natAdd t 3,Fin.natAdd t 5,Fin.castAdd 6 (focus 8)] := by
  funext i; fin_cases i <;> rfl

private theorem encoded_binary (bs : List Bool) : RadixZeroFill.encodedBinary (q := a) bs =
    CountedLoopReuseAlphabet.binary bs := by
  change (fun j => (CountedLoopReuseAlphabet.encoding a).encode (CountedCopyReuse.binary bs j)) = _
  exact CountedLoopReuseAlphabet.encoding_binary bs

private theorem gather_active (caller : Tapes t a) (focus : Fin 9 → Fin t)
    (hi : Function.Injective focus) (S : Gather.Shape) (hs : Fin 6 → List Bool)
    (ht : ∀ i : Fin 6, caller.tape (focus (Fin.natAdd 3 i)) = RadixZeroFill.encodedBinary (hs i))
    (hh : ∀ i : Fin 6, caller.head (focus (Fin.natAdd 3 i)) = 1) :
    Placement.active (gatherPlacement focus hi) (bank caller S 2) =
      CountedGatherRun.bank (CountedGatherDigit.bank
        (Gather.bank (caller.tape (focus 0)) (caller.tape (focus 1)) (caller.tape (focus 2))
          (caller.head (focus 0)) (caller.head (focus 1)) (caller.head (focus 2)))
        (CountedGatherMetadata.digitWords S hs)) (hs 5) := by
  unfold gatherPlacement
  rw [InjectivePlacement.active_bank,gatherSlot_eq]
  apply congrArg₂ Tapes.mk
  · funext i; fin_cases i
    all_goals simp [Matrix.cons_val,bank,Tapes.append,Fin.addCases_left,Fin.addCases_right,
      CountedGatherDigit.bank,CountedGatherDigit.descriptors,
      CountedLoopReuseAlphabet.controls,Gather.bank,work]
    all_goals first | rfl | exact hh 1 | exact hh 4 | exact hh 2 | exact hh 5
  · funext i; fin_cases i
    all_goals simp [Matrix.cons_val,bank,Tapes.append,Fin.addCases_left,Fin.addCases_right,
      CountedGatherDigit.bank,CountedGatherDigit.descriptors,
      CountedLoopReuseAlphabet.controls,Gather.bank,work]
    all_goals first | rfl | exact (ht 1).trans (encoded_binary _) |
      exact (ht 4).trans (encoded_binary _) | exact (ht 2).trans (encoded_binary _) |
      exact encoded_binary _ | exact (ht 5).trans (encoded_binary _)

private theorem result_frame (caller : Tapes t a) (focus : Fin 9 → Fin t)
    (target : ℤ → Fin (a+4)) (px pz pt : ℤ) (j : Fin t)
    (h0 : j ≠ focus 0) (h1 : j ≠ focus 1) (h2 : j ≠ focus 2) :
    (result caller focus target px pz pt).head j = caller.head j ∧
    (result caller focus target px pz pt).tape j = caller.tape j := by
  simp only [result,setTape,Function.update_of_ne h0,Function.update_of_ne h1,Function.update_of_ne h2]
  trivial

private theorem result_headers (caller : Tapes t a) (focus : Fin 9 → Fin t) (hi : Function.Injective focus)
    (target : ℤ → Fin (a+4)) (px pz pt : ℤ) (i : Fin 6) :
    (result caller focus target px pz pt).head (focus (Fin.natAdd 3 i)) = caller.head (focus (Fin.natAdd 3 i)) ∧
    (result caller focus target px pz pt).tape (focus (Fin.natAdd 3 i)) = caller.tape (focus (Fin.natAdd 3 i)) := by
  apply result_frame
  all_goals intro hh; have he := hi hh; have hv := congrArg Fin.val he
  all_goals norm_num [Fin.val_natAdd] at hv
  all_goals omega

private theorem result_payload (caller : Tapes t a) (focus : Fin 9 → Fin t) (hi : Function.Injective focus)
    (target : ℤ → Fin (a+4)) (px pz pt : ℤ) :
    Gather.bank ((result caller focus target px pz pt).tape (focus 0))
      ((result caller focus target px pz pt).tape (focus 1))
      ((result caller focus target px pz pt).tape (focus 2))
      ((result caller focus target px pz pt).head (focus 0))
      ((result caller focus target px pz pt).head (focus 1))
      ((result caller focus target px pz pt).head (focus 2)) =
    Gather.bank (caller.tape (focus 0)) (caller.tape (focus 1)) target px pz pt := by
  have h01 : focus 0 ≠ focus 1 := fun he => (by decide : (0 : Fin 9) ≠ 1) (hi he)
  have h02 : focus 0 ≠ focus 2 := fun he => (by decide : (0 : Fin 9) ≠ 2) (hi he)
  have h12 : focus 1 ≠ focus 2 := fun he => (by decide : (1 : Fin 9) ≠ 2) (hi he)
  simp only [result,setTape,Function.update_self,Function.update_of_ne h01,
    Function.update_of_ne h02,Function.update_of_ne h12]

private theorem gather_frame (caller : Tapes t a) (focus : Fin 9 → Fin t) (S : Gather.Shape)
    (target : ℤ → Fin (a+4)) (px pz pt : ℤ) (j : Fin (t+6))
    (hj : ∀ i, j ≠ gatherSlot focus i) :
    (bank caller S 2).head j = (bank (result caller focus target px pz pt) S 2).head j ∧
    (bank caller S 2).tape j = (bank (result caller focus target px pz pt) S 2).tape j := by
  induction j using Fin.addCases with
  | left j =>
    simp only [bank,Tapes.append,Fin.addCases_left]
    have hn (i : Fin 3) : j ≠ focus (Fin.castAdd 6 i) := by
      intro he
      have hne := hj (Fin.castAdd 8 i)
      apply hne
      rw [gatherSlot_eq]
      fin_cases i <;> simpa using congrArg (Fin.castAdd 6) he
    have hh := result_frame caller focus target px pz pt j (hn 0) (hn 1) (hn 2)
    exact ⟨hh.1.symm,hh.2.symm⟩
  | right j => simp only [bank,Tapes.append,Fin.addCases_right]; trivial

private theorem gather_runs (caller : Tapes t a) (focus : Fin 9 → Fin t) (hi : Function.Injective focus)
    (op : Bool → Bool → Bool) (S : Gather.Shape) (xs zs : List Bool)
    (f g h : ℤ → Fin (a+4)) (px pz pt : ℤ) (hs : Fin 6 → List Bool)
    (ht : ∀ i : Fin 6, caller.tape (focus (Fin.natAdd 3 i)) = RadixZeroFill.encodedBinary (hs i))
    (hh : ∀ i : Fin 6, caller.head (focus (Fin.natAdd 3 i)) = 1)
    (h0 : caller.tape (focus 0) = putWord f px (xs.map bitSymbol))
    (h1 : caller.tape (focus 1) = putWord g pz (zs.map bitSymbol))
    (h2 : caller.tape (focus 2) = h)
    (p0 : caller.head (focus 0) = px) (p1 : caller.head (focus 1) = pz) (p2 : caller.head (focus 2) = pt)
    (hxs : zs.length*S.sx ≤ xs.length)
    (hv : ∀ i, Counter.value (hs i) = CountedGatherMetadata.originalValues S zs.length i) :
    HoareTime (Placement.placed (CountedGatherRun.program op a) (gatherPlacement focus hi))
      (fun z => z = bank caller S 2)
      (fun z => z = bank (result caller focus
        (putWord h pt ((Gather.gather op S xs zs zs.length).map bitSymbol))
        (px+zs.length*S.sx) (pz+zs.length) (pt+zs.length*S.st)) S 2)
      (CountedGatherRun.cost S (CountedGatherMetadata.digitWords S hs) zs.length (hs 5)) := by
  let target := putWord h pt ((Gather.gather op S xs zs zs.length).map (bitSymbol (a := a)))
  let after := result caller focus target (px+zs.length*S.sx) (pz+zs.length) (pt+zs.length*S.st)
  have hv' : ∀ i, Counter.value (CountedGatherMetadata.digitWords S hs i) = CountedGatherDigit.counts S i :=
    CountedGatherMetadata.digit_values S zs.length hs hv
  have hn : Counter.value (hs 5) = zs.length := hv 5
  have hr := CountedGatherRun.gather_hoare op S xs zs f g h px pz pt
    (CountedGatherMetadata.digitWords S hs) (hs 5) hxs hv' hn
  have ha := gather_active caller focus hi S hs ht hh
  rw [h0,h1,h2,p0,p1,p2] at ha
  have ht' : ∀ i : Fin 6, after.tape (focus (Fin.natAdd 3 i)) = RadixZeroFill.encodedBinary (hs i) := by
    intro i; exact (result_headers caller focus hi target _ _ _ i).2.trans (ht i)
  have hh' : ∀ i : Fin 6, after.head (focus (Fin.natAdd 3 i)) = 1 := by
    intro i; exact (result_headers caller focus hi target _ _ _ i).1.trans (hh i)
  have hb := gather_active after focus hi S hs ht' hh'
  rw [result_payload caller focus hi target, h0,h1] at hb
  simp only [CountedGatherRun.state,Gather.gather,List.map_nil,putWord,Nat.cast_zero,zero_mul,add_zero] at hr
  apply placed_hoare _ _ _ _ _ _ _ hr
  · exact ha
  · exact hb
  · exact gather_frame caller focus S target _ _ _

private theorem clock_active (caller : Tapes t a) (S : Gather.Shape) (k : Fin 2) :
    Placement.active (clockPlacement t) (bank caller S (k.val+1)) =
      if k.val = 0 then CountedGatherClockPair.empty else CountedGatherClockPair.marked := by
  unfold clockPlacement
  rw [InjectivePlacement.active_bank]
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases k <;> fin_cases i
  all_goals simp [clockSlot,bank,Tapes.append,work,CountedGatherClockPair.empty,
    CountedGatherClockPair.marked,FixedHeaderBankCopy.empty,CountedLoopReuseAlphabet.controls]
  all_goals rfl

private theorem clock_frame (caller : Tapes t a) (S : Gather.Shape) (j : Fin (t+6))
    (hj : ∀ i, j ≠ clockSlot t i) :
    (bank caller S 1).head j = (bank caller S 2).head j ∧
    (bank caller S 1).tape j = (bank caller S 2).tape j := by
  induction j using Fin.addCases with
  | left j => simp only [bank,Tapes.append,Fin.addCases_left]; trivial
  | right j =>
    simp only [bank,Tapes.append,Fin.addCases_right]
    fin_cases j
    all_goals first | exact ⟨rfl,rfl⟩ | exact (hj 0 rfl).elim | exact (hj 1 rfl).elim

private theorem clock_constructs (caller : Tapes t a) (S : Gather.Shape) :
    HoareTime (clockInit a t) (fun z => z = bank caller S 1) (fun z => z = bank caller S 2) 1 := by
  exact placed_hoare _ _ _ _ _ _ _ CountedGatherClockPair.init_hoare
    (clock_active caller S 0) (clock_active caller S 1) (clock_frame caller S)
private theorem clock_cleans (caller : Tapes t a) (S : Gather.Shape) :
    HoareTime (clockClean a t) (fun z => z = bank caller S 2) (fun z => z = bank caller S 1) 2 := by
  exact placed_hoare _ _ _ _ _ _ _ CountedGatherClockPair.clear_hoare
    (clock_active caller S 1) (clock_active caller S 0)
    (fun j hj => ⟨(clock_frame caller S j hj).1.symm,(clock_frame caller S j hj).2.symm⟩)

def cost (S : Gather.Shape) (n : ℕ) (hs : Fin 6 → List Bool) :=
  CountedGatherMetadata.constructCost S +
    CountedGatherRun.cost S (CountedGatherMetadata.digitWords S hs) n (hs 5) +
    CountedGatherMetadata.cleanupCost S + 7

/-- Complete actual original-header execution. Four derived descriptors and
both independent clocks are physically constructed and erased, while every
original header and every complementary caller tape is retained. -/
theorem runs (caller : Tapes t a) (focus : Fin 9 → Fin t) (hi : Function.Injective focus)
    (op : Bool → Bool → Bool) (S : Gather.Shape) (xs zs : List Bool)
    (f g h : ℤ → Fin (a+4)) (px pz pt : ℤ) (hs : Fin 6 → List Bool)
    (hv : ∀ i, Counter.value (hs i) = CountedGatherMetadata.originalValues S zs.length i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i))
    (ht : ∀ i : Fin 6, caller.tape (focus (Fin.natAdd 3 i)) = RadixZeroFill.encodedBinary (hs i))
    (hh : ∀ i : Fin 6, caller.head (focus (Fin.natAdd 3 i)) = 1)
    (h0 : caller.tape (focus 0) = putWord f px (xs.map bitSymbol))
    (h1 : caller.tape (focus 1) = putWord g pz (zs.map bitSymbol))
    (h2 : caller.tape (focus 2) = h)
    (p0 : caller.head (focus 0) = px) (p1 : caller.head (focus 1) = pz) (p2 : caller.head (focus 2) = pt)
    (hxs : zs.length*S.sx ≤ xs.length) :
    HoareTime (program op focus hi) (fun z => z = input caller)
      (fun z => z = input (result caller focus
        (putWord h pt ((Gather.gather op S xs zs zs.length).map bitSymbol))
        (px+zs.length*S.sx) (pz+zs.length) (pt+zs.length*S.st))) (cost S zs.length hs) := by
  let target := putWord h pt ((Gather.gather op S xs zs zs.length).map (bitSymbol (a := a)))
  let after := result caller focus target (px+zs.length*S.sx) (pz+zs.length) (pt+zs.length*S.st)
  have ht' : ∀ i : Fin 6, after.tape (focus (Fin.natAdd 3 i)) = RadixZeroFill.encodedBinary (hs i) := by
    intro i; exact (result_headers caller focus hi target _ _ _ i).2.trans (ht i)
  have hh' : ∀ i : Fin 6, after.head (focus (Fin.natAdd 3 i)) = 1 := by
    intro i; exact (result_headers caller focus hi target _ _ _ i).1.trans (hh i)
  have hm := metadata_constructs caller focus hi S zs.length hs hv hc ht hh
  have hi' := clock_constructs caller S
  have hr := gather_runs caller focus hi op S xs zs f g h px pz pt hs ht hh h0 h1 h2 p0 p1 p2 hxs hv
  have he := clock_cleans after S
  have hc' := metadata_cleans after focus hi S hs ht' hh'
  have hall := (((hm.seq hi').seq hr).seq he).seq hc'
  rw [bank_zero,bank_zero] at hall
  apply hall.consequence (fun _ h => h) (fun _ h => h) _
  unfold cost
  omega

/-- A uniform full-stride bound includes all original-header preparation and
reverse cleanup, even when the digit count or either stride is zero. -/
theorem cost_linear (S : Gather.Shape) (n : ℕ) (hs : Fin 6 → List Bool)
    (hv : ∀ i, Counter.value (hs i) = CountedGatherMetadata.originalValues S n i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    cost S n hs ≤ 169*((n+1)*(S.sx+S.st+1)) := by
  have hg := CountedGatherRun.cost_linear S (CountedGatherMetadata.digitWords S hs) n (hs 5)
    (CountedGatherMetadata.digit_values S n hs hv) (CountedGatherMetadata.digit_canonical S hs hc)
    (hv 5) (hc 5)
  have he := CountedGatherMetadata.cleanup_cost_bound S
  unfold cost CountedGatherMetadata.constructCost
  nlinarith

end
end IntegerMultBounds.Machine.CountedGatherOriginalRun
