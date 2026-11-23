module

public import IntegerMultBounds.MathlibTM2.M6.BitRemainderPiece
public import IntegerMultBounds.MathlibTM2.M6.BitIntervalRows
public import IntegerMultBounds.MathlibTM2.M6.BitHelperPacking
public import IntegerMultBounds.MathlibTM2.M6.OrthogonalInvocation

/-! The packed slot changes between successive uses of a PR589 helper owner. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks
open Shared50ModularControl (prime)
open IntegerMultBounds.Networks.Certificates.PR589.Nine
open BitHosting

local instance (w : ℕ) : NeZero (prime^(w+1)) := ⟨(pow_pos Shared50ModularControl.prime_prime.pos _).ne'⟩

def helperPosition (entry : Fin 9 × Fin 439) : Fin 56 :=
  ⟨slotPos (IntegerMultBounds.MathlibTM2.M6.BitNode.slotOf entry.1 entry.2),Nat.lt_succ_of_le (slotPos_le _ entry.1.isLt _ entry.2.isLt)⟩

/-- During an idle, one fixed ordering of the five run classes locates
every hosted eight-axis interval on this owner, across all its stages. -/
theorem helperPosition_of_runClass (n : Fin 9) (r : Fin 32) (d : Fin 5) (h : Fin 439) :
    let slot := IntegerMultBounds.MathlibTM2.M6.BitNode.slotOf n.val h.val
    let cls := (hostRole n r d h).cls.val
    (helperPosition (n,h)).val = 7*idleSource slot.idle + 8*((cls+5-d.val)%5) := by
  intro slot cls
  have fits := slot_fits slot (slotOf_spec n n.isLt h h.isLt).1
  change 7*idleSource slot.idle + slot.offset =
    7*idleSource slot.idle + 8*((((d.val+slot.offset/8)%5)+5-d.val)%5)
  congr 1
  have hd := d.isLt
  omega

/-- Narrowing a scheduled eight-axis helper to a MOVE or COPY subinterval
selects that same interval directly on the parent's physical words. -/
theorem helperSubinterval_descriptor (v : RecursiveInterchangeLayout.Descriptor)
    (n : Fin 9) (r : Fin 32) (d : Fin 5) (h : Fin 439) (w lo hi : ℕ)
    (fits : hi ≤ 8) :
    let slot := IntegerMultBounds.MathlibTM2.M6.BitNode.slotOf n.val h.val
    let start := 7*idleSource slot.idle + 8*(((hostRole n r d h).cls.val+5-d.val)%5)
    let p := (helperPosition (n,h)).val
    inheritedInterval (inheritedInterval v (p*w) (8*w) ((64-(p+8))*w))
      (lo*w) ((hi-lo)*w) ((8-hi)*w) =
      inheritedInterval v ((start+lo)*w) ((hi-lo)*w) ((64-(start+hi))*w) := by
  intro slot start p
  have pos : p = start := helperPosition_of_runClass n r d h
  have bound : p < 56 := (helperPosition (n,h)).isLt
  rw [inheritedInterval_nested,← pos,← Nat.add_mul,← Nat.add_mul]
  congr 2
  omega

/-- The physical child selected inside a helper retains the full role volume,
including the parent's existing middle and trailing spectators. -/
theorem helperSubinterval_volume (v : RecursiveInterchangeLayout.Descriptor)
    (n : Fin 9) (h : Fin 439) (w lo hi : ℕ) (width : v.width = 64*w)
    (ordered : lo ≤ hi) (fits : hi ≤ 8) :
    let p := (helperPosition (n,h)).val
    let lane := inheritedInterval v (p*w) (8*w) ((64-(p+8))*w)
    RecursiveInterchangeLayout.volume prime
      (inheritedInterval lane (lo*w) ((hi-lo)*w) ((8-hi)*w)) =
      RecursiveInterchangeLayout.volume prime v := by
  intro p lane
  have bound : p < 56 := (helperPosition (n,h)).isLt
  have inner : lane.width = lo*w+(hi-lo)*w+(8-hi)*w := by
    change 8*w = _
    rw [← Nat.add_mul,← Nat.add_mul]
    congr 1
    omega
  rw [inheritedInterval_volume _ _ _ _ inner]
  apply inheritedInterval_volume
  rw [width,← Nat.add_mul,← Nat.add_mul]
  congr 1
  omega

open RecursiveInterchangeLayout Cover.Fallback in
/-- Selecting the physical slot on a row-split owner preserves all three
quantities used to recurse at the scheduled occurrence. -/
theorem helperSubinterval_shape (v : Descriptor) (i : Fin nodeChildren5.length)
    (n : Fin 9) (r : Fin 32) (d : Fin 5) (h : Fin 439) (w lo hi : ℕ)
    (width : v.width = 64*w) (ordered : lo ≤ hi) (fits : hi ≤ 8)
    (rank : nodeChildren5[i.val] = hi-lo) :
    let slot := IntegerMultBounds.MathlibTM2.M6.BitNode.slotOf n.val h.val
    let start := 7*idleSource slot.idle + 8*(((hostRole n r d h).cls.val+5-d.val)%5)
    ScheduledChildShape prime v i (inheritedInterval (role v 142080)
      ((start+lo)*w) ((hi-lo)*w) ((64-(start+hi))*w)) := by
  intro slot start
  have actual := helperSubinterval_volume (role v 142080) n h w lo hi width ordered fits
  dsimp only at actual
  rw [helperSubinterval_descriptor _ n r d h w lo hi fits] at actual
  have scheduled : scheduledChild prime v i =
      rankDescriptor prime ((hi-lo)*w) ((64-(hi-lo))*w) (role v 142080) := by
    simp only [scheduledChild,width,Nat.mul_div_cancel_left _ (by decide : 0 < 64),rank]
  constructor
  · rw [scheduled]
    rfl
  · rfl
  · rw [scheduled,rankDescriptor_volume]
    · exact actual
    · change v.width = _
      rw [width,← Nat.add_mul]
      congr 1
      omega

open RecursiveInterchangeLayout Certificates.PR589 in
/-- A paid MOVE on a helper uses the directory entry for that occurrence,
even when several edges have the same frame pair. -/
theorem helperMove_shape (v : Descriptor) (n : Fin 9) (run : Fin 32 × Fin 5)
    (h : Fin 439) (w : ℕ) (width : v.width = 64*w) :
    let edges := Geometry.Moves.phaseEdges.filter fun p => Geometry.moveRank p.1 p.2 != 0
    ∀ j : Fin edges.length, let p := edges[j.val]
      let a := Geometry.Dimensions.value p.1
      let b := Geometry.Dimensions.value p.2
      let lo := min a b
      let hi := max a b
      let start := (helperPosition (n,h)).val
      ScheduledChildShape prime v (phaseChildPositions.choose (n,run,j))
        (inheritedInterval (role v 142080) ((start+lo)*w) ((hi-lo)*w) ((64-(start+hi))*w)) := by
  intro edges j p a b lo hi start
  have mem := List.mem_filter.mp (List.getElem_mem (l := edges) (n := j.val) j.isLt)
  have checked := Geometry.Moves.phase_checked p mem.1
  have paid : 0 < Geometry.moveRank p.1 p.2 := Nat.pos_of_ne_zero (bne_iff_ne.mp mem.2)
  obtain ⟨ordered,fits⟩ := phaseInterval_bounds checked paid
  have rank := (phaseChildPositions.choose_spec n run j).1
  have diff := Geometry.Moves.rank p checked
  change Geometry.moveRank p.1 p.2 = (b-a)+(a-b) at diff
  change nodeChildren5[_] = Geometry.moveRank p.1 p.2 at rank
  rw [show start = _ from helperPosition_of_runClass n run.1 run.2 h]
  apply helperSubinterval_shape _ _ _ _ _ _ _ _ _ width ordered.le fits
  exact rank.trans (diff.trans (by omega))

/-- In inherited order the live H digits begin at the slot offset; the
corresponding D digits begin 64 fields later. -/
def helperBasisAxis (p : Fin 56) (i : Fin 16) : Fin 128 :=
  ⟨p.val+i.val+(if i.val < 8 then 0 else 56),by split <;> omega⟩

theorem helperBasisAxis_strict (p : Fin 56) : StrictMono (helperBasisAxis p) := by
  intro i j lt
  change i.val < j.val at lt
  change p.val+i.val+(if i.val < 8 then 0 else 56) < p.val+j.val+(if j.val < 8 then 0 else 56)
  split_ifs <;> omega

/-- Compile each elementary basis operation at its physical field position,
retaining the protected coefficient and the earlier-control condition. -/
def helperBasisOp (p : Fin 56) : FlatCoordinateSchedule.Op 16 → FlatCoordinateSchedule.Op 128
  | .scale t a legal => .scale (helperBasisAxis p t) a legal
  | .shift t k earlier a legal =>
    .shift (helperBasisAxis p t) (helperBasisAxis p k) (helperBasisAxis_strict p earlier) a legal

theorem helperBasis_read (p : Fin 56) (ops : List (FlatCoordinateSchedule.Op 16)) (b : ℕ)
    (x : Fin 128 → ZMod (ActualAffineScaling.modulus b)) :
    OrderedAffine.run (ops.map fun op => (helperBasisOp p op).action b) x ∘ helperBasisAxis p =
      OrderedAffine.run (ops.map fun op => op.action b) (x ∘ helperBasisAxis p) := by
  induction ops generalizing x with
  | nil => rfl
  | cons op ops ih =>
    simp only [List.map_cons,OrderedAffine.run,List.foldl_cons] at ih ⊢
    rw [ih]
    congr 1
    cases op <;> exact Function.update_comp_eq_of_injective x (helperBasisAxis_strict p).injective _ _

theorem helperBasis_spectator (p : Fin 56) (ops : List (FlatCoordinateSchedule.Op 16)) (b : ℕ)
    (x : Fin 128 → ZMod (ActualAffineScaling.modulus b)) (j : Fin 128)
    (outside : ∀ i, j ≠ helperBasisAxis p i) :
    OrderedAffine.run (ops.map fun op => (helperBasisOp p op).action b) x j = x j := by
  induction ops generalizing x with
  | nil => rfl
  | cons op ops ih =>
    simp only [List.map_cons,OrderedAffine.run,List.foldl_cons] at ih ⊢
    rw [ih]
    cases op <;> exact Function.update_of_ne (outside _) _ _

local instance (b : ℕ) : NeZero (ActualAffineScaling.modulus b) := ⟨(ActualAffineScaling.modulus_pos b).ne'⟩

open M8.Machine.Segments ActualAffineScaling AffineFieldCoordinates in
/-- A certified basis segment runs on the owner's clean bank. Its active
coordinates follow the original field program and every other digit is fixed. -/
theorem helperSegment_runs (p : Fin 56) (ops : List (AffineFieldProgram.Op (Fin 8) ℚ))
    (good : Good ops) (b W : ℕ) (live : 0 < W) (input : FlatCoordinateStages.Array 128 b W) :
    let physical := (description ops good).map (helperBasisOp p)
    let bank := fun word => SharedBankStageInput.raw (FlatCoordinateShiftSharedBank.common word)
      (FlatCoordinateCleanSchedule.tapeCount physical)
    let spec := ops.map (AffineFieldProgram.mapOp (IntegerMultBounds.Swap.Modular.ratMod (modulus b)))
    HoareTime (FlatCoordinateCleanSchedule.program physical) (fun z => z = bank input)
      (fun z => ∃ output, z = bank output ∧
        ∀ x s, x ∘ helperBasisAxis p = embed s → ∃ y,
          y ∘ helperBasisAxis p = embed (AffineFieldProgram.run spec s) ∧
          (∀ j, (∀ i, j ≠ helperBasisAxis p i) → y j = x j) ∧
          ∀ j : Fin W, output (FlatCoordinateLayout.index y j) = input (FlatCoordinateLayout.index x j))
      (FlatCoordinateCleanSchedule.constant physical*((modulus b)^128*W)) := by
  intro physical bank spec
  apply (FlatCoordinateCleanSchedule.realizes physical b W live input).consequence (fun _ h => h) _ le_rfl
  intro z result
  refine ⟨_,result.1,?_⟩
  intro x s active
  let y := OrderedAffine.run (physical.map fun op => op.action b) x
  refine ⟨y,?_,?_,result.2 x⟩
  · have action := helperBasis_read p (description ops good) b x
    rw [active,description_actions ops good b,segment_run _ (nonrecursive_map ops good b)] at action
    simpa only [y,physical,List.map_map,Function.comp_def] using action
  · intro j outside
    simpa only [y,physical,List.map_map,Function.comp_def] using
      helperBasis_spectator p (description ops good) b x j outside

/-- On a flat owner the interval builder accepts the original compact input.
Moving the slot changes the program's prefix and suffix, but its runtime
inputs still contain the same atom width, child rank and spectator count. -/
theorem helperSubinterval_header (n : Fin 9) (h : Fin 439) (w W lo hi : ℕ) :
    let p := (helperPosition (n,h)).val
    let child := inheritedInterval ⟨1,1,1,64*w,1,W⟩ ((p+lo)*w) ((hi-lo)*w) ((64-(p+hi))*w)
    child = phaseIntervalChild (p+lo) (p+hi) w W 64 ∧
      phaseHeaderInput (p+lo) (p+hi) w W = phaseHeaderInput lo hi w W := by
  intro p child
  have rank : p+hi-(p+lo) = hi-lo := by omega
  constructor
  · simpa only [rank] using inheritedInterval_flat (p+lo) (p+hi) 64 w W
  · simp only [phaseHeaderInput,rank]

open RecursiveInterchangeLayout M8.RevMachine in
/-- With its interval header installed, a stopping helper child exchanges the
scheduled fields on the owner's tape at a fixed linear rate below cutoff. -/
theorem stoppedHelperSubinterval_runs [M8.Machine.Net] {T : ℕ}
    (v : Descriptor) (positive : v.Positive) (n : Fin 9) (r : Fin 32) (d : Fin 5) (h : Fin 439)
    (w lo hi cutoff : ℕ) (width : v.width = 64*w) (ordered : lo ≤ hi) (fits : hi ≤ 8)
    (live : 0 < (hi-lo)*w) (stop : (hi-lo)*w ≤ cutoff)
    (io : Fin T) (roles : Tapes T prime) (x : Fin (volume prime v) → ZMod 2)
    (head : roles.head io = 0)
    (stored : roles.tape io = M8.Machine.ArbitraryWidthHighExchangeShared.sourceWord x)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime)
    (ctr : Fin CommonBank.K → Option ℕ) (st : Tapes 2 prime) :
    let slot := IntegerMultBounds.MathlibTM2.M6.BitNode.slotOf n.val h.val
    let start := 7*idleSource slot.idle + 8*(((hostRole n r d h).cls.val+5-d.val)%5)
    let child := inheritedInterval v ((start+lo)*w) ((hi-lo)*w) ((64-(start+hi))*w)
    ∃ (y : Fin (volume prime v) → ZMod 2) (cost : ℕ), GraphContract.Runs (LeafCore.core io)
      (CommonBank.bank roles (Routines.hdr child) f p node scalar ctr st)
      (CommonBank.bank (SharedPlacementAlphabet.setTape roles io
        (M8.Machine.ArbitraryWidthHighExchangeShared.sourceWord y) 0)
        (Routines.hdr child) f p node scalar ctr st) cost ∧
      (cost : ℝ) ≤ |LeafCore.C| * volume prime v * cutoff ∧
      Cover.LabelView.Swapped prime child (ext x) (ext y) := by
  intro slot start child
  have size := helperSubinterval_volume v n h w lo hi width ordered fits
  dsimp only at size
  rw [helperSubinterval_descriptor v n r d h w lo hi fits] at size
  obtain ⟨y,run,effect⟩ := Cover.LabelExchange.realizes_view size positive io roles x head stored f p node scalar ctr st
  refine ⟨y,_,run,?_,effect⟩
  apply RevBudget.coreCost_le
  change ((max 1 ((hi-lo)*w) : ℕ) : ℝ)^M8.Machine.BudgetBound.tau ≤ cutoff
  rw [max_eq_right live]
  exact (Real.rpow_le_self_of_one_le (by exact_mod_cast live : (1 : ℝ) ≤ ((hi-lo)*w : ℕ))
    M8.Machine.BudgetBound.exponent_range.2.le).trans (by exact_mod_cast stop)

open IntegerMultBounds.Swap.Modular M8.Exchange in
/-- The invocation exchanges the scheduled parent span when its helper word
is read at the flat packing address, with the actual local port encoding. -/
theorem OrthogonalPortReads.packedHelper {V W : ℕ} (n : Fin 9) (h : Fin 439) (w : ℕ)
    [NeZero (prime^w)] (pos : IntegerMultBounds.Swap.Shear.State (Fin 8) (ZMod (prime^w)) →
      Fin ((prime^w)^112*W) → Fin V)
    (input output : Fin 661 → Fin V → ZMod 2) (read : OrthogonalPortReads w pos input output) :
    let slot := IntegerMultBounds.MathlibTM2.M6.BitNode.slotOf n.val h.val
    let c := port (slot.copy % 111)
    let readAt := fun (i : Fin ((prime^w)^128*W)) =>
      let a := copyAddress (i.cast (by rw [← Nat.mul_assoc,← pow_add]))
      pos a.1 a.2
    let address := fun s (j : Fin W) => readAt (FlatCoordinateLayout.index
      (helperSlotField c (some (helperPosition (n,h))) w s) j)
    let reg : Fin 661 := ⟨222+h.val,by omega⟩
    ∀ s j, output reg (address (exchange (reduce (prime^w) (helperSpan n h)) s) j) =
      input reg (address s j) := by
  intro slot c readAt address reg s j
  let H := (reduce (prime^w) (c.helperChart (slotPos slot) (slotPos_le n n.isLt h h.isLt))).transpose
  have cell (a : IntegerMultBounds.Swap.Shear.State Axis (ZMod (prime^w))) :
      address a j = pos (copyAddress (chartAddress (transform H H a,j))).1
        (copyAddress (chartAddress (transform H H a,j))).2 := by
    dsimp only [address,readAt]
    rw [helperSlotField_some]
    apply congrArg (fun i => pos (copyAddress i).1 (copyAddress i).2)
    exact Fin.ext (helperDigits_index (transform H H a) j)
  rw [cell,cell]
  exact read.helperSlot n h w pos input output s j

/-- The invocation reads data in place and reads each helper in the inherited
order of its own scheduled slot. -/
noncomputable def invocationOwnerAddress {M W : ℕ} [NeZero M] (n : Fin 9) (i : Fin 661) :
    Equiv.Perm (Fin (M^128*W)) :=
  if h : 222 ≤ i.val then inheritedHelperAddress (helperPosition (n,⟨i.val-222,by omega⟩))
  else Equiv.refl _

/-- A completed invocation can be read with arbitrary helper layouts. Only the
output read of each helper changes: exchange its logical halves before applying
its layout and exchange the resulting physical halves afterwards. -/
theorem OrthogonalPortReads.reindexHelpers {V W w : ℕ}
    (address : (Swap.Shear.State (Fin 8) (ZMod (prime^w)) × Fin W) ≃ Fin V)
    (layout : Fin 661 → Equiv.Perm (Fin V))
    (dataFixed : ∀ i : Fin 661, i.val < 222 → layout i = Equiv.refl _)
    {x y : Fin 661 → Fin V → ZMod 2}
    (read : OrthogonalPortReads w (fun s k => address (s,k)) x y) :
    let swap := fun i => let p := address.symm i; address (p.1.swap,p.2)
    OrthogonalPortReads w (fun s k => address (s,k)) (fun i => x i ∘ layout i)
      (fun i j => if i.val < 222 then y i j else y i (swap (layout i (swap j)))) := by
  intro swap
  constructor
  · intro t s k
    simpa only [show t.val < 222 by omega,ite_true,Function.comp_apply,
      dataFixed ⟨t.val,by omega⟩ (show t.val < 222 by omega),Equiv.refl_apply] using read.source t s k
  · intro t s k
    have ht : 111+t.val < 222 := by omega
    simpa only [ht,ite_true,Function.comp_apply,dataFixed ⟨111+t.val,by omega⟩ ht,
      dataFixed ⟨t.val,by omega⟩ (show t.val < 222 by omega),Equiv.refl_apply] using read.target t s k
  · intro h s k
    let reg : Fin 661 := ⟨222+h.val,by omega⟩
    have unwrap : swap (address (s.swap,k)) = address (s,k) := by simp [swap]
    simp only [show ¬222+h.val < 222 by omega,ite_false,unwrap,Function.comp_apply]
    let p := address.symm (layout reg (address (s,k)))
    exact (read.helper h p.1 p.2).trans (congrArg (x reg) (address.apply_symm_apply _))

open IntegerMultBounds.Swap.Modular M8.Exchange in
theorem OrthogonalPortReads.inheritedHelper {w W : ℕ} [NeZero (prime^w)] (n : Fin 9)
    (input output : Fin 661 → Fin ((prime^w)^128*W) → ZMod 2) :
    let size : (prime^w)^16*((prime^w)^112*W) = (prime^w)^128*W := by
      rw [← Nat.mul_assoc,← pow_add]
    let pos := fun s j => (copyAddress.symm (s,j)).cast size
    let view := fun (word : Fin 661 → Fin ((prime^w)^128*W) → ZMod 2) i =>
      word i ∘ invocationOwnerAddress n i
    OrthogonalPortReads w pos (view input) (view output) →
    ∀ (h : Fin 439) s (j : Fin W),
      let c := port ((IntegerMultBounds.MathlibTM2.M6.BitNode.slotOf n.val h.val).copy % 111)
      let reg : Fin 661 := ⟨222+h.val,by omega⟩
      let addr := fun a => FlatCoordinateLayout.index (helperSlotField c none w a) j
      output reg (addr (exchange (reduce (prime^w) (helperSpan n h)) s)) = input reg (addr s) := by
  intro size pos view read h s j c reg addr
  have run := read.packedHelper n h w pos (view input) (view output) s j
  let packed := fun a => FlatCoordinateLayout.index (helperSlotField c (some (helperPosition (n,h))) w a) j
  have atCell (a) : invocationOwnerAddress n reg (packed a) = addr a := by
    have hit : 222 ≤ reg.val := Nat.le_add_right _ _
    simp only [invocationOwnerAddress,dite_eq_left hit,reg,Nat.add_sub_cancel_left]
    exact inheritedHelperAddress_index c (helperPosition (n,h)) a j
  have cancel (i : Fin ((prime^w)^128*W)) :
      pos (copyAddress (i.cast size.symm)).1 (copyAddress (i.cast size.symm)).2 = i := by
    simp only [pos,Prod.mk.eta,Equiv.symm_apply_apply,Fin.cast_cast,Fin.cast_refl,id_eq]
  change output reg (invocationOwnerAddress n reg (pos _ _)) = input reg (invocationOwnerAddress n reg (pos _ _)) at run
  rw [cancel,cancel] at run
  let b := exchange (reduce (prime^w) (helperSpan n h)) s
  change output reg (invocationOwnerAddress n reg (packed b)) = input reg (invocationOwnerAddress n reg (packed s)) at run
  rwa [atCell b,atCell s] at run

noncomputable def helperSlotChange (n : Fin 9) (run : Fin 32 × Fin 5)
    (before : Fin 142081 → Option (Fin 9 × Fin 439)) (h : Fin 439) : Fin 142081 × Option (Fin 56) × Option (Fin 56) :=
  let t := ownerTape n run.1 run.2 ⟨222+h.val,by omega⟩
  (t,(before t).map helperPosition,some (helperPosition (n,h)))

/-- Enter first-use slots from the port descriptor and skip repeated slots already in place. -/
noncomputable def scheduledSlotChanges (n : Fin 9) (run : Fin 32 × Fin 5)
    (before : Fin 142081 → Option (Fin 9 × Fin 439)) : List (Fin 142081 × Option (Fin 56) × Option (Fin 56)) :=
  let change := helperSlotChange n run before
  ((List.finRange 439).filter fun h => (change h).2.1 != (change h).2.2).map change

/-- Every recorded slot in the sweep prefix was installed by an invocation
on that same physical owner. -/
theorem helperChart_origin (n : Fin 9) (prefixRuns : List (Fin 32 × Fin 5)) (t : Fin 142081)
    (entry : Fin 9 × Fin 439)
    (recorded : (prefixRuns.foldl (fun c p => helperChartsAfter n p c) (fun _ => none)) t = some entry) :
    ∃ p ∈ prefixRuns, entry.1 = n ∧ ownerTape n p.1 p.2 ⟨222+entry.2.val,by omega⟩ = t := by
  induction prefixRuns using List.reverseRecOn with
  | nil => cases recorded
  | append_singleton ps p ih =>
    rw [List.foldl_append,List.foldl_cons,List.foldl_nil,helperChartsAfter] at recorded
    split at recorded
    next hit =>
      obtain rfl := Option.some.inj recorded
      exact ⟨p,by simp,rfl,hit.choose_spec⟩
    next =>
      obtain ⟨q,mem,origin⟩ := ih recorded
      exact ⟨q,List.mem_append_left _ mem,origin⟩

theorem scheduledSlotChanges_unique (n : Fin 9) (run : Fin 32 × Fin 5) (before) :
    ((scheduledSlotChanges n run before).map Prod.fst).Nodup := by
  unfold scheduledSlotChanges
  rw [List.map_map]
  apply List.Nodup.map _ ((List.nodup_finRange _).filter _)
  intro h k same
  have eqn := congrArg Fin.val (ownerTape_injective n run.1 run.2 same)
  exact Fin.ext (Nat.add_left_cancel eqn)

private theorem trace_off {k w W : ℕ} (ls : List (Fin k × Option (Fin 56) × Option (Fin 56))) (a b)
    (trace : HelperSlotTrace w W ls a b) (t : Fin k) (off : ∀ p ∈ ls, p.1 ≠ t) : b t = a t := by
  induction ls generalizing a with
  | nil => exact congrFun trace.symm t
  | cons p ps ih =>
    obtain ⟨word,_,tail⟩ := trace
    rw [ih _ tail (fun q hq => off q (List.mem_cons_of_mem _ hq)),Function.update_of_ne
      (Ne.symm (off p List.mem_cons_self))]

private theorem trace_slot {k w W : ℕ} (ls : List (Fin k × Option (Fin 56) × Option (Fin 56))) (a b)
    (trace : HelperSlotTrace w W ls a b) (unique : (ls.map Prod.fst).Nodup)
    (t : Fin k) (x y : Option (Fin 56)) (hit : (t,x,y) ∈ ls) (c : PortCertificate) s j :
    b t (FlatCoordinateLayout.index (helperSlotField c y (w+1) s) j) =
      a t (FlatCoordinateLayout.index (helperSlotField c x (w+1) s) j) := by
  induction ls generalizing a with
  | nil => simp at hit
  | cons p ps ih =>
    obtain ⟨fresh,nd⟩ := List.nodup_cons.mp unique
    obtain ⟨word,read,tail⟩ := trace
    rcases List.mem_cons.mp hit with eqn | mem
    · subst p
      rw [trace_off ps _ _ tail t (fun q hq eq => fresh (List.mem_map.mpr ⟨q,hq,eq⟩)),
        Function.update_self]
      exact read c s j
    · rw [ih _ tail nd mem,Function.update_of_ne]
      intro eqn
      exact fresh (eqn ▸ List.mem_map_of_mem mem)

/-- Read any returning helper at its scheduled position, including a call
that reuses the previous slot without touching the owner. -/
theorem scheduledSlotRead (n : Fin 9) (run : Fin 32 × Fin 5) (before) {w W : ℕ} (a b)
    (trace : HelperSlotTrace w W (scheduledSlotChanges n run before) a b) (h : Fin 439) :
    let change := helperSlotChange n run before h
    ∀ c s j, b change.1 (FlatCoordinateLayout.index (helperSlotField c change.2.2 (w+1) s) j) =
      a change.1 (FlatCoordinateLayout.index (helperSlotField c change.2.1 (w+1) s) j) := by
  intro change c s j
  by_cases same : change.2.1 = change.2.2
  · let pos := fun i : Option (Fin 56) => FlatCoordinateLayout.index (helperSlotField c i (w+1) s) j
    change b change.1 (pos change.2.2) = a change.1 (pos change.2.1)
    rw [same]
    apply congrFun
    apply trace_off _ _ _ trace
    intro p hp eqn
    obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hp
    have ij := congrArg Fin.val (ownerTape_injective n run.1 run.2 eqn)
    have kh : k = h := Fin.ext (Nat.add_left_cancel ij)
    subst k
    exact (bne_iff_ne.mp (List.mem_filter.mp hk).2) same
  · apply trace_slot _ _ _ trace (scheduledSlotChanges_unique ..)
    apply List.mem_map.mpr
    exact ⟨h,List.mem_filter.mpr ⟨List.mem_finRange _,bne_iff_ne.mpr same⟩,rfl⟩

open Stack Host Cover.Fallback in
/-- The physical batch selected by the incoming chart history works for
all parent widths with one charge coefficient per scheduled invocation. -/
theorem scheduledSlotPack_exec [M8.Machine.Net] {P U : Type} (n : Fin 9) (run : Fin 32 × Fin 5)
    (prefixRuns : List (Fin 32 × Fin 5))
    (body : P → Pr P ((rowSwapBlock.tapes+35)+142081) rowSwapBlock.states prime U) :
    let before := prefixRuns.foldl (fun c p => helperChartsAfter n p c) (fun _ => none)
    ∃ code C, ∀ w W : ℕ, 0 < W →
      let M := prime^(w+1)
      let V := M^128*W
      ∀ v (owners : Stacks 142081 prime) (data : Fin 142081 → Fin V → ZMod 2),
      (∀ t z, readAt blank (owners.L t) (owners.R t) z = M8.AtomBank.arrTape (SparseRoleCircuit.encode ∘ data t) z) →
      ∃ z F, ∃ time : ℕ, ∃ result : Fin 142081 → Fin V → ZMod 2, z.user = v.user ∧
        (time : ℝ) ≤ C*V*((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau ∧
        Exec body code (mk v (helperPackInput w W owners)) time (mk z F) ∧
        (∀ t : Fin 142081, ∀ j, readAt blank (F.L (t.natAdd (rowSwapBlock.tapes+35)))
          (F.R (t.natAdd (rowSwapBlock.tapes+35))) j = M8.AtomBank.arrTape (SparseRoleCircuit.encode ∘ result t) j) ∧
        (∀ t, (∀ h : Fin 439, (helperSlotChange n run before h).1 ≠ t) → result t = data t) ∧
        ∀ h : Fin 439, let change := helperSlotChange n run before h
          ∀ c s j, result change.1 (FlatCoordinateLayout.index (helperSlotField c change.2.2 (w+1) s) j) =
            data change.1 (FlatCoordinateLayout.index (helperSlotField c change.2.1 (w+1) s) j) := by
  intro before
  obtain ⟨code,C,batch⟩ := helperSlotBatch_fromOwners (scheduledSlotChanges n run before) body
  refine ⟨code,C,?_⟩
  intro w W live M V v owners data input
  obtain ⟨z,F,time,result,user,cost,exec,reads,trace⟩ := batch w W live v owners data input
  refine ⟨z,F,time,result,user,cost,exec,reads,?_,scheduledSlotRead n run before _ _ trace⟩
  intro t off
  apply trace_off _ _ _ trace
  rintro p hp
  obtain ⟨h,_,rfl⟩ := List.mem_map.mp hp
  exact off h

end IntegerMultBounds.MathlibTM2.M6.BitNode
