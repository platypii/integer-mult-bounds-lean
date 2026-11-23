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

open ActualAffineScaling AffineFieldCoordinates in
def HelperSlotTransport {α : Type*} {b W : ℕ} (p : Fin 56)
    (act : Swap.Shear.State (Fin 8) (ZMod (modulus b)) → Swap.Shear.State (Fin 8) (ZMod (modulus b)))
    (input output : Fin ((modulus b)^128*W) → α) : Prop :=
  ∀ x s, x ∘ helperBasisAxis p = embed s → ∃ y,
    y ∘ helperBasisAxis p = embed (act s) ∧
    (∀ j, (∀ i, j ≠ helperBasisAxis p i) → y j = x j) ∧
    ∀ j : Fin W, output (FlatCoordinateLayout.index y j) = input (FlatCoordinateLayout.index x j)

theorem HelperSlotTransport.comp {α : Type*} {b W : ℕ} {p : Fin 56} {f g}
    {input middle output : Fin ((ActualAffineScaling.modulus b)^128*W) → α}
    (enter : HelperSlotTransport p f input middle) (leave : HelperSlotTransport p g middle output) :
    HelperSlotTransport p (g ∘ f) input output := by
  intro x s active
  obtain ⟨y,atY,offY,readY⟩ := enter x s active
  obtain ⟨z,atZ,offZ,readZ⟩ := leave y (f s) atY
  exact ⟨z,atZ,fun j hj => (offZ j hj).trans (offY j hj),fun j => (readZ j).trans (readY j)⟩

open ActualAffineScaling FlatCoordinateLayout AffineFieldCoordinates in
/-- Every output cell of an invertible slot action inherits its symbol from
an input cell, including words supplied with arbitrary spectator contents. -/
theorem HelperSlotTransport.range_subset {α : Type*} {b W : ℕ} {p : Fin 56} {act}
    {input output : Fin ((modulus b)^128*W) → α} (run : HelperSlotTransport p act input output)
    (onto : Function.Surjective act) : Set.range output ⊆ Set.range input := by
  classical
  rintro _ ⟨cell,rfl⟩
  obtain ⟨⟨row,j⟩,rfl⟩ := finProdFinEquiv.surjective cell
  obtain ⟨target,rfl⟩ := (rankEquiv (Q := modulus b) (d := 128)).surjective row
  let digits := target ∘ helperBasisAxis p
  let state := (fun k : Fin 8 => digits (k.castAdd 8),fun k : Fin 8 => digits (k.natAdd 8))
  have packed : embed state = digits := Fin.append_castAdd_natAdd (m := 8) (n := 8) (f := digits)
  obtain ⟨s,hs⟩ := onto state
  let x := Function.extend (helperBasisAxis p) (embed s) target
  have active : x ∘ helperBasisAxis p = embed s := by
    funext k
    exact (helperBasisAxis_strict p).injective.extend_apply _ _ k
  obtain ⟨y,live,off,read⟩ := run x s active
  have same : y = target := by
    funext k
    by_cases hit : ∃ t, helperBasisAxis p t = k
    · obtain ⟨t,rfl⟩ := hit
      exact congrFun (live.trans ((congrArg embed hs).trans packed)) t
    · exact (off k (fun t eq => hit ⟨t,eq.symm⟩)).trans (Function.extend_apply' _ _ _ hit)
  refine ⟨index x j,?_⟩
  change input (index x j) = output (index target j)
  rw [← same]
  exact (read j).symm

/-- Recover a binary payload and its read equation from the symbol-level
basis run. The same argument works for any injective tape alphabet. -/
theorem HelperSlotTransport.decode {α β : Type*} {b W : ℕ} {p : Fin 56} {act}
    (encode : α → β) (faithful : Function.Injective encode)
    {input : Fin ((ActualAffineScaling.modulus b)^128*W) → α} {output}
    (run : HelperSlotTransport p act (encode ∘ input) output) (onto : Function.Surjective act) :
    ∃ y, output = encode ∘ y ∧ HelperSlotTransport p act input y := by
  have represented i : ∃ a, encode a = output i := by
    obtain ⟨k,h⟩ := run.range_subset onto ⟨i,rfl⟩
    exact ⟨input k,h⟩
  choose y encoded using represented
  refine ⟨y,funext (fun i => (encoded i).symm),?_⟩
  intro x s active
  obtain ⟨z,hz,off,read⟩ := run x s active
  exact ⟨z,hz,off,fun j => faithful ((encoded _).trans (read j))⟩

open FlatCoordinateLayout AffineFieldCoordinates M8.RevMachine RecursiveInterchangeLayout in
/-- The physical child transpose on the two inherited fields realizes the
middle exchange of the MOVE, including at either end of the helper slot. -/
theorem helperInterval_transport (p : Fin 56) {lo hi b W : ℕ} (ordered : lo ≤ hi) (fits : hi ≤ 8) :
    let child := phaseIntervalChild (p.val+lo) (p.val+hi) b W 64
    ∀ word : Fin (volume prime child) → ZMod 2,
      HelperSlotTransport (b := b) (W := W) p (Swap.Shear.run (intervalSwaps lo hi))
        (fun i => ext word i.val)
        (fun i => ext (Shared50RecursiveNodeRows.transpose (one_dvd child.rows) word) i.val) := by
  intro child word x s active
  let slot (k : Fin 8) : Fin 64 := ⟨p.val+k.val,by omega⟩
  have left (k : Fin 8) : helperBasisAxis p (k.castAdd 8) = (slot k).castAdd 64 := by
    apply Fin.ext
    simp [helperBasisAxis,slot,k.isLt]
  have right (k : Fin 8) : helperBasisAxis p (k.natAdd 8) = (slot k).natAdd 64 := by
    apply Fin.ext
    simp [helperBasisAxis,slot]
    omega
  let a := fun k : Fin 64 => x (k.castAdd 64)
  let d := fun k : Fin 64 => x (k.natAdd 64)
  have ha (k : Fin 8) : a (slot k) = s.1 k := by
    simpa only [a,Function.comp_apply,left,embed_h] using congrFun active (k.castAdd 8)
  have hd (k : Fin 8) : d (slot k) = s.2 k := by
    simpa only [d,Function.comp_apply,right,embed_d] using congrFun active (k.natAdd 8)
  let swap := fun (u v : Fin 64 → ZMod (prime^b)) (i : Fin 64) =>
    if p.val+lo ≤ i.val ∧ i.val < p.val+hi then v i else u i
  let y := Fin.append (swap a d) (swap d a)
  refine ⟨y,?_,?_,?_⟩
  · funext i
    cases i using Fin.addCases (m := 8) (n := 8) with
    | _ k =>
      have inside : (p.val+lo ≤ (slot k).val ∧ (slot k).val < p.val+hi) ↔
          lo ≤ k.val ∧ k.val < hi := by dsimp [slot]; omega
      change y (helperBasisAxis p _) = _
      first | rw [left] | rw [right]
      simp only [y,Fin.append_left,Fin.append_right,
        swap,inside,ha,hd,embed_h,embed_d,intervalSwaps_run]
      split_ifs with hit <;> simp [M8.Exchange.exchange,Matrix.sub_mulVec,Matrix.one_mulVec,
        Matrix.mulVec_diagonal,hit] <;> rfl
  · intro j
    cases j using Fin.addCases (m := 64) (n := 64) with
    | _ k =>
      intro off
      have outside : ¬(p.val+lo ≤ k.val ∧ k.val < p.val+hi) := by
        intro hit
        let t : Fin 8 := ⟨k.val-p.val,by omega⟩
        have eq : slot t = k := Fin.ext (by dsimp [slot,t]; omega)
        first | (apply off (t.castAdd 8); rw [left,eq]; done) | (apply off (t.natAdd 8); rw [right,eq])
      simp only [y,Fin.append_left,Fin.append_right,swap,a,d]
      exact if_neg outside
  · intro j
    have read := remainderInterval_fullRead (Nat.add_le_add_left ordered p.val)
      (show p.val+hi ≤ 64 by omega) word a d j
    have whole : Fin.append a d = x := Fin.append_castAdd_natAdd
    change _ = ext word (index (Fin.append a d) j).val at read
    rwa [whole] at read

open ActualAffineScaling in
/-- Compose the physical reads on the same 128-digit word in execution order. -/
theorem helperMove_transport {α : Type*} {b W : ℕ} (p : Fin 56) (lo hi : ℕ)
    (C : Matrix (Fin 8) (Fin 8) ℚ)
    (input loaded moved output : Fin ((modulus b)^128*W) → α) :
    let spec := List.map (AffineFieldProgram.mapOp (Swap.Modular.ratMod (modulus b)))
    HelperSlotTransport p (AffineFieldProgram.run (spec (M8.Exchange.transformOps C.adjugate C.adjugate))) input loaded →
    HelperSlotTransport p (Swap.Shear.run (intervalSwaps lo hi)) loaded moved →
    HelperSlotTransport p (AffineFieldProgram.run (spec (M8.Exchange.transformOps C C))) moved output →
    HelperSlotTransport p (AffineFieldProgram.run (spec (rationalMoveWord lo hi C))) input output := by
  intro spec enter child leave
  have action := (enter.comp child).comp leave
  intro x s active
  simpa only [rationalMoveWord_run,Function.comp_apply,spec] using action x s active

open ActualAffineScaling RecursiveInterchangeLayout M8.RevMachine in
/-- On a common owner bank, sequence the two linear passes around one
physical recursive transpose. Both joins and the child time are counted. -/
theorem helperMove_sequence {T q r u b W : ℕ} (p : Fin 56) {lo hi : ℕ}
    (ordered : lo ≤ hi) (fits : hi ≤ 8) (C : Matrix (Fin 8) (Fin 8) ℚ)
    (enter : Program T q prime) (child : Program T r prime) (leave : Program T u prime)
    (enterRate childTime leaveRate : ℕ) :
    let v := phaseIntervalChild (p.val+lo) (p.val+hi) b W 64
    let Word := Fin (volume prime v) → ZMod 2
    let V := (modulus b)^128*W
    let read := fun (word : Word) (i : Fin V) => ext word i.val
    let spec := List.map (AffineFieldProgram.mapOp (Swap.Modular.ratMod (modulus b)))
    ∀ (bank : Word → Tapes T prime),
    (∀ x, HoareTime enter (· = bank x) (fun z => ∃ y, z = bank y ∧ HelperSlotTransport p
      (AffineFieldProgram.run (spec (M8.Exchange.transformOps C.adjugate C.adjugate))) (read x) (read y)) (enterRate*V)) →
    (∀ x, HoareTime child (· = bank x)
      (· = bank (Shared50RecursiveNodeRows.transpose (one_dvd v.rows) x)) childTime) →
    (∀ x, HoareTime leave (· = bank x) (fun z => ∃ y, z = bank y ∧ HelperSlotTransport p
      (AffineFieldProgram.run (spec (M8.Exchange.transformOps C C))) (read x) (read y)) (leaveRate*V)) →
    ∀ x, HoareTime (IntegerMultBounds.Machine.seq enter (IntegerMultBounds.Machine.seq child leave))
      (· = bank x) (fun z => ∃ y, z = bank y ∧ HelperSlotTransport p
        (AffineFieldProgram.run (spec (rationalMoveWord lo hi C))) (read x) (read y))
      ((enterRate+leaveRate)*V+childTime+2) := by
  intro v Word V read spec bank first exchange last x
  rw [Nat.add_mul,show enterRate*V+leaveRate*V+childTime+2 =
    enterRate*V+1+(childTime+1+leaveRate*V) by omega]
  apply (first x).seq
  rintro _ ⟨loaded,rfl,entered⟩
  let moved := Shared50RecursiveNodeRows.transpose (one_dvd v.rows) loaded
  have finish := (exchange loaded).seq (last moved)
  obtain ⟨steps,config,bill,ran,halt,y,returned,left⟩ := finish (bank loaded) rfl
  exact ⟨steps,config,bill,ran,halt,y,returned,helperMove_transport p lo hi C _ _ _ _ entered
    (helperInterval_transport p ordered fits loaded) left⟩

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
        HelperSlotTransport p (AffineFieldProgram.run spec) input output)
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

open M8.Machine.Segments SharedPlacementAlphabet ActualAffineScaling in
/-- Place a lifted basis pass on the selected owner. The caller's remaining
tapes are preserved and the private payload slot is returned blank. -/
theorem helperSegment_placed {t : ℕ} (src : Fin t) (p : Fin 56)
    (ops : List (AffineFieldProgram.Op (Fin 8) ℚ)) (good : Good ops) (b W : ℕ)
    (live : 0 < W) (input : FlatCoordinateStages.Array 128 b W) (caller : Tapes t prime) :
    let physical := (description ops good).map (helperBasisOp p)
    let bank := fun word => SharedBankStageInput.raw (FlatCoordinateShiftSharedBank.common word)
      (FlatCoordinateCleanSchedule.tapeCount physical)
    let slot := segmentSource physical
    let scratch := fun word => setTape (bank word) slot (fun _ => blank) 0
    let spec := ops.map (AffineFieldProgram.mapOp (IntegerMultBounds.Swap.Modular.ratMod (modulus b)))
    caller.head src = (bank input).head slot → caller.tape src = (bank input).tape slot →
    HoareTime (Placement.placed (FlatCoordinateCleanSchedule.program physical) (sharedPlacement src slot))
      (fun z => z = caller.append (scratch input))
      (fun z => ∃ output, z = (setTape caller src ((bank output).tape slot) ((bank output).head slot)).append
          (scratch input) ∧ HelperSlotTransport p (AffineFieldProgram.run spec) input output)
      (FlatCoordinateCleanSchedule.constant physical*((modulus b)^128*W)) := by
  intro physical bank slot scratch spec head payload
  have ready : Placement.active (sharedPlacement src slot) (caller.append (scratch input)) = bank input := by
    rw [active_shared,head,payload]
    exact (setTape_setTape ..).trans (setTape_self ..)
  have placed := Placement.hoare_at (helperSegment_runs p ops good b W live input) _ _ ready
  apply placed.consequence (fun _ eq => eq) _ le_rfl
  rintro z ⟨_,⟨output,rfl,reads⟩,rfl⟩
  refine ⟨output,?_,reads⟩
  refine (replace_shared caller (scratch input) (bank output) src slot).trans ?_
  apply congrArg (Tapes.append _)
  change setTape (bank output) slot ((scratch input).tape slot) ((scratch input).head slot) = scratch input
  simp only [scratch,setTape,Function.update_self]
  apply congrArg₂ Tapes.mk
  · rfl
  · funext k
    by_cases eq : k = slot
    · simp [eq]
    · simp only [Function.update_of_ne eq,bank,SharedBankStageInput.raw]
      split
      next inside =>
        have nz : k.val ≠ 0 := fun zero => eq (Fin.ext zero)
        have index : (⟨k.val,inside⟩ : Fin 4) = 1 ∨ (⟨k.val,inside⟩ : Fin 4) = 2 ∨
            (⟨k.val,inside⟩ : Fin 4) = 3 := by simp only [Fin.ext_iff]; omega
        rcases index with h | h | h <;> rw [h] <;> rfl
      next => rfl

open M8.Machine.Segments SharedPlacementAlphabet ActualAffineScaling RecursiveInterchangeLayout
  M8.Machine.ArbitraryWidthHighExchangeShared in
/-- A placed basis pass returns a binary owner word with the transported reads. -/
theorem helperBasisWord_placed {t : ℕ} (src : Fin t) (p : Fin 56)
    (C : Matrix (Fin 8) (Fin 8) ℚ) (pass : CopyBasisPass C) (b W : ℕ) (live : 0 < W)
    (v : Descriptor) (size : volume prime v = (prime^b)^128*W)
    (input : Fin ((prime^b)^128*W) → ZMod 2) (caller : Tapes t prime) :
    let ops := M8.Exchange.transformOps C C
    let physical := (description ops pass.good).map (helperBasisOp p)
    let payload := fun (word : Fin ((prime^b)^128*W) → ZMod 2) =>
      sourceWord (fun i => word (Fin.cast size i))
    let slot := segmentSource physical
    let scratch := basisWorkspace physical (0 : Fin ((prime^b)^128*W) → ZMod 2)
    let spec := ops.map (AffineFieldProgram.mapOp (IntegerMultBounds.Swap.Modular.ratMod (modulus b)))
    caller.head src = 0 → caller.tape src = payload input →
    HoareTime (Placement.placed (FlatCoordinateCleanSchedule.program physical) (sharedPlacement src slot))
      (fun z => z = caller.append scratch)
      (fun z => ∃ output, z = (setTape caller src (payload output) 0).append
        scratch ∧ HelperSlotTransport p (AffineFieldProgram.run spec) input output)
      (FlatCoordinateCleanSchedule.constant physical*((modulus b)^128*W)) := by
  intro ops physical payload slot scratch spec head tape
  let bank := fun (word : Fin ((prime^b)^128*W) → ZMod 2) => SharedBankStageInput.raw
    (FlatCoordinateShiftSharedBank.common (d := 128) (b := b) (W := W) (SparseRoleCircuit.encode ∘ word))
    (FlatCoordinateCleanSchedule.tapeCount physical)
  have source word : (bank word).tape slot = payload word := by
    apply congrArg (fun xs => FlatRepeatedControlNormalize.encoded (radix := prime)
      (putWord (fun _ => blank) 0 xs))
    exact List.ofFn_congr size.symm (fun i => SparseRoleCircuit.encode (a := 0) (word i))
  have workspace := basisWorkspace_eq physical input 0
  have step := helperSegment_placed src p ops pass.good b W live
    (SparseRoleCircuit.encode ∘ input) caller head (tape.trans (source input).symm)
  apply step.consequence (fun _ h => h.trans (congrArg caller.append workspace.symm)) _ le_rfl
  rintro z ⟨output,placed,read⟩
  obtain ⟨y,rfl,transport⟩ := read.decode _ M8.RevMachine.RevSemantics.encode_injective
    (AffineFieldBijective.run_bijective spec (pass.legal b)).surjective
  refine ⟨y,placed.trans ?_,transport⟩
  change (setTape caller src ((bank y).tape slot) 0).append (basisWorkspace physical input) = _
  exact congrArg₂ Tapes.append (congrArg (fun tape => setTape caller src tape 0) (source y)) workspace

open M8.Machine.Segments SharedPlacementAlphabet ActualAffineScaling RecursiveInterchangeLayout
  M8.RevMachine M8.Machine.ArbitraryWidthHighExchangeShared in
/-- Run a basis pass on the descriptor-indexed payload used by the recursive call. -/
theorem helperBasis_onOwner {t : ℕ} (src : Fin t) (p : Fin 56)
    (C : Matrix (Fin 8) (Fin 8) ℚ) (pass : CopyBasisPass C) (b W : ℕ) (live : 0 < W)
    (v : Descriptor) (size : volume prime v = (prime^b)^128*W) (caller : Tapes t prime) :
    let ops := M8.Exchange.transformOps C C
    let stages := (description ops pass.good).map (helperBasisOp p)
    let scratch := basisWorkspace stages (0 : Fin ((prime^b)^128*W) → ZMod 2)
    let bank := fun x => (setTape caller src (sourceWord (v := v) x) 0).append scratch
    let read := fun (x : Fin (volume prime v) → ZMod 2) (i : Fin ((prime^b)^128*W)) => ext x i.val
    let spec := ops.map (AffineFieldProgram.mapOp (Swap.Modular.ratMod (modulus b)))
    ∀ x, HoareTime (Placement.placed (FlatCoordinateCleanSchedule.program stages)
      (sharedPlacement src (segmentSource stages))) (· = bank x)
      (fun z => ∃ y, z = bank y ∧ HelperSlotTransport p (AffineFieldProgram.run spec) (read x) (read y))
      (FlatCoordinateCleanSchedule.constant stages*((modulus b)^128*W)) := by
  intro ops stages scratch bank read spec x
  have castRead (word : Fin (volume prime v) → ZMod 2) i :
      read word i = word (Fin.cast size.symm i) := by
    simp [read,M8.RevMachine.ext,show i.val < volume prime v by rw [size]; exact i.isLt]
    rfl
  let loaded := setTape caller src (sourceWord x) 0
  have step := helperBasisWord_placed src p C pass b W live v size (read x) loaded
    (by simp [loaded,setTape]) (by simp [loaded,setTape,castRead])
  apply step.consequence (fun _ h => h) _ le_rfl
  rintro _ ⟨y,rfl,transport⟩
  refine ⟨fun i => y (Fin.cast size i),?_,?_⟩
  · simp only [loaded,setTape_setTape,bank,scratch,stages,ops]
    rfl
  · simpa only [funext (fun i => castRead (fun k => y (Fin.cast size k)) i),Fin.cast_cast,
      Fin.cast_refl,id_eq,spec,ops] using transport

open M8.Machine.Segments SharedPlacementAlphabet ActualAffineScaling RecursiveInterchangeLayout
  M8.RevMachine M8.Machine.ArbitraryWidthHighExchangeShared in
/-- Both helper basis passes share the child's source tape. Each private workspace
is restored and the recursive call is charged once. -/
theorem helperMove_onOwner {t q : ℕ} (src : Fin t) (p : Fin 56) {lo hi : ℕ}
    (ordered : lo ≤ hi) (fits : hi ≤ 8) (C : Matrix (Fin 8) (Fin 8) ℚ)
    (rev : CopyBasisPass C.adjugate) (fwd : CopyBasisPass C) (b W : ℕ) (live : 0 < W)
    (caller : Tapes t prime) (child : Program t q prime) (childTime : ℕ) :
    let v := phaseIntervalChild (p.val+lo) (p.val+hi) b W 64
    let owner := fun x => setTape caller src (sourceWord (v := v) x) 0
    let A := (description _ rev.good).map (helperBasisOp p)
    let B := (description _ fwd.good).map (helperBasisOp p)
    let n := FlatCoordinateCleanSchedule.tapeCount A
    let m := FlatCoordinateCleanSchedule.tapeCount B
    let zero : Fin ((prime^b)^128*W) → ZMod 2 := 0
    let bank := fun x => ((owner x).append (basisWorkspace B zero)).append (basisWorkspace A zero)
    let enter := Placement.placed (FlatCoordinateCleanSchedule.program A)
      (sharedPlacement (Fin.castAdd m src) (segmentSource A))
    let leave := Placement.placed (FlatCoordinateCleanSchedule.program B) (sharedPlacement src (segmentSource B))
    let spec := List.map (AffineFieldProgram.mapOp (Swap.Modular.ratMod (modulus b)))
    let read := fun (x : Fin (volume prime v) → ZMod 2) (i : Fin ((prime^b)^128*W)) => ext x i.val
    (∀ x, HoareTime child (· = owner x)
      (· = owner (Shared50RecursiveNodeRows.transpose (one_dvd v.rows) x)) childTime) →
    ∀ x, HoareTime (seq enter (seq (extend (extend child m) n) (extend leave n))) (· = bank x)
      (fun z => ∃ y, z = bank y ∧ HelperSlotTransport p
        (AffineFieldProgram.run (spec (rationalMoveWord lo hi C))) (read x) (read y))
      ((FlatCoordinateCleanSchedule.constant A+FlatCoordinateCleanSchedule.constant B)*
        ((prime^b)^128*W)+childTime+2) := by
  intro v owner A B n m zero bank enter leave spec read exchange
  have size : volume prime v = (prime^b)^128*W :=
    intervalChild_volume (Nat.add_le_add_left ordered p.val) (by omega) b W
  apply helperMove_sequence p ordered fits C _ _ _ _ _ _ bank
  · intro x
    have placed := helperBasis_onOwner (Fin.castAdd m src) p
      C.adjugate rev b W live v size (caller.append (basisWorkspace B zero)) x
    simp only [setTape_append_left] at placed
    exact placed
  · intro x
    exact hoare_extend_eq (hoare_extend_eq (exchange x) (basisWorkspace B zero)) (basisWorkspace A zero)
  · intro x
    have pass := (helperBasis_onOwner src p C fwd b W live v size caller x).extend (basisWorkspace A zero)
    apply pass.consequence (fun _ h => ⟨_,rfl,h⟩) _ le_rfl
    rintro _ ⟨_,⟨y,rfl,transport⟩,rfl⟩
    exact ⟨y,rfl,transport⟩

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
