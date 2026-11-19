module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackPhysicalSignedPass
public import IntegerMultBounds.MathlibTM2.Cover.FallbackConjugationQueue
public import IntegerMultBounds.MathlibTM2.Cover.LabelClassCost
public import IntegerMultBounds.MathlibTM2.Cover.LabelCountBank
public import IntegerMultBounds.MathlibTM2.Cover.LabelSpectators
public import IntegerMultBounds.MathlibTM2.Cover.LabelDirectorySetup
public import IntegerMultBounds.MathlibTM2.Cover.FallbackIdentitySeed

/-! Compose residual queue generation and the signed pass on their shared archive register. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host LabelTraversal
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
variable [M8.Machine.Net] {T K Q d r w W : ℕ} {P U : Type}
local notation "N" => rowSwapBlock.tapes+35

open Record RecursiveInterchangeLayout RingFormula Node
local notation "M" => prime^(w+1)
local instance : NeZero M := ⟨pow_ne_zero _ Networks.Shared50ModularControl.prime_prime.ne_zero⟩

noncomputable def seededQueueBody (r d : ℕ) (e : (Fin r ⊕ Fin r) ≃ Fin (d+1))
    (bank : Fin 18 ↪ Fin K) (recip : Fin 16 ↪ Fin K) (clock count : Fin K)
    (pool : Fin ((conjugationDepth r+1)*13) ↪ Fin K) (coeff : Fin r → Fin r → Fin 4 ↪ Fin K)
    (coeffOff : ∀ i j k l, recip k ≠ coeff i j l) (scan : Fin 6 ↪ Fin K)
    (mask seed tmp : Fin K) : Pr P K Q prime U :=
  let inputs := QueueLayout.formulaInputs.trans bank
  let source := sourcePorts (m := r) inputs id
  let weights := fun i j => QueueLayout.residualPorts recip (coeff i j) (coeffOff i j)
  let f := determinant (matrixInput false)
  let conjugate : Pr P K Q prime U := (.seq (directoryMatrix r (QueueLayout.readPorts.trans (QueueLayout.directoryWork.trans bank)) (QueueLayout.digitPorts.trans (QueueLayout.directoryWork.trans bank)) (bank 12) (bank 9) (bank 10)) (.seq (.seq (.seq (compile (readLeaf (leafBank source)) (registerBank pool) f 0 (recip 14)) (reusablePivotInverse prime recip clock count))
        (.seq (packedConjugate pool source (QueueLayout.normalizationPorts.trans recip) false true) (.seq (bclear (recip 0)) (bclear (recip 14))))) (bclear (bank 10))))
  let live : Pr P K Q prime U := .seq conjugate (.seq (sequence (fun i => sequence
      (fun j => blockEntry weights (e.symm i) (e.symm j)) (List.finRange (d+1))) (List.finRange (d+1))) (bclear (recip 13)))
  let branch := fun p => Prog.seq p (.seq (moveR (scan 4) (scan 5) id) (advanceDirectory r scan))
  (.seq (maskedScan mask (branch live) (branch (bcopy seed (scan 4) (scan 3) tmp)))
        (moveR (scan 5) (scan 4) id))

noncomputable def withIdentitySeed (d : ℕ) (zero one seed tmp saved : Fin K) (generate : Pr P K Q prime U) :
    Pr P K Q prime U :=
  .seq (.seq (identitySeed d zero one seed tmp saved) generate) (bclear seed)

/-- Write and release the binary constants and the square identity padding. -/
def paddingSetupCost (d H : ℕ) : ℕ := d*d*(8*H+6)+d+14*H+17

omit [M8.Machine.Net] in
theorem paddingSetupCost_eq (d H cost : ℕ) :
    6*H+6+(4*H+4+(d*(d*(6*H+6)+1)+1+cost+(2*(d*d*H)+2))+(2*H+2))+(2*H+2) =
      cost + paddingSetupCost d H := by unfold paddingSetupCost; ring

omit [M8.Machine.Net] in
/-- Splitting both address coordinates into field atoms and a spectator suffix
preserves the descriptor volume represented by all records of the pass. -/
theorem signedPassVolume_eq_descriptor (v : Descriptor) (e : (Fin r ⊕ Fin r) ≃ Fin (d+1))
    (w suffix : ℕ) (width : v.width = r*(w+1) + suffix) :
    LabelMask.records v * ((prime^(w+1))^(d+1) *
      (prime^(2*suffix)*v.between*v.afterD)) = volume prime v := by
  have dim := Fintype.card_congr e
  simp only [Fintype.card_sum, Fintype.card_fin] at dim
  simp only [LabelMask.records, volume, width, ← dim, pow_add, pow_mul,
    Nat.mul_comm r (w+1), two_mul suffix]
  ring

omit [M8.Machine.Net] in
/-- At the largest whole atom width fitting the rank, the spectator factor
is bounded independently of the address width. -/
theorem signedPassVolume_div_width (v : Descriptor) (e : (Fin r ⊕ Fin r) ≃ Fin (d+1))
    (fits : r ≤ v.width) :
    let atom := v.width / r
    let spectators := prime^(2*(v.width % r))*v.between*v.afterD
    0 < atom ∧ LabelMask.records v * ((prime^atom)^(d+1)*spectators) = volume prime v ∧
      spectators ≤ prime^(2*(r-1))*v.between*v.afterD := by
  have dim := Fintype.card_congr e
  simp only [Fintype.card_sum, Fintype.card_fin] at dim
  have rankPos : 0 < r := by omega
  have atomPos := Nat.div_pos fits rankPos
  refine ⟨atomPos, ?_, ?_⟩
  · have split := Nat.div_add_mod v.width r
    have atom := Nat.sub_add_cancel (show 1 ≤ v.width / r from atomPos)
    simpa only [atom] using signedPassVolume_eq_descriptor v e (v.width/r-1) (v.width%r)
      (by rw [atom]; exact split.symm)
  · apply Nat.mul_le_mul_right
    apply Nat.mul_le_mul_right
    apply Nat.pow_le_pow_right IntegerMultBounds.Networks.Shared50ModularControl.prime_prime.pos
    apply Nat.mul_le_mul_left
    have := Nat.mod_lt v.width rankPos
    omega

omit [M8.Machine.Net] in
/-- The spectator counter needs only the bits of the two descriptor fields
and a remainder allowance bounded by the rank. -/
theorem signedPassCounter_binaryWidth (v : Descriptor) {r : ℕ} (rankPos : 0 < r) :
    let W := prime^(2*(v.width % r))*v.between*v.afterD
    W < 2^Nat.size W ∧ Nat.size W ≤
      2*(r-1)*Nat.size prime + Nat.size v.between + Nat.size v.afterD := by
  intro W
  refine ⟨Nat.lt_size_self _, Nat.size_le.mpr ?_⟩
  have remainder := Nat.mod_lt v.width rankPos
  have field : prime^(2*(v.width % r)) ≤ (2^Nat.size prime)^(2*(r-1)) := by
    gcongr
    · exact Nat.one_le_two_pow
    · exact (Nat.lt_size_self prime).le
    · omega
  dsimp only [W]
  rw [pow_add, pow_add, Nat.mul_comm (2*(r-1)), pow_mul 2]
  exact Nat.mul_lt_mul_of_le_of_lt
    (Nat.mul_le_mul field (Nat.lt_size_self v.between).le) (Nat.lt_size_self v.afterD)
    (by positivity)

omit [M8.Machine.Net] in
/-- Spectator field lengths are absorbed by the two spectator factors in the
descriptor volume, even when their binary widths exceed the address width. -/
theorem signedPassCounter_volume_le (v : Descriptor) (positive : v.Positive)
    {r : ℕ} (rankPos : 0 < r) (live charge : ℕ) (count : live ≤ LabelMask.records v) :
    let W := prime^(2*(v.width % r))*v.between*v.afterD
    prime^(2*v.width)*(live*charge*Nat.size W) ≤
      charge*(2*(r-1)*Nat.size prime+2)*volume prime v := by
  intro W
  let allowance := 2*(r-1)*Nat.size prime
  have middle := positive.2.2.2.1
  have suffix := positive.2.2.2.2
  have bits (x : ℕ) : Nat.size x ≤ x := Nat.size_le.mpr Nat.lt_two_pow_self
  have between := (bits v.between).trans (Nat.le_mul_of_pos_right v.between suffix)
  have afterD := (bits v.afterD).trans (Nat.le_mul_of_pos_left v.afterD middle)
  have base := Nat.le_mul_of_pos_right allowance (Nat.mul_pos middle suffix)
  have width := (signedPassCounter_binaryWidth v rankPos).2
  change Nat.size W ≤ allowance + Nat.size v.between + Nat.size v.afterD at width
  have budget : Nat.size W ≤ (allowance+2)*(v.between*v.afterD) := by
    rw [Nat.add_mul]
    omega
  grw [budget, count]
  unfold allowance LabelMask.records volume
  rw [two_mul v.width, pow_add]
  exact le_of_eq (by ring)

omit [M8.Machine.Net] in
/-- The directory's per-record digit scan consumes an exponentially decreasing
fraction of descriptor volume as the address width grows. -/
theorem directoryDigits_volume_le (v : Descriptor) (positive : v.Positive)
    (r atom : ℕ) (fits : r*atom ≤ v.width) :
    prime^v.width * (LabelMask.records v * (19*(atom*(r*r))+(4*r*r+144))) ≤
      (19*r+(4*r*r+144))*volume prime v := by
  have width : v.width ≤ prime^v.width :=
    (Nat.lt_pow_self (IntegerMultBounds.Networks.Shared50ModularControl.prime_prime.one_lt)).le
  have power : 1 ≤ prime^v.width := Nat.one_le_pow _ _ (by
    exact IntegerMultBounds.Networks.Shared50ModularControl.prime_prime.pos)
  have digits : atom*(r*r) ≤ r*prime^v.width := by
    simpa only [Nat.mul_left_comm, Nat.mul_assoc, Nat.mul_comm] using
      Nat.mul_le_mul_left r (fits.trans width)
  have scan : 19*(atom*(r*r))+(4*r*r+144) ≤ (19*r+(4*r*r+144))*prime^v.width := by
    rw [Nat.add_mul, Nat.mul_assoc 19 r]
    exact Nat.add_le_add (Nat.mul_le_mul_left _ digits) (by simpa using Nat.mul_le_mul_left (4*r*r+144) power)
  have middle := positive.2.2.2.1
  have suffix := positive.2.2.2.2
  grw [scan]
  unfold LabelMask.records volume
  calc
    _ = (19*r+(4*r*r+144))*(v.beforeRows*v.rows*v.beforeH*prime^v.width*1*prime^v.width*1) := by ring
    _ ≤ _ := by gcongr <;> omega

/-- Reading inherited labels pays once per parent, per record, and per live record. -/
def inheritedLabelCost (r width parents records live : ℕ) :=
  width * (6*parents + 18*records + 12*r*r*live)

omit [M8.Machine.Net] in
theorem inheritedLabelCost_le_volume (v : Descriptor) (positive : v.Positive)
    (r width parents live : ℕ) (hp : parents ≤ LabelMask.records v)
    (hl : live ≤ LabelMask.records v) (hw : width ≤ prime^v.width) :
    prime^v.width * inheritedLabelCost r width parents (LabelMask.records v) live ≤
      (24+12*r*r)*volume prime v := by
  unfold inheritedLabelCost
  grw [hp, hl, hw]
  unfold LabelMask.records volume
  calc
    _ = (24+12*r*r)*(v.beforeRows*v.rows*v.beforeH*prime^v.width*1*prime^v.width*1) := by ring
    _ ≤ _ := by
      have middle := positive.2.2.2.1
      have suffix := positive.2.2.2.2
      gcongr <;> omega

def directorySetupCost (r atom width parents records live box : ℕ) :=
  records*(19*(atom*(r*r))+(4*r*r+144)) + inheritedLabelCost r width parents records live +
    25*parents + 151*box

omit [M8.Machine.Net] in
theorem directorySetupCost_le_volume (v : Descriptor) (positive : v.Positive)
    (r atom width parents live box : ℕ) (fits : r*atom ≤ v.width)
    (hp : parents ≤ LabelMask.records v) (hl : live ≤ LabelMask.records v)
    (hb : box ≤ LabelMask.records v) (hw : width ≤ prime^v.width) :
    prime^v.width * directorySetupCost r atom width parents (LabelMask.records v) live box ≤
      (16*r*r + 19*r + 344)*volume prime v := by
  have digits := directoryDigits_volume_le v positive r atom fits
  have labels := inheritedLabelCost_le_volume v positive r width parents live hp hl hw
  have records : prime^v.width * LabelMask.records v ≤ volume prime v := by
    have power := pow_pos IntegerMultBounds.Networks.Shared50ModularControl.prime_prime.pos v.width
    have middle := positive.2.2.2.1
    have suffix := positive.2.2.2.2
    unfold LabelMask.records volume
    calc
      _ = v.beforeRows*v.rows*v.beforeH*prime^v.width*1*1*1 := by ring
      _ ≤ _ := by gcongr <;> omega
  unfold directorySetupCost
  rw [Nat.mul_add, Nat.mul_add, Nat.mul_add]
  grw [digits, labels, hp, hb]
  rw [Nat.mul_left_comm _ 25, Nat.mul_left_comm _ 151]
  grw [records]
  exact le_of_eq (by ring)

omit [M8.Machine.Net] in
/-- A shaped descriptor supplies all three record-count bounds for directory setup. -/
theorem physicalDirectorySetupCost_le_volume (v : Descriptor) (positive : v.Positive)
    (r w B width : ℕ) (shape : v.beforeH = B*prime^(r*((w+1)*r)))
    (fits : r*(w+1) ≤ v.width) (hw : width ≤ prime^v.width) :
    let box := (prime^(w+1))^(r*r)
    let parents := v.beforeRows*v.rows*B
    let live := (∏ i : Fin r, (prime^r-prime^i.val))*(prime^w)^(r*r)
    prime^v.width * directorySetupCost r (w+1) width parents (LabelMask.records v)
      (parents*live) box ≤ (16*r*r+19*r+344)*volume prime v := by
  intro box parents live
  have count : LabelMask.records v = parents*box := by
    simp only [LabelMask.records, parents, box, shape, ← pow_mul]
    ring_nf
  have boxPos : 0 < box := pow_pos (pow_pos Networks.Shared50ModularControl.prime_prime.pos _) _
  have parentsPos : 0 < parents := by
    have before := positive.2.2.1
    rw [shape] at before
    exact Nat.mul_pos (Nat.mul_pos positive.1 positive.2.1) (Nat.pos_of_mul_pos_right before)
  have liveBound : live ≤ box := by
    have countLive := (liveLabelCount (m := r) (by omega : 0 < w+1)).trans (LabelPadding.unit_count w)
    have length := List.countP_le_length (p := LabelStock.live r (w+1) 1) (l := List.range box)
    simpa only [box, live, countLive, liveClasses_eq_product, List.length_range] using length
  apply directorySetupCost_le_volume v positive _ _ _ _ _ _ fits _ _ _ hw
  · rw [count]
    exact Nat.le_mul_of_pos_right _ boxPos
  · rw [count]
    exact Nat.mul_le_mul_left _ liveBound
  · rw [count]
    exact Nat.le_mul_of_pos_left _ parentsPos

omit [M8.Machine.Net] in
private theorem queueArchive_le (classes live words build : ℕ) (count : live ≤ classes) :
    live*(build + 4*words) + (classes-live)*(10*words+6) ≤
      live*build + classes*(10*words+6) := by
  have copy : 4*words ≤ 10*words+6 := by omega
  grw [copy]
  rw [← Nat.sub_add_cancel count]
  simp only [Nat.add_sub_cancel_right]
  exact le_of_eq (by ring)

omit [M8.Machine.Net] in
theorem queueArchive_volume_le (v : Descriptor) (positive : v.Positive) (n H : ℕ)
    (width : H ≤ prime^v.width) :
    prime^v.width * (LabelMask.records v*(10*(n*n*H)+6)) ≤
      (10*(n*n)+6)*volume prime v := by
  have power := pow_pos Networks.Shared50ModularControl.prime_prime.pos v.width
  have frame : 10*(n*n*H)+6 ≤ (10*(n*n)+6)*prime^v.width := by
    rw [Nat.add_mul, Nat.mul_assoc 10]
    exact Nat.add_le_add (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ width)) (by omega)
  grw [frame]
  unfold LabelMask.records volume
  calc
    _ = (10*(n*n)+6)*(v.beforeRows*v.rows*v.beforeH*prime^v.width*1*prime^v.width*1) := by ring
    _ ≤ _ := by
      have middle := positive.2.2.2.1
      have suffix := positive.2.2.2.2
      gcongr <;> omega

omit [M8.Machine.Net] in
/-- Binary modulus width meets the machine's strict radix bound and makes
archive copying affordable directly from the descriptor width. -/
theorem queueArchive_binaryWidth (v : Descriptor) (positive : v.Positive)
    (n atom : ℕ) (atomPos : 0 < atom) (fits : atom ≤ v.width) :
    let H := Nat.size (prime^atom)
    prime^atom < 2^H ∧ H ≤ atom * Nat.size prime ∧
      prime^v.width * (LabelMask.records v*(10*(n*n*H)+6)) ≤
        (10*(n*n)+6)*volume prime v := by
  intro H
  have radix : prime < 2^Nat.size prime := Nat.size_le.mp le_rfl
  refine ⟨Nat.size_le.mp le_rfl, Nat.size_le.mpr ?_, queueArchive_volume_le v positive n H ?_⟩
  · rw [Nat.mul_comm, pow_mul]
    exact Nat.pow_lt_pow_left radix atomPos.ne'
  · apply Nat.size_le.mpr
    exact (Nat.pow_le_pow_right Networks.Shared50ModularControl.prime_prime.pos fits).trans_lt
      Nat.lt_two_pow_self

omit [M8.Machine.Net] in
/-- The one-time padding setup is absorbed by a single address coordinate. -/
theorem paddingSetupCost_volume_le (v : Descriptor) (positive : v.Positive) (n atom : ℕ)
    (fits : atom ≤ v.width) :
    prime^v.width * paddingSetupCost n (Nat.size (prime^atom)) ≤
      paddingSetupCost n 1 * volume prime v := by
  let q := prime^v.width
  have power : 1 ≤ q := pow_pos Networks.Shared50ModularControl.prime_prime.pos _
  have bits : Nat.size (prime^atom) ≤ q := Nat.size_le.mpr
    ((Nat.pow_le_pow_right Networks.Shared50ModularControl.prime_prime.pos fits).trans_lt
      Nat.lt_two_pow_self)
  have setup : paddingSetupCost n (Nat.size (prime^atom)) ≤ paddingSetupCost n 1 * q := by
    unfold paddingSetupCost
    grw [bits]
    have hn := Nat.mul_le_mul_left n power
    have hnn := Nat.mul_le_mul_left (n*n) power
    ring_nf at hn hnn ⊢
    omega
  have room : q*q ≤ volume prime v := by
    obtain ⟨br, rows, bh, middle, suffix⟩ := positive
    unfold volume
    calc
      q*q = 1*1*1*q*1*q*1 := by ring
      _ ≤ _ := by gcongr <;> omega
  calc
    _ ≤ q*(paddingSetupCost n 1*q) := Nat.mul_le_mul_left q setup
    _ = paddingSetupCost n 1*(q*q) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ room

/-- The live part of the generated pass pays the density factor on both swaps
and shears, and the quotient-width factor on swaps. -/
theorem signedPassResidualCharge_le (L r swaps shears live V : ℕ) (rankPos : 0 < r)
    (fits : r ≤ L) :
    (((6 + (swaps * swapVolumeRate (L/r-1) + shears)) *
      min live (((prime-1)*V)/prime) : ℕ) : ℝ) ≤
      (6 + ((swaps : ℝ) * ((3808275 + M8.RevMachine.LeafCore.C) *
        ((L : ℝ)^M8.Machine.BudgetBound.tau / (r : ℝ)^M8.Machine.BudgetBound.tau)) + shears)) *
        (((prime-1 : ℕ) : ℝ) / prime * V) := by
  have volumeBound : ((min live (((prime-1)*V)/prime) : ℕ) : ℝ) ≤
      ((prime-1 : ℕ) : ℝ) / prime * V := by
    calc
      _ ≤ ((((prime-1)*V)/prime : ℕ) : ℝ) := by exact_mod_cast min_le_right _ _
      _ ≤ _ := by
        apply (Nat.cast_div_le (α := ℝ) (m := (prime-1)*V) (n := prime)).trans_eq
        rw [Nat.cast_mul]
        ring
  push_cast
  exact mul_le_mul (by gcongr; exact swapVolumeRate_div_width_le L r rankPos fits)
    (by simpa using volumeBound) (by positivity)
    (by have pos : 0 < M8.RevMachine.LeafCore.C := (Classical.choose_spec M8.Machine.ArbitraryWidthOriginalTotalRun.uniform_bound).1
        positivity)

omit [M8.Machine.Net] in
private theorem fixedBoxCost_le (r w : ℕ) (rankPos : 0 < r) :
    22*(prime^(w+1))^(r*r) + 21*(w+1) + 26*prime^w + 82 ≤
      151*(prime^(w+1))^(r*r) := by
  have primeLarge := IntegerMultBounds.Networks.Shared50ModularControl.prime_prime.one_lt
  have box : prime^(w+1) ≤ (prime^(w+1))^(r*r) := by
    simpa using Nat.pow_le_pow_right (pow_pos (by omega : 0 < prime) (w+1))
      (Nat.mul_pos rankPos rankPos : 1 ≤ r*r)
  have atom := (Nat.lt_pow_self (n := w+1) primeLarge).le.trans box
  have high := (Nat.pow_le_pow_right (by omega : 0 < prime) (Nat.le_succ w)).trans box
  omega

noncomputable def anchorClassCost (table : Matrix (Fin r) (Fin r) (ZMod prime) → Matrix (Fin (d+1)) (Fin (d+1)) (ZMod prime))
    (T w W : ℕ) (digits : Fin (r*r) → ZMod prime) :=
  let m := table (LabelSelectors.matrix r digits)
  Record.cost d T 1 (w+1) W (negativeAnchor (classPivots m) m) + 2

noncomputable def scanClassCost (table : Matrix (Fin r) (Fin r) (ZMod prime) → Matrix (Fin (d+1)) (Fin (d+1)) (ZMod prime))
    (w W H J : ℕ) (U : Type) (digits : Fin (r*r) → ZMod prime) :=
  let m := LabelSelectors.matrix r digits
  let volume := (prime^(w+1))^(d+1)*W
  let branch := if m.det ≠ 0 then
    6*volume+6+(1+signedResidualTime U (classPivots (table m)) w W H J)
    else 4*(d+1)*(d+1)+1
  branch+(4*volume+4)+((d+1)*(d+1)*(4*H+4)+1)+4

/-- Payload moves outside the residual kernel are proportional to record volume. -/
noncomputable def classVolumeRate (table : Matrix (Fin r) (Fin r) (ZMod prime) → Matrix (Fin (d+1)) (Fin (d+1)) (ZMod prime))
    (T : ℕ) (digits : Fin (r*r) → ZMod prime) :=
  let c := LabelSelectors.matrix r digits
  let m := table c
  14 + M8.AtomSegment.chainConst (anchorOps d (negativeAnchor (classPivots m) m))*(size d+T+5) +
    (if c.det ≠ 0 then 6 else 0)

noncomputable def classResidualCost (table : Matrix (Fin r) (Fin r) (ZMod prime) → Matrix (Fin (d+1)) (Fin (d+1)) (ZMod prime))
    (T w W H J : ℕ) (U : Type) (digits : Fin (r*r) → ZMod prime) :=
  let c := LabelSelectors.matrix r digits
  let branch := if c.det ≠ 0 then 7+signedResidualTime U (classPivots (table c)) w W H J
    else 4*(d+1)*(d+1)+1
  size d+3*T+34+(d+1)*(d+1)*(4*H+4)+branch

private theorem splitClassCost (table : Matrix (Fin r) (Fin r) (ZMod prime) → Matrix (Fin (d+1)) (Fin (d+1)) (ZMod prime))
    (T w W H J : ℕ) (U : Type) (xs : List (Fin (r*r) → ZMod prime)) :
    (xs.map fun x => anchorClassCost table T w W x + scanClassCost table w W H J U x).sum =
      ((prime^(w+1))^(d+1)*W)*(xs.map (classVolumeRate table T)).sum +
      (xs.map (classResidualCost table T w W H J U)).sum := by
  rw [← List.sum_map_mul_left,← List.sum_map_add]
  apply congrArg List.sum
  apply List.map_congr_left
  intro x _
  unfold anchorClassCost scanClassCost classVolumeRate classResidualCost Record.cost
  simp only [ActualAffineScaling.modulus,Nat.mul_one]
  split <;> ring

/-- Three label traversals and two round trips over the record volume accompany
the anchor and residual operations on each residue class. -/
noncomputable def signedPassWork (table : Matrix (Fin r) (Fin r) (ZMod prime) → Matrix (Fin (d+1)) (Fin (d+1)) (ZMod prime))
    (T parents records w W H J : ℕ) (U : Type) :=
  let classes := LabelSelectors.classes 1 (r*r)
  let perClass := ((prime^(w+1))^(d+1)*W)*(classes.map (classVolumeRate table T)).sum +
    (classes.map (classResidualCost table T w W H J U)).sum
  3*parents*(LabelTraversal.time (prime^w) (r*r) 1+5) +
    parents*(prime^w)^(r*r)*perClass + 4*records*((prime^(w+1))^(d+1)*W)

omit [M8.Machine.Net] in
private theorem invertibleClassCount (r : ℕ) :
    (LabelSelectors.classes 1 (r*r)).countP (LabelSelectors.accept r) =
      ∏ i : Fin r, (prime^r - prime^i.val) := by
  rw [LabelSelectors.classes_eq, one_mul, List.countP_map, ← liveClasses_eq_product]
  have count := liveLabelCount (m := r) (w := 1) (by decide)
  have units := LabelPadding.unit_count (m := r) 0
  rw [show LabelStock.live r 1 1 = fun j => decide ((LabelStock.residue r 1 1 j).det ≠ 0) from rfl] at count
  simpa only [LabelSelectors.residue_eq, pow_one, LabelSelectors.accept,
    Function.comp_def, pow_zero, one_pow, mul_one] using count.trans units

/-- The two possible signs give one anchor budget independent of the residue table. -/
def anchorVolumeRate (d T : ℕ) :=
  14 + max (M8.AtomSegment.chainConst (anchorOps d false))
    (M8.AtomSegment.chainConst (anchorOps d true)) * (size d+T+5)

omit [M8.Machine.Net] in
private theorem classVolumeRate_sum_le (table : Matrix (Fin r) (Fin r) (ZMod prime) →
    Matrix (Fin (d+1)) (Fin (d+1)) (ZMod prime)) (T : ℕ) :
    ((LabelSelectors.classes 1 (r*r)).map (classVolumeRate table T)).sum ≤
      prime^(r*r)*anchorVolumeRate d T + (∏ i : Fin r, (prime^r-prime^i.val))*6 := by
  have bound (xs : List (Fin (r*r) → ZMod prime)) :
      (xs.map (classVolumeRate table T)).sum ≤ xs.length*anchorVolumeRate d T +
        xs.countP (LabelSelectors.accept r)*6 := by
    induction xs with
    | nil => simp
    | cons x xs ih =>
      let m := table (LabelSelectors.matrix r x)
      have sign : M8.AtomSegment.chainConst (anchorOps d (negativeAnchor (classPivots m) m)) ≤
          max (M8.AtomSegment.chainConst (anchorOps d false)) (M8.AtomSegment.chainConst (anchorOps d true)) := by
        cases negativeAnchor (classPivots m) m <;> simp
      have cost := Nat.mul_le_mul_right (size d+T+5) sign
      dsimp [m] at cost
      by_cases live : (LabelSelectors.matrix r x).det = 0 <;>
        simp [classVolumeRate, LabelSelectors.accept, live, Nat.add_mul, anchorVolumeRate] at ih ⊢ <;> omega
  have length : (LabelSelectors.classes 1 (r*r)).length = prime^(r*r) := by
    simp [LabelSelectors.classes_eq]
  simpa only [length, invertibleClassCount] using bound (LabelSelectors.classes 1 (r*r))

/-- The most expensive column of an itinerary also occurs in a constant itinerary. -/
private theorem residualSetup_le_constant_sup (U : Type) (rows : Fin (d+1) → Fin (d+1))
    (w H : ℕ) : signedResidualTime U rows w 0 H 0 ≤
      Finset.univ.sup (fun r => signedResidualTime U (fun _ : Fin (d+1) => r) w 0 H 0) := by
  obtain ⟨k, hk, worst⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty
    (fun i => columnProgramTime U i (rows i) w 0 H 0)
  apply le_trans _ (Finset.le_sup (f := fun r => signedResidualTime U (fun _ => r) w 0 H 0)
    (Finset.mem_univ (rows k)))
  simp only [signedResidualTime, worst]
  gcongr
  exact Finset.le_sup (f := fun i => columnProgramTime U i (rows k) w 0 H 0) hk

/-- Baseline per class, with the excess residual setup paid only on live classes. -/
noncomputable def signedClassSetup (U : Type) (d T w H classes live : ℕ) :=
  let padding := 4*(d+1)*(d+1)+1
  let kernel := Finset.univ.sup fun r => signedResidualTime U (fun _ : Fin (d+1) => r) w 0 H 0
  classes*(size d+3*T+34+(d+1)*(d+1)*(4*H+4)+padding) + live*(7+kernel-padding)

omit [M8.Machine.Net] in
private theorem cube_le_three_pow (a : ℕ) : a^3 ≤ 3^a := by
  induction a with
  | zero => decide
  | succ a ih =>
    match a with
    | 0 | 1 | 2 => decide
    | n+3 =>
      rw [pow_succ 3]
      apply le_trans _ (Nat.mul_le_mul_right 3 ih)
      ring_nf
      omega

/-- With the binary modulus width, the extra setup for each live class
fits in one record of unit payload. -/
theorem signedClassSetup_volume_le (U : Type) (d : ℕ) :
    ∃ C : ℕ, ∀ T w classes live,
      let H := Nat.size (prime^(w+1))
      signedClassSetup U d T w H classes live ≤
        classes*(size d+3*T+34+(d+1)*(d+1)*(4*H+4)+(4*(d+1)*(d+1)+1)) +
          live*(C*(prime^(w+1))^(d+1)) := by
  obtain ⟨c,hc⟩ := signedResidualTime_setup_le U d
  refine ⟨7+2*c*(Nat.size prime+1)^2, ?_⟩
  intro T w classes live H
  have bits : H ≤ (w+1)*Nat.size prime := by
    apply Nat.size_le.mpr
    rw [Nat.mul_comm, pow_mul]
    exact Nat.pow_lt_pow_left (Nat.size_le.mp (le_refl (Nat.size prime))) (by omega)
  have field : H+1 ≤ (w+1)*(Nat.size prime+1) := by rw [Nat.mul_add, Nat.mul_one]; omega
  have cube : (w+1)^3 ≤ prime^(w+1) := (cube_le_three_pow _).trans
    (Nat.pow_le_pow_left Networks.Shared50ModularControl.prime_odd _)
  have prefixPos : 1 ≤ (prime^(w+1))^d := pow_pos (pow_pos Networks.Shared50ModularControl.prime_prime.pos _) _
  have kernel := Finset.sup_le (s := Finset.univ) (f := fun r =>
    signedResidualTime U (fun _ : Fin (d+1) => r) w 0 H 0) (fun r _ => hc (fun _ => r) w H)
  unfold signedClassSetup
  apply Nat.add_le_add_left
  apply Nat.mul_le_mul_left
  apply (Nat.sub_le _ _).trans
  grw [kernel, field]
  rw [pow_succ (prime^(w+1)) d]
  have factor : w+1+(prime^(w+1))^d ≤ 2*(w+1)*(prime^(w+1))^d := by
    nlinarith [Nat.mul_le_mul_left (w+1) prefixPos]
  grw [factor]
  calc
    _ = 7 + 2*c*(Nat.size prime+1)^2*(prime^(w+1))^d*(w+1)^3 := by ring
    _ ≤ _ := by
      grw [cube]
      have pos := Nat.mul_pos prefixPos (pow_pos Networks.Shared50ModularControl.prime_prime.pos (w+1))
      nlinarith

/-- Across the parent boxes and their lifts, one address coordinate pays the
baseline per class. Only live records pay the full residual setup. -/
theorem signedClassSetup_total_le (U : Type) (d T : ℕ) :
    ∃ baseline residual : ℕ, ∀ w parents lifts classes live,
      parents*(lifts*signedClassSetup U d T w (Nat.size (prime^(w+1))) classes live) ≤
        baseline*(parents*lifts*classes)*prime^(w+1) +
        residual*(parents*lifts*live)*(prime^(w+1))^(d+1) := by
  obtain ⟨c,hc⟩ := signedClassSetup_volume_le U d
  let n := (d+1)*(d+1)
  refine ⟨size d+3*T+34+8*n+(4*n+1), c, ?_⟩
  intro w parents lifts classes live
  let q := prime^(w+1)
  have bits : Nat.size q ≤ q := Nat.size_le.mpr Nat.lt_two_pow_self
  have positive : 1 ≤ q := pow_pos Networks.Shared50ModularControl.prime_prime.pos _
  have base : size d+3*T+34+n*(4*(Nat.size q)+4)+(4*n+1) ≤
      (size d+3*T+34+8*n+(4*n+1))*q := by
    grw [bits]
    obtain ⟨k,hk⟩ := Nat.exists_eq_add_of_le positive
    rw [hk]
    ring_nf
    omega
  have setup := hc T w classes live
  simp only [Nat.mul_assoc 4 (d+1) (d+1)] at setup
  grw [setup]
  change parents*(lifts*(classes*(size d+3*T+34+n*(4*(Nat.size q)+4)+(4*n+1)) +
    live*(c*q^(d+1)))) ≤ _
  grw [base]
  dsimp only [q]
  exact le_of_eq (by ring)

/-- At binary field and payload widths the counter scans charge one address
coordinate per live payload symbol, in addition to the class setup. -/
theorem signedPass_parentSetup_le (U : Type) (d T : ℕ) :
    ∃ baseline residual counter : ℕ, ∀ w W parents lifts classes live,
      let q := prime^(w+1)
      let H := Nat.size q
      parents*(lifts*signedClassSetup U d T w H classes live +
        lifts*live*residualCounterRate U d H*Nat.size W) ≤
        baseline*(parents*lifts*classes)*q + residual*(parents*lifts*live)*q^(d+1) +
          counter*(parents*lifts*live)*q*W := by
  obtain ⟨baseline,residual,setup⟩ := signedClassSetup_total_le U d T
  obtain ⟨c,rate⟩ := residualCounterRate_linear U d
  refine ⟨baseline,residual,2*c, ?_⟩
  intro w W parents lifts classes live q H
  have bits : H ≤ q := Nat.size_le.mpr Nat.lt_two_pow_self
  have positive : 1 ≤ q := pow_pos Networks.Shared50ModularControl.prime_prime.pos _
  have width : H+1 ≤ 2*q := by omega
  rw [Nat.mul_add]
  apply Nat.add_le_add (setup w parents lifts classes live)
  grw [rate H, width, show Nat.size W ≤ W from Nat.size_le.mpr Nat.lt_two_pow_self]
  exact le_of_eq (by ring)

/-- At binary widths, setup and payload-counter scans together take linear
time in the total volume represented by the parent boxes. -/
theorem signedPass_parentSetup_volume_le (U : Type) (d T : ℕ) :
    ∃ C : ℕ, ∀ w W parents lifts classes live, 0 < W → live ≤ classes →
      let q := prime^(w+1)
      let H := Nat.size q
      parents*(lifts*signedClassSetup U d T w H classes live +
        lifts*live*residualCounterRate U d H*Nat.size W) ≤
        C*(parents*lifts*classes)*(q^(d+1)*W) := by
  obtain ⟨b,r,c,cost⟩ := signedPass_parentSetup_le U d T
  refine ⟨b+r+c, ?_⟩
  intro w W parents lifts classes live width count q H
  apply (cost w W parents lifts classes live).trans
  have power : q ≤ q^(d+1) := by
    simpa using Nat.pow_le_pow_right (pow_pos Networks.Shared50ModularControl.prime_prime.pos (w+1))
      (show 1 ≤ d+1 by omega)
  have record : q^(d+1) ≤ q^(d+1)*W := Nat.le_mul_of_pos_right _ width
  change b*(parents*lifts*classes)*q + r*(parents*lifts*live)*q^(d+1) +
    c*(parents*lifts*live)*q*W ≤ _
  calc
    _ ≤ b*(parents*lifts*classes)*(q^(d+1)*W) + r*(parents*lifts*classes)*(q^(d+1)*W) +
        c*(parents*lifts*classes)*q^(d+1)*W := by
      gcongr
      exact power.trans record
    _ = _ := by ring

private theorem classSetup_sum_le (table : Matrix (Fin r) (Fin r) (ZMod prime) →
    Matrix (Fin (d+1)) (Fin (d+1)) (ZMod prime)) (U : Type) (T w H : ℕ) :
    ((LabelSelectors.classes 1 (r*r)).map (classResidualCost table T w 0 H 0 U)).sum ≤
      signedClassSetup U d T w H (prime^(r*r)) (∏ i : Fin r, (prime^r-prime^i.val)) := by
  have bound (xs : List (Fin (r*r) → ZMod prime)) :
      (xs.map (classResidualCost table T w 0 H 0 U)).sum ≤
        signedClassSetup U d T w H xs.length (xs.countP (LabelSelectors.accept r)) := by
    induction xs with
    | nil => simp [signedClassSetup]
    | cons x xs ih =>
      have kernel := residualSetup_le_constant_sup U (classPivots (table (LabelSelectors.matrix r x))) w H
      by_cases zero : (LabelSelectors.matrix r x).det = 0 <;>
        simp [signedClassSetup, classResidualCost, LabelSelectors.accept, zero, Nat.add_mul] at ih ⊢ <;>
        omega
  have length : (LabelSelectors.classes 1 (r*r)).length = prime^(r*r) := by
    simp [LabelSelectors.classes_eq]
  simpa only [length, invertibleClassCount] using bound (LabelSelectors.classes 1 (r*r))

/-- Only invertible classes pay the residual volume charge in the physical pass. -/
theorem signedPassWork_le_setup_add_volume (U : Type) (d : ℕ) :
    ∃ swaps shears : ℕ, ∀ w {r : ℕ} (table : Matrix (Fin r) (Fin r) (ZMod prime) →
      Matrix (Fin (d+1)) (Fin (d+1)) (ZMod prime)) T parents records W H J,
      let xs := LabelSelectors.classes 1 (r*r)
      let live := ∏ i : Fin r, (prime^r - prime^i.val)
      signedPassWork table T parents records w W H J U ≤
        signedPassWork table T parents records w 0 H 0 U +
          parents*(prime^w)^(r*r)*live*residualCounterRate U d H*J +
          (parents*(prime^w)^(r*r)*((xs.map (classVolumeRate table T)).sum + live*(swaps * swapVolumeRate w + shears)) +
            4*records) * ((prime^(w+1))^(d+1)*W) := by
  obtain ⟨swaps, shears, kernel⟩ := signedResidualTime_le_setup_add_width_volume U d
  refine ⟨swaps, shears, ?_⟩
  intro w r table T parents records W H J xs live
  let V := (prime^(w+1))^(d+1)*W
  have classes (ys : List (Fin (r*r) → ZMod prime)) :
      (ys.map (classResidualCost table T w W H J U)).sum ≤
        (ys.map (classResidualCost table T w 0 H 0 U)).sum +
        (ys.countP fun x => decide ((LabelSelectors.matrix r x).det ≠ 0)) * ((swaps * swapVolumeRate w + shears) * V +
          residualCounterRate U d H * J) := by
    induction ys with
    | nil => simp
    | cons x ys ih =>
      have h := kernel (classPivots (table (LabelSelectors.matrix r x))) w W H J
      have counter := residualCounterRate_spec U d H
        (classPivots (table (LabelSelectors.matrix r x))) w 0 J
      by_cases zero : (LabelSelectors.matrix r x).det = 0
      all_goals
        simp [classResidualCost, zero, Nat.add_mul] at *
        dsimp [V] at *
        omega
  unfold signedPassWork
  dsimp only [xs, live, V] at *
  rw [← invertibleClassCount]
  unfold LabelSelectors.accept
  simp only [Nat.mul_zero, Nat.zero_mul, Nat.zero_add, Nat.add_zero]
  grw [classes]
  exact le_of_eq (by ring)

omit [M8.Machine.Net] in
private theorem collectPassCost (parents traversal lifts volume : ℕ) (xs : List α) (anchor scan : α → ℕ) :
    (1+(parents*traversal+4 + (parents*lifts*(xs.map anchor).sum+2) + (2*volume+2))) +
      (2*(parents*traversal+4) + (1+(parents*lifts*(xs.map scan).sum+2+(2*volume+2)))) =
    3*parents*traversal + parents*lifts*(xs.map fun x => anchor x + scan x).sum + 4*volume+22 := by
  rw [List.sum_map_add]
  ring

omit [M8.Machine.Net] in
theorem liveRecordCost_le_width_budget (r d w H numTime detTime : ℕ) :
    liveRecordCost r d w H 0 (numTime*(H+1)^2) (detTime*(H+1)^2) ≤
      liveRecordCost r d 1 1 0 numTime detTime * (w+1)*(H+1)^2 := by
  unfold liveRecordCost
  ring_nf
  omega

noncomputable def matrixBuildCost (r d w H : ℕ) := liveRecordCost r d w H 0
  (Finset.univ.sup fun ij : Fin r × Fin r => RingFormula.time H (readTime H)
    (numerator (matrixInput false) (matrixInput true) ij.1 ij.2))
  (RingFormula.time H (readTime H) (determinant (matrixInput (m := r) false)))

omit [M8.Machine.Net] in
theorem matrixBuildCost_le (r d w H : ℕ) :
    matrixBuildCost r d w H ≤ matrixBuildCost r d 1 1 * (w+1)*(H+1)^2 := by
  let num := fun h (ij : Fin r × Fin r) => RingFormula.time h (readTime h)
    (numerator (matrixInput false) (matrixInput true) ij.1 ij.2)
  have entries : Finset.univ.sup (num H) ≤ Finset.univ.sup (num 1)*(H+1)^2 := by
    apply Finset.sup_le
    intro ij hi
    exact (time_readTime_le _ H).trans (Nat.mul_le_mul_right _ (Finset.le_sup (f := num 1) hi))
  apply le_trans _ (liveRecordCost_le_width_budget r d w H _ _)
  simp only [matrixBuildCost, liveRecordCost]
  gcongr
  all_goals first | exact entries | exact time_readTime_le _ H

omit [M8.Machine.Net] in
theorem matrixBuildCost_volume_le (v : Descriptor) (positive : v.Positive)
    (r d w live : ℕ) (fits : w+1 ≤ v.width) (count : live ≤ LabelMask.records v) :
    let H := Nat.size (prime^(w+1))
    prime^v.width * (live * (matrixBuildCost r d 1 1 * (w+1)*(H+1)^2)) ≤
      matrixBuildCost r d 1 1 * (Nat.size prime+1)^2 * volume prime v := by
  intro H
  have power : (w+1)^3 ≤ prime^v.width :=
    (cube_le_three_pow _).trans ((Nat.pow_le_pow_left Networks.Shared50ModularControl.prime_odd _).trans
      (Nat.pow_le_pow_right Networks.Shared50ModularControl.prime_prime.pos fits))
  have bits := (queueArchive_binaryWidth v positive d (w+1) (by omega) fits).2.1
  have field : H+1 ≤ (w+1)*(Nat.size prime+1) := by
    change H ≤ _ at bits
    rw [Nat.mul_add, Nat.mul_one]
    omega
  grw [field, count]
  unfold LabelMask.records volume
  calc
    _ = matrixBuildCost r d 1 1 * (Nat.size prime+1)^2 *
      (v.beforeRows*v.rows*v.beforeH*prime^v.width*1*(w+1)^3*1) := by ring
    _ ≤ _ := by
      have middle := positive.2.2.2.1
      have suffix := positive.2.2.2.2
      gcongr <;> omega

omit [M8.Machine.Net] in
/-- Matrix generation and archive copies over all parent boxes share one
volume budget. The descriptor shape fixes both multiplicities. -/
theorem physicalQueueSetup_volume_le (v : Descriptor) (positive : v.Positive)
    (r d w B : ℕ) (shape : v.beforeH = B*prime^(r*((w+1)*r))) (fits : w+1 ≤ v.width) :
    let H := Nat.size (prime^(w+1))
    let parents := v.beforeRows*v.rows*B
    let lifts := (prime^w)^(r*r)
    let units := ∏ i : Fin r, (prime^r-prime^i.val)
    let build := matrixBuildCost r d 1 1 * (w+1)*(H+1)^2
    prime^v.width * (parents * (lifts*(units*build + prime^(r*r)*(10*(d*d*H)+6)))) ≤
      (matrixBuildCost r d 1 1 * (Nat.size prime+1)^2 + (10*(d*d)+6))*volume prime v := by
  intro H parents lifts units build
  have records : LabelMask.records v = parents*(prime^(r*r)*lifts) := by
    simp only [LabelMask.records, shape, parents, lifts, ← pow_mul, ← pow_add]
    ring_nf
  have unitsLe : units ≤ prime^(r*r) := by
    calc
      _ ≤ ∏ _ : Fin r, prime^r := Finset.prod_le_prod fun i _ => Nat.sub_le _ _
      _ = _ := by simp [← pow_mul]
  have live : parents*(units*lifts) ≤ LabelMask.records v := by
    rw [records]
    gcongr
  have matrix := matrixBuildCost_volume_le v positive r d w _ fits live
  have archive := (queueArchive_binaryWidth v positive d (w+1) (by omega) fits).2.2
  change _ * (parents*(units*lifts)*build) ≤ _ at matrix
  change _ * (LabelMask.records v*(10*(d*d*H)+6)) ≤ _ at archive
  rw [records] at archive
  convert Nat.add_le_add matrix archive using 1 <;> ring

/-- Cost of preparing the directory, generating the matrix archive, and initializing padding. -/
noncomputable def passPreparationCost (v : Descriptor) (r d w B width H : ℕ) :=
  let parents := v.beforeRows*v.rows*B
  let units := ∏ i : Fin r, (prime^r-prime^i.val)
  let lifts := (prime^w)^(r*r)
  let build := matrixBuildCost r d 1 1 * (w+1)*(H+1)^2
  parents*(lifts*(units*build + prime^(r*r)*(10*(d*d*H)+6))) +
    directorySetupCost r (w+1) width parents (LabelMask.records v)
      (parents*(units*lifts)) ((prime^(w+1))^(r*r)) + paddingSetupCost d H

omit [M8.Machine.Net] in
theorem passPreparationCost_volume_le (v : Descriptor) (positive : v.Positive)
    (r d w B width : ℕ) (rankPos : 0 < r) (shape : v.beforeH = B*prime^(r*((w+1)*r)))
    (fits : r*(w+1) ≤ v.width) (hw : width ≤ prime^v.width) :
    prime^v.width * passPreparationCost v r d w B width (Nat.size (prime^(w+1))) ≤
      (matrixBuildCost r d 1 1*(Nat.size prime+1)^2 + (10*(d*d)+6) +
        (16*r*r+19*r+344) + paddingSetupCost d 1)*volume prime v := by
  have atom := (Nat.le_mul_of_pos_left (w+1) rankPos).trans fits
  have queue := physicalQueueSetup_volume_le v positive r d w B shape atom
  have dir := physicalDirectorySetupCost_le_volume v positive r w B width shape fits hw
  have pad := paddingSetupCost_volume_le v positive d (w+1) atom
  simpa only [passPreparationCost, Nat.mul_add, Nat.add_mul] using
    Nat.add_le_add (Nat.add_le_add queue dir) pad

/-- Time budget of the generated program with its supplied field and payload counters. -/
noncomputable def signedPassTime (U : Type) (r d T : ℕ) (v : Descriptor)
    (w W H J B width rate : ℕ) : ℕ :=
  let parents := v.beforeRows*v.rows*B
  let units := ∏ i : Fin r, (prime^r-prime^i.val)
  let classes := prime^(r*r)
  let lifts := (prime^w)^(r*r)
  let perParent := lifts*signedClassSetup U d T w H classes units +
    lifts*units*residualCounterRate U d H*J
  let recordVolume := (prime^(w+1))^(d+1)*W
  let total := LabelMask.records v*recordVolume
  let live := parents*(units*lifts)*recordVolume
  parents*perParent + passPreparationCost v r (d+1) w B width H +
    (anchorVolumeRate d T+4)*total + (6+rate)*min live (((prime-1)*total)/prime)

/-- Specialization to the binary counters and spectator payload of a descriptor. -/
noncomputable def generatedSignedPassCost (U : Type) (r d T : ℕ) (v : Descriptor)
    (w suffix B width rate : ℕ) : ℕ :=
  let W := prime^(2*suffix)*v.between*v.afterD
  let H := Nat.size (prime^(w+1))
  signedPassTime U r d T v w W H (Nat.size W) B width rate

/-- In descriptor units the complete binary-width pass budget consists of a
linear term and the residual rate on the invertible fraction of the volume. -/
theorem generatedSignedPass_cost_le (U : Type) (r d T : ℕ)
    (e : (Fin r ⊕ Fin r) ≃ Fin (d+1)) :
    ∃ C : ℕ, ∀ (v : Descriptor) w suffix B width rate, v.Positive →
      v.width = r*(w+1)+suffix → v.beforeH = B*prime^(r*((w+1)*r)) → width ≤ prime^v.width →
      generatedSignedPassCost U r d T v w suffix B width rate ≤
        C*volume prime v + (6+rate)*(((prime-1)*volume prime v)/prime) := by
  obtain ⟨c,hc⟩ := signedPass_parentSetup_volume_le U d T
  let prep := matrixBuildCost r (d+1) 1 1*(Nat.size prime+1)^2 + (10*((d+1)*(d+1))+6) +
    (16*r*r+19*r+344) + paddingSetupCost (d+1) 1
  refine ⟨c+prep+(anchorVolumeRate d T+4), ?_⟩
  intro v w suffix B width rate positive splitWidth shape hw
  unfold generatedSignedPassCost signedPassTime
  extract_lets W H parents units classes lifts perParent recordVolume total live
  have rankPos : 0 < r := by
    have dim := Fintype.card_congr e
    simp only [Fintype.card_sum, Fintype.card_fin] at dim
    omega
  have volumeEq : total = volume prime v := signedPassVolume_eq_descriptor v e w suffix splitWidth
  have records : parents*lifts*classes = LabelMask.records v := by
    simp only [LabelMask.records, shape, parents, classes, lifts, ← pow_mul]
    ring_nf
  have unitsLe : units ≤ classes := by
    calc
      _ ≤ ∏ _ : Fin r, prime^r := Finset.prod_le_prod fun i _ => Nat.sub_le _ _
      _ = _ := by simp [classes, ← pow_mul]
  have widthPos : 0 < W := Nat.mul_pos (Nat.mul_pos (pow_pos Networks.Shared50ModularControl.prime_prime.pos _)
    positive.2.2.2.1) positive.2.2.2.2
  have parent := hc w W parents lifts classes units widthPos unitsLe
  change parents*perParent ≤ c*(parents*lifts*classes)*recordVolume at parent
  rw [records, Nat.mul_assoc c] at parent
  change parents*perParent ≤ c*total at parent
  rw [volumeEq] at parent
  have preparation := passPreparationCost_volume_le v positive r (d+1) w B width rankPos shape (by omega) hw
  have cheap := Nat.le_mul_of_pos_left (passPreparationCost v r (d+1) w B width H)
    (pow_pos Networks.Shared50ModularControl.prime_prime.pos v.width)
  have setup : passPreparationCost v r (d+1) w B width H ≤ prep*volume prime v := cheap.trans preparation
  rw [volumeEq]
  grw [parent, setup, min_le_right]
  exact le_of_eq (by ring)

/-- At quotient atom width the full budget retains both the invertible density
and the rank divisor on its width-dependent swap term. -/
theorem generatedSignedPass_quotient_cost_le (U : Type) (r d T : ℕ)
    (e : (Fin r ⊕ Fin r) ≃ Fin (d+1)) :
    ∃ C : ℕ, ∀ (v : Descriptor) B width swaps shears, v.Positive → r ≤ v.width →
      let w := v.width/r-1
      let V := volume prime v
      v.beforeH = B*prime^(r*((w+1)*r)) → width ≤ prime^v.width →
      (generatedSignedPassCost U r d T v w (v.width%r) B width
        (swaps*swapVolumeRate w+shears) : ℝ) ≤
        C*(V : ℝ) + (6 + ((swaps : ℝ)*((3808275 + M8.RevMachine.LeafCore.C) *
          ((v.width : ℝ)^M8.Machine.BudgetBound.tau / (r : ℝ)^M8.Machine.BudgetBound.tau)) + shears)) *
          (((prime-1 : ℕ) : ℝ)/prime*V) := by
  obtain ⟨C,bound⟩ := generatedSignedPass_cost_le U r d T e
  refine ⟨C, ?_⟩
  intro v B width swaps shears positive fits w V shape hw
  have dim := Fintype.card_congr e
  simp only [Fintype.card_sum, Fintype.card_fin] at dim
  have rankPos : 0 < r := by omega
  have atom : w+1 = v.width/r := Nat.sub_add_cancel (Nat.div_pos fits rankPos)
  have splitWidth : v.width = r*(w+1)+v.width%r := by rw [atom, Nat.div_add_mod]
  have cost := bound v w (v.width%r) B width (swaps*swapVolumeRate w+shears) positive splitWidth shape hw
  have residual := signedPassResidualCharge_le v.width r swaps shears (((prime-1)*V)/prime) V rankPos fits
  rw [min_self] at residual
  exact (Nat.cast_le.mpr cost).trans (by push_cast; exact add_le_add le_rfl (by simpa [w] using residual))

omit [M8.Machine.Net] in
theorem liveRecordCost_width (r d w H width numTime detTime : ℕ) :
    liveRecordCost r d w H width numTime detTime =
      liveRecordCost r d w H 0 numTime detTime + 12*r*r*width := by
  unfold liveRecordCost
  ring

def SignedPassBound (regs : Fin 6 ↪ Fin T) (anchor : Fin (size d+T) ↪ Fin K)
    (ports : Fin (N+2) ↪ Fin K) (ext : Fin 6 ↪ Fin K) (v : Descriptor) (B : ℕ)
    (a : ScanData r d w W) (payload : ℕ → Record.Array d 1 (w+1) W)
    (rs : List (Pair (size d+T))) (parents saved : Fin (size d+T))
    (body : P → Pr P K Q prime U)
    (setup pass : Pr P K Q prime U) (cost : ℕ) (u : HS K Q prime U)
    (source initial : Stacks K prime) : Prop :=
    v.beforeH = B*prime^(r*((w+1)*r)) →
      a.records = LabelMask.records v → 0 < W →
      let D := embStk anchor initial
      Ready d 1 (w+1) W D → ready (prime^w) D.R rs → D.R saved = [] →
      (D.R parents).length = v.beforeRows*v.rows*B →
      (D.R (port d regs 0)).length = ActualAffineScaling.modulus (w+1)^((d+1)*1)*W →
      a.signed = (List.range a.records).map payload →
      (∀ i ∈ ([2,3,4,5] : List (Fin 6)), D.R (port d regs i) = []) →
      ScanReady a ports ext 0 (preparedPivots a (ports (Fin.last N).castSucc)
        {initial with R := Function.update initial.R (ports (archivePorts 0 (columnBank 34))) (a.matrices 0)}) →
      M < 2^a.H → W < 2^a.J → a.outputTail = [] → initial.R (ext 0) = [] →
      (∀ j < a.records, Record.scalarArray (payload j) = SparseRoleCircuit.encode ∘ a.input j) →
      (∀ j < a.records, LabelStock.live r (w+1) 1 j = false →
      ∃ symbol, Record.scalarArray (payload j) = fun _ => symbol) →
    let output := (List.range a.records).flatMap (outputRecord (LabelStock.live r (w+1) 1) a.matrix a.input)
    ∃ (z : HS K Q prime U) (F : Stacks K prime) (n : ℕ), z.user = u.user ∧ F.R (ext 2) = output ++ a.inputTail ∧ F.R (ext 5) = [] ∧
      F.R (ext 0) = [] ∧ F.R (ports (Fin.last N).castSucc) = a.pivotTail ∧
      F.R (ports (archivePorts 0 (columnBank 34))) = a.matrixTail ∧
      n ≤ cost ∧
      Exec body (.seq setup pass) (mk u source) n (mk z F)

structure SeededQueueReady (w H : ℕ) (proj : Matrix (Fin r) (Fin r) ℚ)
    (α α' : Fin r → ZMod M) (initial S : Stacks K prime) (bank : Fin 18 ↪ Fin K)
    (recip : Fin 16 ↪ Fin K) (pool : Fin ((conjugationDepth r+1)*13) ↪ Fin K)
    (coeff : Fin r → Fin r → Fin 4 ↪ Fin K) (clock count seed tmp archive : Fin K)
    : Prop where
  seedBlank : initial.R seed = []
  tmpBlank : S.R tmp = []
  weightBank : S.R (recip 13) = [] ∧ ∀ i j, let s := coeff i j
      S.R (s 1) = binSyms H (α i).val ∧ S.R (s 2) = binSyms H (α' j).val
  ready :
      (∀ i : Fin 18, i ∈ [0,3,4,5,6,7,11,14,15] → S.R (bank i) = []) ∧ (S.R (bank 8)).length = H ∧
      S.R (bank 10) = [] ∧
       (S.R clock).length = w ∧ S.R count = [] ∧ S.R (recip 14) = [] ∧
      S.R (recip 15) = binSyms H (1 : ZMod (prime^(w+1))).val ∧ S.R (recip 4) = binSyms H (prime^(w+1)) ∧
      (∀ i : Fin 16, i ≠ 4 → i < 13 → S.R (recip i) = []) ∧
      (∀ k ≤ conjugationDepth r, S.R (frame pool k 2) = binSyms H (prime^(w+1))) ∧
      (∀ k ≤ conjugationDepth r, ∀ i : Fin 13, i ≠ 2 → S.R (frame pool k i) = []) ∧
      (∃ suffix, S.R (bank 16) = matrixWords prime H (IntegerMultBounds.Swap.Modular.reduce M proj) ++ suffix)
  empty : S.R (archive) = []
  output : S.R (bank 13) = []

theorem generatedSignedResidualPass (regs : Fin 6 ↪ Fin T) (anchor : Fin (size d+T) ↪ Fin K)
    (ports : Fin (N+2) ↪ Fin K) (ext : Fin 6 ↪ Fin K) (off : ∀ i k, ports i ≠ ext k)
    (banks : ∀ i k, anchor i ≠ ports k) (external : ∀ i k, k ≠ 2 → anchor i ≠ ext k)
    (shared : anchor (port d regs 1) = ext 2)
    (capacity : (anchorProgram d true).1+(anchorProgram d false).1+1 ≤ Q)
    (e : (Fin r ⊕ Fin r) ≃ Fin (d+1)) (proj : Matrix (Fin r) (Fin r) ℚ)
    (idempotent : proj*proj = proj) (admissible : IntegerMultBounds.Swap.Modular.Admissible prime proj)
    (α α' : Fin r → ZMod M) (inverse : ∀ i, α i * α' i = 1)
    (body : P → Pr P K Q prime U) (rs : List (Pair (size d+T))) (hk : rs.length = r*r)
    (parents saved : Fin (size d+T)) (layout : (parents :: saved :: (slots rs ++ [port d regs 4])).Nodup)
    (cap : columnCapacity ≤ Q) (cs : List (Pair K)) (sizeC : cs.length = r*r) (parentsC savedC : Fin K)
    (maskRegs : (parentsC :: savedC :: (slots cs ++ [ext 0])).Nodup)
    (pivotRegs : (parentsC :: savedC :: (slots cs ++ [ports (Fin.last N).castSucc])).Nodup)
    (separate : ∀ k ∈ parentsC :: savedC :: slots cs, ∀ i, anchor i ≠ k) :
    let swaps := (signedPassWork_le_setup_add_volume U d).choose
    let shears := (signedPassWork_le_setup_add_volume U d).choose_spec.choose
    let rate := swaps * swapVolumeRate w + shears
    ∃ pass, ∀ (placement : Fin ((36+2*r+1+(conjugationDepth r+1)*13)+3) ↪ Fin K),
    let size := 36+2*r+1+(conjugationDepth r+1)*13
    let archiveSlot : Fin (size+3) := ⟨36+2*r, by dsimp [size]; omega⟩
    let registers := placement.trans (Equiv.swap (placement archiveSlot)
      (ports (archivePorts 0 (columnBank 34)))).toEmbedding
    let host := QueueLayout.block (n := size) 0 (by dsimp [size]; omega) registers
    let control := QueueLayout.block (n := 3) size (Nat.le_refl _) registers
    let mask := control 0
    let seed := control 1
    let tmp := control 2
    let bank := QueueLayout.block (n := 18) 0 (by omega) host
    let recip := QueueLayout.block (n := 16) 18 (by omega) host
    let counters := QueueLayout.block (n := 2) 34 (by omega) host
    let clock := counters 0
    let count := counters 1
    let pool := QueueLayout.block (n := (conjugationDepth r+1)*13) (36+2*r+1) (by omega) host
    let coeff := fun i j : Fin r => (coefficientSlots i j).trans host
    let archive := host ⟨36+2*r, by omega⟩
    have archiveOff : ∀ i, bank (QueueLayout.directoryWork i) ≠ archive := fun i h => by
      have eq := congrArg Fin.val (host.injective h)
      change 0 + i.val = 36+2*r at eq
      omega
    have coeffOff : ∀ i j k l, recip k ≠ coeff i j l := fun i j k l h => by
      have eq := congrArg Fin.val (host.injective h)
      change 18+k.val = (coefficientSlots (extra := (conjugationDepth r+1)*13) i j l).val at eq
      fin_cases l <;> simp [coefficientSlots, Matrix.cons_val] at eq <;> (try split_ifs at *) <;> omega
    ∀ (maskLayout : (parentsC :: savedC :: (slots cs ++ [mask])).Nodup),
    (∀ k ∈ parentsC :: savedC :: slots cs, k ≠ bank 2 ∧ k ≠ archive) →
    (∀ i, anchor i ≠ bank 2) → (∀ i, ports i ≠ bank 2) → (∀ i, ext i ≠ bank 2) →
    ∃ writeMask : Pr P K Q prime U, ∀ (directoryPorts : Fin 15 ↪ Fin K), directoryPorts 14 = bank 2 →
    let dir := directoryPorts.trans (Equiv.swap (directoryPorts 9) parentsC).toEmbedding
    dir 1 = bank 12 → dir 1 ∉ slots cs →
    let atom := bank 1
    ∀ (one : Fin K), (∀ i, atom ≠ dir i) → (∀ i, one ≠ dir i) →
    [one,atom,dir 7,dir 2,dir 3,dir 5].Nodup → (dir 7 :: dir 2 :: slots cs).Nodup →
    ∀ (br rows bh : Fin K), [br,rows,bh,atom,dir 2,dir 9,dir 3,dir 5].Nodup → ∀ (word : ℕ → List (Fin (prime+4))) (parentTail : List (Fin (prime+4)))
      (v : Descriptor) (B : ℕ) (base : ScanData r d w W) (payload : ℕ → Record.Array d 1 (w+1) W)
      (u : HS K Q prime U) (raw : Stacks K prime),
    v.Positive → (raw.R br).length = v.beforeRows → (raw.R rows).length = v.rows →
    (raw.R bh).length = v.beforeH → raw.R (dir 9) = [] →
    let source := {raw with R := Function.update raw.R (dir 9) (List.replicate (v.beforeRows*v.rows*B) tick)}
    let n := (source.R (dir 9)).length
    let box := M^(r*r)
    let width := (source.R (dir 1)).length
    let digits := (w+1)*(r*r)
    let ancestor := fun k => word (k/box)
    let tail := source.R (dir 14)
    let entries := (List.range (n*box)).flatMap (LabelDirectory.entry ancestor r (w+1))
    let counted := Function.update (LabelDirectorySetup.prepared source.R dir digits) (dir 12)
      (expandedMask box (fun _ => false) (source.R (dir 9)))
    let builtState := {source with R := Function.update (Function.update counted (dir 0) parentTail) (dir 14) (entries ++ tail)}
    let input := {builtState with R := LabelCountBank.fill (cs.map Prod.fst) (prime^w) (Function.update builtState.R (dir 7) (List.replicate (prime^w) tick))}
    source.R atom = List.replicate (w+1) tick → (source.R one).length = 1 →
    source.R (dir 0) = (List.range n).flatMap word ++ parentTail → (∀ j < n, (word j).length = width) →
    (∀ i ∈ ([2,3,4,5,6,7,10,11,12,13] : List (Fin 15)), source.R (dir i) = []) →

    (∀ k ∈ slots cs, builtState.R k = []) → input.R savedC = [] →
    input.R mask = [] →
    let bits := (LabelMask.selectors r (w+1) base.records).map (bitSymbol (a := prime))
    let selected := {input with R := Function.update input.R mask bits}
    selected.R (bank 17) = [] →
    let unitWord := binSyms base.H (1 : ZMod M).val
    let masked := {selected with R := Function.update selected.R (bank 17) unitWord}
    masked.R (bank 9) = [] →
    let initial := {masked with R := Function.update masked.R (bank 9) (binSyms base.H 0)}
    let padWord := matrixWords prime base.H (1 : Matrix (Fin (d+1)) (Fin (d+1)) (ZMod M))
    let S := {initial with R := Function.update initial.R seed padWord}
    SeededQueueReady w base.H proj α α' initial S bank recip pool coeff clock count
      seed tmp archive →
    let scan := QueueLayout.scanPorts (QueueLayout.directoryWork.trans bank) archive archiveOff
    let generate : Pr P K Q prime U := seededQueueBody r d e bank recip clock count pool coeff coeffOff scan mask seed tmp
    let a := base.physical e proj α α'
    SignedPassBound regs anchor ports ext v B a payload rs parents saved body
      (.seq (LabelSpectators.program r br rows bh atom (dir 2) (dir 9) (dir 3) (dir 5)) (.seq (.seq (LabelDirectorySetup.setup r dir atom one) (.seq (expandMask (dir 9) (dir 4) (dir 2) (dir 3) (dir 5) (dir 12) (fun _ => false)) (LabelDirectoryBuild.program dir))) (.seq (.seq (LabelCounts.highCount one atom (dir 7) (dir 2) (dir 3) (dir 5))
        (scanR (dir 7) (dir 2) (LabelCountBank.pushAll (cs.map Prod.fst)))) (.seq writeMask (.seq (.seq (bcopy (recip 15) (bank 17) (bank 4) tmp) (.seq (.seq (umulSym 1 (bitSymbol false) (bank 8) (bank 9) (bank 4)) (withIdentitySeed (d+1) (bank 9) (bank 17) seed (bank 4) tmp generate)) (bclear (bank 9)))) (bclear (bank 17))))))) pass
      (signedPassTime U r d T v w W a.H a.J B width rate) u raw input := by
  intro swaps shears rate
  obtain ⟨pass,run⟩ := physicalSignedResidualPass (w := w) (W := W) regs anchor ports ext off banks external shared
    capacity e proj idempotent admissible α α' inverse body rs hk parents saved layout cap cs sizeC
    parentsC savedC maskRegs pivotRegs separate
  refine ⟨pass,?_⟩
  intro placement size archiveSlot registers host control mask seed tmp bank recip counters clock count pool coeff archive archiveOff
    coeffOff maskLayout retained anchorDirectory portDirectory extDirectory
  obtain ⟨writeMask,write⟩ := record_writes (body := body) r cs sizeC mask parentsC savedC maskLayout
  refine ⟨writeMask,?_⟩
  intro directoryPorts directorySlot dir parentWidthPort parentWidthOff atom one atomOff oneOff highLayout highSlots br rows bh dimensions word parentTail v B base payload u raw positiveDescriptor beforeRows rowsSize beforeH parentBlank source n box parentWidth digits ancestor tail entries counted builtState input atomWord oneWidth parentsWord wordWidth scratch counterEmpty savedBlank maskBlank bits selected oneBlank unitWord masked zeroBlank initial padWord S queueInputs scan generate a shape records hW D
    neutral radix free count width unsigned clean start hm hw fresh maskEmpty encoded padding
  let units := ∏ i : Fin r, (prime^r-prime^i.val)
  let classes := prime^(r*r)
  let lifts := (prime^w)^(r*r)
  let perParent := lifts*signedClassSetup U d T w a.H classes units +
      lifts*units*residualCounterRate U d a.H*a.J
  let recordVolume := M^(d+1)*W
  let totalVolume := LabelMask.records v*recordVolume
  let liveVolume := (v.beforeRows*v.rows*B)*(units*lifts)*recordVolume
  let liveBase := matrixBuildCost r (d+1) 1 1 * (w+1)*(base.H+1)^2
  let queuePerParent := lifts * (units*liveBase + classes*(10*((d+1)*(d+1)*base.H)+6))
  let fixedCost := paddingSetupCost (d+1) base.H
  let active := LabelStock.live r (w+1) 1
  obtain ⟨seedBlank,tmpBlank,weightBank,queueReady,empty,output⟩ := queueInputs
  have blank := queueReady.1 4 (by decide)
  have sharedArchive : archive = ports (archivePorts 0 (columnBank 34)) := by
    change Equiv.swap (placement archiveSlot) _ (placement _) = _
    have slot : (⟨0+(36+2*r), by dsimp [size]; omega⟩ : Fin (size+3)) = archiveSlot :=
      Fin.ext (Nat.zero_add _)
    exact (congrArg (fun k => Equiv.swap (placement archiveSlot) _ (placement k)) slot).trans
      (Equiv.swap_apply_left ..)
  have apart (i j) : host i ≠ control j := QueueLayout.block_ne _ _ registers (by omega) i j
  have copyPorts (k : Fin 18) (hk : k ≠ 4) : [bank k,seed,bank 4,tmp].Nodup := by
    simp [seed,tmp,bank.injective.eq_iff,control.injective.eq_iff,hk,
      show bank k ≠ control 1 from apart _ _,show bank k ≠ control 2 from apart _ _,
      show control 1 ≠ bank 4 from (apart _ _).symm,show bank 4 ≠ control 2 from apart _ _]
  have bankKeep (k : Fin 18) : S.R (bank k) = initial.R (bank k) :=
    Function.update_of_ne (apart _ 1) _ _
  have tmpKeep : S.R tmp = initial.R tmp := Function.update_of_ne (control.injective.ne (by decide : (2 : Fin 3) ≠ 1)) _ _
  have parentPort : dir 9 = parentsC := Equiv.swap_apply_left ..
  have dirSlot : dir 14 = bank 2 := by
    change Equiv.swap (directoryPorts 9) parentsC (directoryPorts 14) = _
    rw [Equiv.swap_apply_of_ne_of_ne (directoryPorts.injective.ne (by decide : (14 : Fin 15) ≠ 9))
      (directorySlot ▸ (retained parentsC (by simp)).1.symm),directorySlot]
  have parentSize : n = v.beforeRows*v.rows*B := by simp [n,source]
  have fillKeep (i : Fin 15) (hi : i ≠ 7) (off : dir i ∉ slots cs) : input.R (dir i) = builtState.R (dir i) := by
    have outside : dir i ∉ cs.map Prod.fst := by
      intro mem
      obtain ⟨pair,hp,eq⟩ := List.mem_map.mp mem
      exact off (eq ▸ List.mem_flatMap.mpr ⟨pair,hp,by simp⟩)
    simp [input,LabelCountBank.fill,outside,hi]
  have parentOff : dir 9 ∉ slots cs := by
    rw [parentPort]
    intro h
    exact maskLayout.notMem (by simp [h])
  have directoryOff : dir 14 ∉ slots cs := by
    intro h
    exact (retained _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h))).1 dirSlot
  have atomWidth : (source.R atom).length = w+1 := by simp [atomWord]
  have parentCount : (input.R parentsC).length = v.beforeRows*v.rows*B := by
    rw [← parentPort,fillKeep 9 (by decide) parentOff]
    simpa [builtState,counted,LabelDirectorySetup.prepared,n] using parentSize
  have rankPos : 0 < r := by
    obtain i | i := e.symm 0 <;> exact Nat.zero_lt_of_lt i.isLt
  have positive : 0 < digits := Nat.mul_pos (Nat.succ_pos _) (Nat.mul_pos rankPos rankPos)
  change base.records = LabelMask.records v at records
  have recordCount : base.records = n*box := by
    rw [records,LabelMask.records,shape,parentSize]
    dsimp only [box]
    rw [← pow_mul]
    rw [show r*((w+1)*r) = (w+1)*(r*r) by ring]
    simp only [Nat.mul_assoc]
  have rawWidth : (raw.R atom).length = w+1 := by simpa [source,atomOff] using atomWidth
  obtain ⟨parentsUser,parentSteps,parentUser,parentCost,parentRun⟩ := LabelSpectators.runs body r rankPos
    br rows bh atom (dir 2) (dir 9) (dir 3) (dir 5) dimensions v positiveDescriptor (w+1) B shape
    u raw beforeRows rowsSize beforeH rawWidth (by
      intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl
      · simpa [source] using scratch 2 (by decide)
      · exact parentBlank
      · simpa [source] using scratch 3 (by decide)
      · simpa [source] using scratch 5 (by decide))
  have build := LabelDirectorySetup.build_from_parents (body := body) r dir atom one atomOff oneOff
    parentsUser source word parentTail oneWidth scratch
  simp only [atomWidth,pow_mul prime (w+1) (r*r)] at build
  obtain ⟨built,buildSteps,buildUser,buildCost,buildRun⟩ := build positive parentsWord wordWidth
  let dirCost := base.records*(15*digits+14*parentWidth+45) + n*(6*parentWidth+25) + 22*box + 8*(w+1)+32
  have directoryCost : buildSteps ≤ dirCost := by
    apply buildCost.trans
    change 8*(w+1)+8+22*box + (n*(6*box+10)+6 + (n*box*(9*digits+15)+6 +
      (n*(box*(8*parentWidth+11)+6*parentWidth+15)+6+n*box*(6*(parentWidth+digits)+13)+6))) ≤ _
    unfold dirCost
    rw [recordCount]
    exact Nat.le_of_eq (by ring)
  obtain ⟨counterReady,initialized,counterSteps,counterUser,counterCost,counterRun⟩ :=
    LabelCountBank.prepare_exec body cs one atom (dir 7) (dir 2) (dir 3) (dir 5) highLayout highSlots
      built builtState (w+1) (by omega) (by simpa [builtState,counted,LabelDirectorySetup.prepared,atomOff] using atomWord)
      (by simpa [builtState,counted,LabelDirectorySetup.prepared,oneOff] using oneWidth) (by
        intro k hk
        rcases List.mem_append.mp hk with h | h
        · simp only [List.mem_cons,List.not_mem_nil,or_false] at h
          rcases h with rfl | rfl | rfl | rfl <;> simp [builtState,counted,LabelDirectorySetup.prepared,scratch]
        · exact counterEmpty _ h)
  change ready (prime^w) input.R cs at counterReady
  have bankMasked (k : Fin 18) (hk : k ≠ 9) : S.R (bank k) = masked.R (bank k) :=
    (bankKeep k).trans (Function.update_of_ne (bank.injective.ne hk) _ _)
  have bankInput (k : Fin 18) (hk : k ≠ 9) (h17 : k ≠ 17) : S.R (bank k) = input.R (bank k) :=
    (bankMasked k hk).trans ((Function.update_of_ne (bank.injective.ne h17) _ _).trans (Function.update_of_ne (show bank k ≠ mask from apart _ 0) _ _))
  have parentWidthEq : (S.R (bank 12)).length = parentWidth := by
    rw [bankInput 12 (by decide) (by decide),← parentWidthPort,fillKeep 1 (by decide) parentWidthOff]
    simp [builtState,counted,LabelDirectorySetup.prepared,parentWidth]
  have retainedAtom : builtState.R atom = List.replicate (w+1) tick := by
    simpa [builtState,counted,LabelDirectorySetup.prepared,atomOff] using atomWord
  have atomOutside : atom ∉ cs.map Prod.fst := by
    intro mem
    obtain ⟨pair,hp,eq⟩ := List.mem_map.mp mem
    have emptyAtom := counterEmpty atom (eq ▸ List.mem_flatMap.mpr ⟨pair,hp,by simp⟩)
    rw [retainedAtom] at emptyAtom
    simp at emptyAtom
  have width0 : (S.R (bank 1)).length = w+1 := by
    rw [bankInput 1 (by decide) (by decide)]
    change (input.R atom).length = _
    simp [input,LabelCountBank.fill,atomOutside,atomOff,retainedAtom]
  have widths (j) (hj : j < base.records) : (S.R (bank 12)).length = (ancestor j).length := by
    have boxPos : 0 < box := pow_pos (pow_pos Networks.Shared50ModularControl.prime_prime.pos _) _
    rw [recordCount] at hj
    exact parentWidthEq.trans (wordWidth _ ((Nat.div_lt_iff_lt_mul boxPos).2 hj)).symm
  have directory : S.R (bank 2) = (List.range base.records).flatMap (LabelDirectory.entry ancestor r (w+1)) ++ tail := by
    rw [bankInput 2 (by decide) (by decide),recordCount,← dirSlot,fillKeep 14 (by decide) directoryOff]
    exact Function.update_self ..
  obtain ⟨writer,tMask,hUser,hTime,emit⟩ := write v (w+1) B (by omega) shape initialized input
    ⟨counterReady,savedBlank,parentCount⟩
  change base.records = LabelMask.records v at records
  rw [← records,maskBlank,List.append_nil] at emit
  have maskBits : S.R mask = (List.range base.records).map fun j => bitSymbol (LabelStock.live r (w+1) 1 j) := by
    change Function.update initial.R seed padWord mask = _
    rw [Function.update_of_ne (control.injective.ne (by decide : (0 : Fin 3) ≠ 1))]
    rw [show initial.R mask = masked.R mask from Function.update_of_ne (apart _ 0).symm _ _]
    rw [show masked.R mask = selected.R mask from Function.update_of_ne (apart _ 0).symm _ _]
    change Function.update input.R mask bits mask = _
    rw [Function.update_self]
    simp [bits,LabelMask.selectors,List.map_map,Function.comp_def]
  have zeroWord : S.R (bank 9) = binSyms base.H 0 := (bankKeep 9).trans (Function.update_self ..)
  have widthWord := (congrArg List.length (bankMasked 8 (by decide))).symm.trans queueReady.2.1
  have separateBank (i j) : bank i ≠ recip j := QueueLayout.block_ne _ _ host (by decide) i j
  have unitValue := queueReady.2.2.2.2.2.2.1
  have oneSource : selected.R (recip 15) = unitWord := by
    simpa only [S,initial,masked,Function.update_of_ne (show recip 15 ≠ seed from apart _ 1),
      Function.update_of_ne (separateBank 9 15).symm,Function.update_of_ne (separateBank 17 15).symm] using unitValue
  have unitLen : unitWord.length = base.H := by simp [unitWord,binSyms]
  have unitDest : S.R (bank 17) = unitWord :=
    (bankMasked 17 (by decide)).trans (Function.update_self ..)
  have tmpSource : selected.R tmp = [] := by
    simpa only [S,initial,masked,Function.update_of_ne (show tmp ≠ seed from control.injective.ne (by decide : (2 : Fin 3) ≠ 1)),
      Function.update_of_ne (show tmp ≠ bank 9 from (apart _ 2).symm),
      Function.update_of_ne (show tmp ≠ bank 17 from (apart _ 2).symm)] using tmpBlank
  obtain ⟨copied,copyUser,copyRun⟩ := bcopy_exec (body := body)
    (a := recip 15) (c := bank 17) (t₁ := bank 4) (t₂ := tmp) (by
      simp [tmp,show recip 15 ≠ bank 17 from (separateBank _ _).symm,
        show recip 15 ≠ bank 4 from (separateBank _ _).symm,show recip 15 ≠ control 2 from apart _ _,
        show bank 17 ≠ control 2 from apart _ _,show bank 4 ≠ control 2 from apart _ _])
    writer selected (by
      have h := (bankMasked 4 (by decide)).symm.trans blank
      simpa [masked] using h) tmpSource
  rw [oneSource,oneBlank,List.append_nil,unitLen] at copyRun
  obtain ⟨withZero,zeroUser,zeroRun⟩ := umulSym_exec body 1 (bitSymbol false)
    (a := bank 8) (b := bank 9) (t := bank 4) (by simp) (by simp) (by simp) copied masked
    ((bankMasked 4 (by decide)).symm.trans blank)
  have zeroCode : (binSyms base.H 0 : List (Fin (prime+4))) = List.replicate base.H (bitSymbol false) := by
    simp [binSyms,List.ofFn_const]
  rw [widthWord,Nat.one_mul,zeroBlank,List.append_nil,← zeroCode] at zeroRun
  obtain ⟨prepared,steps,preparedUser,initCost,initRun⟩ := identitySeed_writes («M» := M) body
    (d+1) base.H (bank 9) (bank 17) seed (bank 4) tmp (copyPorts 9 (by decide))
    (copyPorts 17 (by decide)) withZero initial ⟨(bankKeep 9).symm.trans zeroWord,
      (bankKeep 17).symm.trans unitDest,
      (bankKeep 4).symm.trans blank,tmpKeep.symm.trans tmpBlank⟩
  rw [seedBlank,List.append_nil] at initRun
  have seedWord : S.R seed = padWord := Function.update_self ..
  obtain ⟨_,y,t,hy,ht,generateRun⟩ := physicalResidualQueue_exec body w base.records
    (IntegerMultBounds.Swap.Modular.reduce M proj) base.H hm registers ancestor tail e α α' prepared S
    seedWord tmpBlank weightBank ⟨queueReady.1,queueReady.2.1,zeroWord,by
      obtain ⟨_,_,p,c,t,h,o,m,f,ms,fs,pr⟩ := queueReady
      exact ⟨p,c,t,h,o,m,f,ms,fs,pr,unitDest⟩⟩ widths width0 blank empty directory output maskBits
  have boxCount (select : Bool → Bool) : (List.range base.records).countP (fun j => select (active j)) =
      n*(List.range box).countP (fun j => select (active j)) := by
    rw [recordCount]
    exact LabelStock.count_boxes r (w+1) n select
  have liveCount := boxCount id
  have paddingCount := boxCount Bool.not
  change (List.range base.records).countP active = n*(List.range box).countP active at liveCount
  have cardinality : (List.range box).countP active = units*lifts := by
    simpa only [units,lifts,liveClasses_eq_product] using
      (liveLabelCount (m := r) (by omega : 0 < w+1)).trans (LabelPadding.unit_count w)
  have partition := List.length_eq_countP_add_countP active (l := List.range box)
  simp only [List.length_range,decide_not,Bool.decide_eq_true] at partition
  have boxSize : box = classes*lifts := by
    dsimp only [box,classes,lifts]
    rw [pow_succ',mul_pow]
  have rankPos : 0 < r := by
    have dim := Fintype.card_congr e
    simp only [Fintype.card_sum, Fintype.card_fin] at dim
    omega
  have density := liveClassVolume_le r (n*lifts*recordVolume) rankPos
  rw [liveClasses_eq_product] at density
  have liveBound : liveVolume ≤ ((prime-1)*totalVolume)/prime := by
    apply (Nat.le_div_iff_mul_le IntegerMultBounds.Networks.Shared50ModularControl.prime_prime.pos).2
    dsimp only [liveVolume, totalVolume]
    rw [← records, recordCount, ← parentSize, boxSize]
    dsimp only [units, classes]
    convert density using 1 <;> ring
  have remaining : (List.range box).countP (fun j => !active j) = (classes-units)*lifts := by
    rw [Nat.sub_mul,← boxSize,← cardinality]
    omega
  let setupCost := n*(queuePerParent + classes*lifts*(4+(r*r*(4*(w+1)+4)+1)+6) + parentWidth*lifts*(12*r*r*units+4*classes))+4
  have unitsLe : units ≤ classes := by
    dsimp only [units, classes]
    calc
      _ ≤ ∏ _ : Fin r, prime^r := Finset.prod_le_prod fun i _ => Nat.sub_le _ _
      _ = _ := by simp [← pow_mul]
  have generateCost : t ≤ setupCost := by
    apply ht.trans
    change (List.range base.records).countP active * _ +
      (List.range base.records).countP (fun j => !active j) * _ + base.records * _ + 4 ≤ _
    rw [liveCount,paddingCount,cardinality,remaining,recordCount,boxSize]
    rw [parentWidthEq,liveRecordCost_width r (d+1) w base.H parentWidth]
    dsimp only [setupCost,queuePerParent,liveBase]
    have archive := queueArchive_le classes units ((d+1)*(d+1)*base.H) (matrixBuildCost r (d+1) w base.H) unitsLe
    have archive := archive.trans (Nat.add_le_add_right (Nat.mul_le_mul_left units
      (matrixBuildCost_le r (d+1) w base.H)) _)
    unfold matrixBuildCost at archive
    apply le_trans _ (Nat.add_le_add_right (Nat.mul_le_mul_left n
      (Nat.add_le_add_right (Nat.add_le_add_right (Nat.mul_le_mul_left lifts archive) _) _)) 4)
    exact le_of_eq (by ring)
  let words := (List.range base.records).flatMap fun j => if active j then matrixWords prime base.H
    (projectorResidual e (IntegerMultBounds.Swap.Modular.reduce M proj) α α' (physicalLabel r (w+1) j)) else padWord
  change Exec body generate (mk prepared S) t (mk y (queueResult S mask (scan 2) archive tail words)) at generateRun
  have archiveEq : words = a.matrices 0 := (base.physical_archive e proj α α').symm
  rw [archiveEq] at generateRun
  obtain ⟨cleaned,cleanUser,clearRun⟩ := clearQueueSeed_exec body seed mask (scan 2) archive
    (control.injective.ne (by decide : (1 : Fin 3) ≠ 0)) (apart _ 1).symm (apart _ 1).symm
    padWord tail (a.matrices 0) y initial seedBlank
  let G := queueResult input mask (scan 2) archive tail (a.matrices 0)
  obtain ⟨released,releaseUser,releaseRun⟩ := clearQueueSeed_exec body (bank 9) mask (scan 2) archive
    (apart _ 0) (bank.injective.ne (by decide : (9 : Fin 18) ≠ 2)) (archiveOff 9)
    (binSyms base.H 0) tail (a.matrices 0) cleaned masked zeroBlank
  obtain ⟨finished,finishUser,finishRun⟩ := clearQueueSeed_exec body (bank 17) mask (scan 2) archive
    (apart _ 0) (bank.injective.ne (by decide : (17 : Fin 18) ≠ 2)) (by
      intro eq
      have bad := congrArg Fin.val (host.injective eq)
      change 0+17 = 36+2*r at bad
      omega)
    unitWord tail (a.matrices 0) released selected oneBlank
  have restored : queueResult selected mask (scan 2) archive tail (a.matrices 0) = G := by
    simp only [G,selected,queueResult,Function.update_idem]
  rw [restored,unitLen] at finishRun
  rw [show (binSyms base.H 0 : List (Fin (prime+4))).length = base.H by simp [zeroCode]] at releaseRun
  have padLen : padWord.length = (d+1)*(d+1)*base.H := length_matrixWords ..
  have installed : G.R archive = a.matrices 0 := Function.update_self ..
  have prep : Function.update G.R archive (a.matrices 0) = G.R := by rw [← installed,Function.update_eq_self]
  have outside (k : Fin K) (dirOff : k ≠ bank 2) (archiveOff : k ≠ archive) : G.R k = input.R k := by
    change Function.update (Function.update (Function.update input.R mask [])
      (scan 2) tail) archive (a.matrices 0) k = _
    change k ≠ scan 2 at dirOff
    rw [Function.update_of_ne archiveOff,Function.update_of_ne dirOff,
      ← maskBlank,Function.update_eq_self]
  have kept (k : Fin K) (hk : k ∈ parentsC :: savedC :: slots cs) : G.R k = input.R k :=
    outside k (retained k hk).1 (retained k hk).2
  have anchorState : embStk anchor G = D := by
    have tapes : G.R ∘ anchor = input.R ∘ anchor := funext fun i =>
      outside _ (anchorDirectory i) (sharedArchive ▸ banks i _)
    unfold embStk
    dsimp only [D,embStk]
    rw [tapes]
    rfl
  rw [← anchorState] at neutral radix free count width clean
  have radixC : ready (prime^w) G.R cs := by
    intro pair member
    have left : pair.1 ∈ slots cs := List.mem_flatMap.mpr ⟨pair,member,by simp⟩
    have right : pair.2 ∈ slots cs := List.mem_flatMap.mpr ⟨pair,member,by simp⟩
    simpa only [kept pair.1 (by simp [left]),kept pair.2 (by simp [right])] using
      counterReady pair member
  have freeC := (kept savedC (by simp)).trans savedBlank
  have countC := (congrArg List.length (kept parentsC (by simp))).trans parentCount
  let installedInput := {input with R := Function.update input.R archive (a.matrices 0)}
  rw [← sharedArchive] at start
  change ScanReady a ports ext 0 (preparedPivots a _ installedInput) at start
  have internal (i) : G.R (ports i) = installedInput.R (ports i) := by
    by_cases h : ports i = archive
    · simpa only [h,installedInput,Function.update_self] using installed
    · simpa only [installedInput,Function.update_of_ne h] using outside _ (portDirectory i) h
  have bankState : embStk ports G = embStk ports installedInput := by
    unfold embStk
    congr 1
    exact funext internal
  have extArchive (i) : ext i ≠ archive := sharedArchive ▸ (off _ i).symm
  have extState (i) : G.R (ext i) = installedInput.R (ext i) := by
    simpa only [installedInput,Function.update_of_ne (extArchive i)] using outside _ (extDirectory i) (extArchive i)
  have queueInput := start.queue
  simp only [preparedPivots,Function.update_of_ne (off _ 2).symm,List.drop_zero] at queueInput
  have scanStart := start.signedHandoff a ports ext off installedInput G a.signed bankState
    (fun i _ => extState i) ((extState 2).trans queueInput)
  have emptyMask := (outside _ (extDirectory 0) (extArchive 0)).trans maskEmpty
  obtain ⟨z,E,passSteps,hz,queue,acc,maskDone,pivots,archiveDone,hn,exec⟩ :=
    run v B base payload finished G shape records hW neutral radix free count width unsigned clean
      (sharedArchive ▸ installed.trans (base.physical_archive e proj α α')) (by
        change ScanReady a ports ext 0 (preparedPivots a _ {G with R := Function.update G.R (ports (archivePorts 0 (columnBank 34))) (a.matrices 0)})
        rw [← sharedArchive,prep]
        exact scanStart)
      hm hw fresh emptyMask radixC freeC countC encoded padding
  have anchorCost : (((signedInputs a.table (w+1) a.records payload).map
      (fun x => Record.cost d T 1 (w+1) W x.1 + 2)).sum) =
      (v.beforeRows*v.rows*B)*(prime^w)^(r*r)*((LabelSelectors.classes 1 (r*r)).map (anchorClassCost a.table T w W)).sum := by
    have countEq : a.records = LabelMask.records v := records
    simpa only [signedInputs,List.map_map,Function.comp_def,countEq,LabelSelectors.residue_eq,
      LabelSelectors.recordMap,anchorClassCost] using LabelSelectors.recordMap_sum v r w B shape (anchorClassCost a.table T w W)
  have scanCost : ((List.range a.records).map fun j => a.recordTime U j + 4).sum =
      (v.beforeRows*v.rows*B)*(prime^w)^(r*r)*((LabelSelectors.classes 1 (r*r)).map (scanClassCost a.table w W a.H a.J U)).sum := by
    have countEq : a.records = LabelMask.records v := records
    simpa only [countEq,ScanData.recordTime,ScanData.pivots,LabelStock.live,decide_eq_true_eq,
      LabelSelectors.residue_eq,LabelSelectors.recordMap,scanClassCost] using
      LabelSelectors.recordMap_sum v r w B shape (scanClassCost a.table w W a.H a.J U)
  rw [anchorCost,scanCost] at hn
  have passCost : passSteps ≤ signedPassWork a.table T (v.beforeRows*v.rows*B) a.records w W a.H a.J U + 22 := by
    apply hn.trans_eq
    simpa only [signedPassWork,splitClassCost,ActualAffineScaling.modulus,Nat.mul_one,Nat.mul_assoc] using
      collectPassCost (v.beforeRows*v.rows*B) (LabelTraversal.time (prime^w) (r*r) 1+5)
        ((prime^w)^(r*r)) (a.records*(M^(d+1)*W)) (LabelSelectors.classes 1 (r*r))
        (anchorClassCost a.table T w W) (scanClassCost a.table w W a.H a.J U)
  have queueCost := Nat.add_le_add (Nat.add_le_add initCost generateCost)
    (Nat.le_of_eq (congrArg (fun n => 2*n+2) padLen))
  have paid := Nat.add_le_add_right (Nat.add_le_add_left
    (Nat.add_le_add_right (Nat.add_le_add_left queueCost (4*base.H+4)) (2*base.H+2))
    (6*base.H+6)) (2*base.H+2)
  rw [paddingSetupCost_eq] at paid
  have volumeBound := (signedPassWork_le_setup_add_volume U d).choose_spec.choose_spec w a.table T
    (v.beforeRows*v.rows*B) a.records W a.H a.J
  change signedPassWork _ _ _ _ _ _ _ _ _ ≤ signedPassWork _ _ _ _ _ 0 _ 0 _ +
    (v.beforeRows*v.rows*B)*lifts*units*residualCounterRate U d a.H*a.J +
    ((v.beforeRows*v.rows*B)*lifts*(((LabelSelectors.classes 1 (r*r)).map
      (classVolumeRate a.table T)).sum + units*rate) + 4*a.records)*(M^(d+1)*W) at volumeBound
  have movement := classVolumeRate_sum_le a.table T
  change _ ≤ classes*anchorVolumeRate d T + units*6 at movement
  grw [movement] at volumeBound
  have setup := classSetup_sum_le a.table U T w a.H
  change _ ≤ signedClassSetup U d T w a.H classes units at setup
  unfold signedPassWork at volumeBound
  simp only [Nat.mul_zero, Nat.zero_mul, Nat.zero_add, Nat.add_zero] at volumeBound
  grw [setup] at volumeBound
  have passBound := passCost.trans (Nat.add_le_add_right volumeBound 22)
  have total := Nat.add_le_add (Nat.add_le_add parentCost (Nat.add_le_add directoryCost
    (Nat.add_le_add counterCost (Nat.add_le_add hTime paid)))) passBound
  refine ⟨z,E,_,hz.trans (finishUser.trans (releaseUser.trans (cleanUser.trans (hy.trans (preparedUser.trans (zeroUser.trans (copyUser.trans (hUser.trans (counterUser.trans (buildUser.trans parentUser)))))))))),queue,acc,maskDone,pivots,archiveDone,?_,
    Exec.seq (Exec.seq parentRun (Exec.seq buildRun (Exec.seq counterRun (Exec.seq emit (Exec.seq (Exec.seq copyRun (Exec.seq (Exec.seq zeroRun (Exec.seq (Exec.seq initRun generateRun) clearRun)) releaseRun)) finishRun))))) exec⟩
  change _ ≤ (v.beforeRows*v.rows*B)*perParent + passPreparationCost v r (d+1) w B parentWidth base.H +
    (anchorVolumeRate d T+4)*totalVolume + (6+rate)*min liveVolume (((prime-1)*totalVolume)/prime)
  rw [min_eq_left liveBound]
  have traversal : LabelTraversal.time (prime^w) (r*r) 1 + 5 ≤ 11*box := by
    have bound := LabelTraversal.time_add_ten_le (pow_pos IntegerMultBounds.Networks.Shared50ModularControl.prime_prime.pos w) (r*r) 1
    change _ ≤ 11*(prime^(w+1))^(r*r)
    rw [pow_succ]
    omega
  have fixed := fixedBoxCost_le r w rankPos
  change 22*box + 21*(w+1) + 26*prime^w + 82 ≤ 151*box at fixed
  rw [show passPreparationCost v r (d+1) w B parentWidth base.H =
    (v.beforeRows*v.rows*B)*queuePerParent + directorySetupCost r (w+1) parentWidth
      (v.beforeRows*v.rows*B) (LabelMask.records v) ((v.beforeRows*v.rows*B)*(units*lifts)) box +
      fixedCost from rfl]
  unfold directorySetupCost
  rw [show ∀ x y f : ℕ, x + (y + 151*box) + f = (x+y) + (151*box+f) by intros; ring]
  rw [← Nat.add_assoc (_*perParent) _ (151*box+fixedCost)]
  apply le_trans _ (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_left
    (Nat.add_le_add_right fixed (paddingSetupCost (d+1) base.H)) _) _) _)
  apply total.trans
  dsimp only [dirCost,setupCost,digits,inheritedLabelCost,perParent,recordVolume,totalVolume,liveVolume,fixedCost,signedPassWork,Nat.add_one_sub_one]
  grw [traversal]
  change a.records = LabelMask.records v at records
  rw [← records,show a.records = n*box from recordCount,recordCount,← parentSize,boxSize]
  exact le_of_eq (by ring)

end IntegerMultBounds.MathlibTM2.Cover.Fallback
