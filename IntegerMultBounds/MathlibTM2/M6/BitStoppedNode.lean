module

public import IntegerMultBounds.MathlibTM2.M6.BitFlatSweepHandoff
public import IntegerMultBounds.MathlibTM2.M6.BitStoppedSweep

/-! Complete PR589 node execution at the last recursive level. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host M8.RevMachine
open Certificates.PR589 RecursiveInterchangeLayout
open Shared50ModularControl (prime)

/-- Group the physical child charges by rank, retaining integer rounding
inside each occurrence. Every scheduled child has one role's volume. -/
theorem scheduledRankBill (node : Descriptor) (w : ℕ) (width : node.width = 64*w)
    (rows : 142080 ∣ node.rows) (price : ℕ → ℕ → ℕ) :
    (∑ i : Fin nodeChildren5.length, let child := scheduledChild prime node i
      price child.width (volume prime child)) =
      (fiveHistogram.map fun e => e.2 * price (e.1*w) (volume prime node / 142080)).sum := by
  let charge := fun r => price (r*w) (volume prime node / 142080)
  calc
    _ = ∑ i : Fin nodeChildren5.length, charge nodeChildren5[i.val] := by
      apply Finset.sum_congr rfl
      intro i _
      obtain ⟨_,vol⟩ := scheduledChild_measures prime node ⟨w,width⟩ rows i
      have childWidth : (scheduledChild prime node i).width = nodeChildren5[i.val]*w := by
        change _*(node.width/64) = _
        rw [width,Nat.mul_div_cancel_left _ (by decide)]
      dsimp only [charge]
      rw [childWidth,← vol,Nat.mul_div_cancel _ (by decide)]
    _ = (nodeChildren5.map charge).sum := Fin.sum_univ_fun_getElem nodeChildren5 charge
    _ = _ := by
      rw [(nodeChildren5_realizes.map charge).sum_eq,Layer.SelectedMoments.sum_map_expand]
      simp [charge]

/-- Sum a width power over the actual occurrence volumes before rounding. -/
theorem scheduledPowerMoment (node : Descriptor) (width : 64 ∣ node.width) (rows : 142080 ∣ node.rows)
    (rate exponent : ℝ) :
    (∑ i : Fin nodeChildren5.length, let child := scheduledChild prime node i
      (rate*(child.width : ℝ)^exponent)*volume prime child) =
      (rate*(node.width : ℝ)^exponent*volume prime node) *
        (Layer.SelectedMoments.histMoment fiveHistogram 64 exponent / 142080) := by
  let scale := rate*(node.width : ℝ)^exponent*volume prime node
  rw [← Layer.SelectedMoments.occurrence_moment_eq nodeChildren5_realizes,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  let child := scheduledChild prime node i
  obtain ⟨cw,cv⟩ := scheduledChild_measures prime node width rows i
  have w : (child.width : ℝ) = ((nodeChildren5[i.val] : ℝ)/64)*node.width := by
    have eq : (child.width : ℝ)*64 = nodeChildren5[i.val]*(node.width : ℝ) := by exact_mod_cast cw
    linarith
  have v : (volume prime child : ℝ)*142080 = volume prime node := by exact_mod_cast cv
  dsimp only [scale]
  change (rate*(child.width : ℝ)^exponent)*volume prime child = _
  rw [w,Real.mul_rpow (by positivity) (Nat.cast_nonneg _),← v]
  ring

/-- At any exponent the integer leaf bill is bounded by the corresponding
rank moment times the parent's width power and full volume. -/
theorem scheduledLeafMoment (node : Descriptor) (width : 64 ∣ node.width) (rows : 142080 ∣ node.rows)
    (rate exponent : ℝ) (nonneg : 0 ≤ rate) :
    (((∑ i : Fin nodeChildren5.length, let child := scheduledChild prime node i
      ⌊(rate*(child.width : ℝ)^exponent)*volume prime child⌋₊) : ℕ) : ℝ) ≤
      (rate*(node.width : ℝ)^exponent*volume prime node) *
        (Layer.SelectedMoments.histMoment fiveHistogram 64 exponent / 142080) := by
  rw [← scheduledPowerMoment node width rows rate exponent,Nat.cast_sum]
  apply Finset.sum_le_sum
  intro i _
  exact Nat.floor_le (by positivity)

/-- A mixed level obeys the same rank moment when the induction hypothesis
pays for each active child. Each occurrence charges its own local work per unit of child volume. -/
theorem scheduledMixedMoment (node : Descriptor) (width : 64 ∣ node.width) (rows : 142080 ∣ node.rows)
    (cutoff : ℕ) (rate exponent : ℝ) (nonneg : 0 ≤ rate) (recursiveTime overhead : Fin nodeChildren5.length → ℕ) :
    let child := scheduledChild prime node
    let budget := fun i => ⌊(rate*((child i).width : ℝ)^exponent)*volume prime (child i)⌋₊
    (∀ i, cutoff < (child i).width → recursiveTime i ≤ budget i) →
    (((∑ i, ((if cutoff < (child i).width then recursiveTime i else budget i) + overhead i * volume prime (child i))) : ℕ) : ℝ) ≤
      (rate*(node.width : ℝ)^exponent*volume prime node) *
        (Layer.SelectedMoments.histMoment fiveHistogram 64 exponent / 142080) +
      ((∑ i, overhead i : ℕ) : ℝ) * (volume prime node / 142080 : ℝ) := by
  intro child budget paid
  have bound : (∑ i, if cutoff < (child i).width then recursiveTime i else budget i) ≤ ∑ i, budget i := by
    apply Finset.sum_le_sum
    intro i _
    split
    next h => exact paid i h
    next => exact le_rfl
  rw [Finset.sum_add_distrib]
  rw [Nat.cast_add]
  apply add_le_add ((Nat.cast_le.mpr bound).trans (scheduledLeafMoment node width rows rate exponent nonneg))
  apply le_of_eq
  rw [Nat.cast_sum,Nat.cast_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  have measure := (scheduledChild_measures prime node width rows i).2
  have size : (volume prime (child i) : ℝ)*142080 = volume prime node := by exact_mod_cast measure
  rw [Nat.cast_mul,← size]
  ring

/-- The stopped branch of the physical sweep pays its leaf exponent, while
active children carry the selected bit exponent and cutoff factor. The certified
rank sum leaves at least one part in 2^24 of the parent bill for local work. -/
theorem scheduledCutoffMoment [M8.Machine.Net] (node : Descriptor) (w cutoff : ℕ)
    (width : node.width = 64*(w+1)) (rows : 142080 ∣ node.rows) (rate : ℝ) (hr : 0 ≤ rate)
    (time : Fin nodeChildren5.length → ℕ) (localWork : ℝ) :
    let a := Layer.SelectedMoments.bitSaving
    let child := scheduledChild prime node
    let scale := rate*(cutoff : ℝ)^a
    let parentBill := (scale*(node.width : ℝ)^(1-a))*volume prime node
    localWork ≤ parentBill / 2^24 →
    (∀ i, cutoff < (child i).width →
      (time i : ℝ) ≤ (scale*((child i).width : ℝ)^(1-a))*volume prime (child i)) →
    localWork + ((∑ i, if cutoff < (child i).width then time i else
      ⌊(rate*((child i).width : ℝ)^M8.Machine.BudgetBound.tau)*volume prime (child i)⌋₊ : ℕ) : ℝ) ≤
      parentBill := by
  intro a child scale parentBill localBound active
  have ha : 0 ≤ a := by norm_num [a,Layer.SelectedMoments.bitSaving]
  have hs : 0 ≤ scale := mul_nonneg hr (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  rw [Nat.cast_sum]
  have childBill : (∑ i : Fin nodeChildren5.length, ((if cutoff < (child i).width then time i else
      ⌊(rate*((child i).width : ℝ)^M8.Machine.BudgetBound.tau)*volume prime (child i)⌋₊ : ℕ) : ℝ)) ≤ ∑ i : Fin nodeChildren5.length, (scale*((child i).width : ℝ)^(1-a))*volume prime (child i) := by
      apply Finset.sum_le_sum
      intro i _
      split
      next h => exact active i h
      next h =>
        have shape : (child i).width = nodeChildren5[i.val]*(w+1) := by
          change _*(node.width/64) = _
          rw [width,Nat.mul_div_cancel_left _ (by decide)]
        have pos : 0 < (child i).width := shape ▸ Nat.mul_pos (nodeChildren5_bounds i).1 (Nat.succ_pos w)
        have one : (1 : ℝ) ≤ (child i).width := by exact_mod_cast pos
        have leaf := Real.rpow_le_rpow_of_exponent_le one M8.Machine.BudgetBound.exponent_range.2.le
        rw [Real.rpow_one] at leaf
        have factor : ((child i).width : ℝ) = ((child i).width : ℝ)^a*((child i).width : ℝ)^(1-a) := by
          rw [← Real.rpow_add (by positivity : (0 : ℝ) < (child i).width), add_sub_cancel,Real.rpow_one]
        have cap := Real.rpow_le_rpow (Nat.cast_nonneg (child i).width) (Nat.cast_le.mpr (Nat.le_of_not_gt h)) ha
        apply (Nat.floor_le (by positivity)).trans
        apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
        dsimp only [scale]
        rw [mul_assoc]
        apply mul_le_mul_of_nonneg_left _ hr
        exact leaf.trans (factor.le.trans (mul_le_mul_of_nonneg_right cap (by positivity)))
  rw [scheduledPowerMoment node ⟨_,width⟩ rows scale (1-a)] at childBill
  have moment : Layer.SelectedMoments.histMoment fiveHistogram 64 (1-a) / 142080 ≤ 1-1/2^24 := by
    rw [histMoment_five]
    have cert := Layer.SelectedMoments.bit_histMoment_le
    dsimp only [a]
    linarith
  have nonneg : 0 ≤ parentBill := by dsimp only [parentBill]; positivity
  change _ ≤ parentBill * _ at childBill
  exact (add_le_add localBound (childBill.trans (mul_le_mul_of_nonneg_left moment nonneg))).trans
    (by apply le_of_eq; ring)

/-- Dividing the physical recursive bill by parent volume gives precisely
the child weights used in the variable-width recurrence. -/
theorem scheduledBillPerVolume (node : Descriptor) (width : 64 ∣ node.width)
    (rows : 142080 ∣ node.rows)
    (time : Fin nodeChildren5.length → ℕ) :
    ((∑ i, time i : ℕ) : ℝ) / volume prime node =
      ∑ i, (1 / (142080 : ℝ)) * ((time i : ℝ) / volume prime (scheduledChild prime node i)) := by
  rw [Nat.cast_sum,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  obtain ⟨_,measure⟩ := scheduledChild_measures prime node width rows i
  have size : (volume prime (scheduledChild prime node i) : ℝ) * 142080 = volume prime node := by
    exact_mod_cast measure
  rw [← size]
  ring_nf

/-- All nine sweeps, idle intervals, and scalar handoffs cost at most a
fixed multiple of the packed stage volume times the leaf width power. -/
theorem alignedLocalCost_bound [M8.Machine.Net] (base nt : ℕ) (rate : Fin 9 → ℝ) :
    ∃ D : ℝ, ∀ m V w : ℕ, 0 < m → V ≤ m → 0 < w →
      let power := (w : ℝ)^M8.Machine.BudgetBound.tau
      let sweep := fun i => ⌊(stageSetupCost base nt m w : ℝ)+rate i*m*power⌋₊+142081*(8*m+10)+1
      let idle := 35520 * (((298*(intervalSplitTapes+5)+5)*142080+142081*8)*V + (142081*10+31)) +
        1 + 142081*(8*m+10)+1
      (((∑ i, sweep i)+9*idle+9*(2*(76*17760*m*(142081+7)+6)+1+(142081*(8*m+10)+1))+2 : ℕ) : ℝ) ≤
        D*m*power := by
  choose C bound using fun i => sweepHandoffCost_bound base nt (rate i)
  let fixed (V m : ℕ) :=
    let idle := 35520 * (((298*(intervalSplitTapes+5)+5)*142080+142081*8)*V + (142081*10+31)) +
      1 + 142081*(8*m+10)+1
    9*idle+9*(2*(76*17760*m*(142081+7)+6)+1+(142081*(8*m+10)+1))+2
  refine ⟨(∑ i, C i)+fixed 1 1,?_⟩
  intro m V w hm hV hw power sweep idle
  have one : 1 ≤ power := Real.one_le_rpow (by exact_mod_cast hw) M8.Machine.BudgetBound.exponent_range.1.le
  have scaled := le_mul_of_one_le_right (Nat.cast_nonneg m (α := ℝ)) one
  have overhead : fixed V m ≤ fixed 1 1*m := by
    dsimp only [fixed,intervalSplitTapes]
    omega
  have paid : ((∑ i, sweep i : ℕ) : ℝ) ≤ (∑ i, C i)*m*power := by
    rw [Nat.cast_sum,Finset.sum_mul,Finset.sum_mul]
    exact Finset.sum_le_sum fun i _ => bound i m w hm hw
  have fixedBound : (fixed V m : ℝ) ≤ (fixed 1 1 : ℝ)*(m*power) :=
    (show (fixed V m : ℝ) ≤ (fixed 1 1 : ℝ)*m by exact_mod_cast overhead).trans
      (mul_le_mul_of_nonneg_left scaled (Nat.cast_nonneg _))
  rw [show (∑ i, sweep i)+9*idle+9*(2*(76*17760*m*(142081+7)+6)+1+(142081*(8*m+10)+1))+2 =
    (∑ i, sweep i)+fixed V m by dsimp only [idle,fixed]; omega, Nat.cast_add]
  linarith only [paid,fixedBound]

/-- Execute an aligned node with every child stopped. Its cost contains
one leaf charge per scheduled occurrence and the nine local stage costs. -/
theorem stoppedAlignedNode [M8.Machine.Net] {U : Type} :
    ∃ (states base nt : ℕ) (rate C : ℝ), ∀ {Q : ℕ}, states ≤ Q →
      ∃ coeff : Fin 9 → StageRun → ℝ, ∀ (node : Descriptor) (h B groups : ℕ),
      node.width = 64*(h+1) → node.rows = 142080*(142080*groups) →
      node.beforeH = B*prime^(64*((h+1)*64)) →
      let w := h+1
      let rows := 142080*groups
      let K := node.beforeRows*rows*node.between*node.afterD
      let W := B*prime^(64*(w*64))*(node.beforeRows*groups*node.between*node.afterD)
      let V := (prime^w)^128*W
      let m := (prime^w)^128*(W*142080)
      0 < B → 0 < K → ({node with rows := rows} : Descriptor).Positive →
      let leafBill := (fiveHistogram.map fun e =>
        e.2 * ⌊(rate*((e.1*w : ℕ) : ℝ)^M8.Machine.BudgetBound.tau)*(volume prime node / 142080 : ℕ)⌋₊).sum
      let sweep := fun i => ⌊(stageSetupCost base nt m w : ℝ)+
        (C+|stagePackingRate i+(stageRuns.map (coeff i)).sum|)*m*(w : ℝ)^M8.Machine.BudgetBound.tau⌋₊+
        142081*(8*m+10)+1
      let idle := 35520 * (((298*(intervalSplitTapes+5)+5)*142080+142081*8)*V + (142081*10+31)) +
        1 + 142081*(8*m+10)+1
      PackedWindowHandoff U Q m (packedChildOutput w m)
        ((∑ i, sweep i)+9*idle+leafBill+9*(2*(76*17760*m*(142081+7)+6)+1+(142081*(8*m+10)+1))+2) := by
  classical
  obtain ⟨C,idleRate,base,nt,nodeStates,_,assemble⟩ := alignedFlatNode (U := U)
  choose states rates stages using stoppedPackedSweep
  obtain ⟨s,hs⟩ := Finite.exists_le states
  obtain ⟨r,hr⟩ := Finite.exists_le rates
  let rate := max r idleRate
  refine ⟨max s nodeStates,base,nt,rate,C,?_⟩
  intro Q cap
  choose coeff build using fun i => stages i (U := U) ((hs i).trans ((le_max_left _ _).trans cap))
  refine ⟨coeff,?_⟩
  intro node h B groups width split label w rows K W V m hB hK positive leafBill sweep idle
  let budget := fun k => let child := scheduledChild prime node k
    ⌊(rate*(child.width : ℝ)^M8.Machine.BudgetBound.tau)*volume prime child⌋₊
  have live : 0 < ((prime^(h+1))^112*B)*prime^(64*((h+1)*64))*K :=
    Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _) hB)
      (pow_pos Shared50ModularControl.prime_prime.pos _)) hK
  choose P tapes body execute using fun i => build i node h B rows width split label live rate
    ((hr i).trans (le_max_left _ _))
  let required := fun (_ : Fin 9) (time : ℕ → ℕ) => ∀ i : Fin nodeChildren5.length, time i.val = budget i
  have run := assemble (cutoff := node.width) ((le_max_right _ _).trans cap) node width split label
    hB hK positive P tapes body coeff required budget rate (le_max_right _ _) execute
    (by intro i j; simp only [Fin.isLt,dite_eq_left,Fin.eta,budget,ite_self]) (by
      intro i j child above same smaller
      exact False.elim ((Nat.not_lt_of_ge (same ▸ smaller.le)) above))
  have costs : (∑ k, budget k) = leafBill := scheduledRankBill node w width ⟨rows,split⟩
    (fun d v => ⌊(rate*(d : ℝ)^M8.Machine.BudgetBound.tau)*v⌋₊)
  rw [← costs]
  simpa only [budget,ite_self,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] using run

end IntegerMultBounds.MathlibTM2.M6.BitNode
