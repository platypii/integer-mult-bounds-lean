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

/-- At any exponent the integer leaf bill is bounded by the corresponding
rank moment times the parent's width power and full volume. -/
theorem scheduledLeafMoment (node : Descriptor) (width : 64 ∣ node.width) (rows : 142080 ∣ node.rows)
    (rate exponent : ℝ) (nonneg : 0 ≤ rate) :
    (((∑ i : Fin nodeChildren5.length, let child := scheduledChild prime node i
      ⌊(rate*(child.width : ℝ)^exponent)*volume prime child⌋₊) : ℕ) : ℝ) ≤
      (rate*(node.width : ℝ)^exponent*volume prime node) *
        (Layer.SelectedMoments.histMoment fiveHistogram 64 exponent / 142080) := by
  let scale := rate*(node.width : ℝ)^exponent*volume prime node
  rw [Nat.cast_sum,← Layer.SelectedMoments.occurrence_moment_eq nodeChildren5_realizes,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  let child := scheduledChild prime node i
  obtain ⟨cw,cv⟩ := scheduledChild_measures prime node width rows i
  have w : (child.width : ℝ) = ((nodeChildren5[i.val] : ℝ)/64)*node.width := by
    have eq : (child.width : ℝ)*64 = nodeChildren5[i.val]*(node.width : ℝ) := by exact_mod_cast cw
    linarith
  have v : (volume prime child : ℝ)*142080 = volume prime node := by exact_mod_cast cv
  change _ ≤ scale * _
  calc
    _ ≤ (rate*(child.width : ℝ)^exponent)*volume prime child := Nat.floor_le (by positivity)
    _ = _ := by
      dsimp only [scale]
      rw [w,Real.mul_rpow (by positivity) (Nat.cast_nonneg _),← v]
      ring

/-- A mixed level obeys the same rank moment when the induction hypothesis
pays for each active child. Dispatch adds three steps per occurrence. -/
theorem scheduledMixedMoment (node : Descriptor) (width : 64 ∣ node.width) (rows : 142080 ∣ node.rows)
    (cutoff : ℕ) (rate exponent : ℝ) (nonneg : 0 ≤ rate) (recursiveTime : Fin nodeChildren5.length → ℕ) :
    let child := scheduledChild prime node
    let budget := fun i => ⌊(rate*((child i).width : ℝ)^exponent)*volume prime (child i)⌋₊
    (∀ i, cutoff < (child i).width → recursiveTime i ≤ budget i) →
    (((∑ i, ((if cutoff < (child i).width then recursiveTime i else budget i) + 3)) : ℕ) : ℝ) ≤
      (rate*(node.width : ℝ)^exponent*volume prime node) *
        (Layer.SelectedMoments.histMoment fiveHistogram 64 exponent / 142080) + nodeChildren5.length * 3 := by
  intro child budget paid
  have bound : (∑ i, if cutoff < (child i).width then recursiveTime i else budget i) ≤ ∑ i, budget i := by
    apply Finset.sum_le_sum
    intro i _
    split
    next h => exact paid i h
    next => exact le_rfl
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
  exact add_le_add ((Nat.cast_le.mpr bound).trans (scheduledLeafMoment node width rows rate exponent nonneg)) le_rfl

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
