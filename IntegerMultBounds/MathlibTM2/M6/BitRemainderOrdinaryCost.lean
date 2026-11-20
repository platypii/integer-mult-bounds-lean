module

import IntegerMultBounds.MathlibTM2.M6.BitRemainderScan
public import IntegerMultBounds.MathlibTM2.M6.BitRemainderOrdinaryEntry
import IntegerMultBounds.MathlibTM2.Cover.FallbackGoodRecordSetup
import IntegerMultBounds.MathlibTM2.Cover.FallbackGoodCoordinates

/-! Volume charge for generating and executing ordinary PR589 records. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Networks.Shared50ModularControl (prime prime_prime)

/-- The row setup and cursor advance cost one payload-volume factor plus a linear
charge for reading the ancestor prefix. The child budget occurs once. -/
theorem ordinaryRowTime_volume_le (m overhead : ℕ) (active : 0 < m) :
    ∃ rate : ℕ, ∀ r w W prefixWidth budget, r ≤ m → 0 < W →
      let M := prime^(w+1)
      let H := M.size
      ordinaryRowTime m r w W H prefixWidth overhead budget +
        (1+(4*prefixWidth+4+(m*m*(4*(w+1)+4)+1)+1)) ≤
        budget+(12*m*m+4)*prefixWidth+rate*(M^(m+m)*W) := by
  let depth := RingFormula.conjugationDepth m+1
  let scale := 2*(prime.size+1)^2
  let a := matrixBuildCost m 0 1 1 * scale
  let b := pivotSetupTime m m 1 1 * scale
  let c := 2200*(prime+1)*(m+1)^4 * scale
  refine ⟨a+b+c+overhead+depth*16+12*m*m+60,?_⟩
  intro r w W prefixWidth budget hr hW M H
  let V := M^(m+m)*W
  have positive : 0 < M := pow_pos prime_prime.pos _
  have radix : M ≤ V := by
    exact (show M^1 ≤ M^(m+m) from Nat.pow_le_pow_right positive (by omega)).trans'
      (by simp) |>.trans (Nat.le_mul_of_pos_right _ hW)
  have small : H ≤ V := (Nat.size_le.2 Nat.lt_two_pow_self : M.size ≤ M).trans radix
  have one : 1 ≤ V := positive.trans_le radix
  have ticks : w+1 ≤ V := (Nat.le_of_lt (Nat.lt_pow_self prime_prime.one_lt)).trans radix
  have co : recordConjugationTime m w H prefixWidth ≤ 12*m*m*prefixWidth+a*V :=
    (recordConjugationTime_binary_le ..).trans (Nat.add_le_add_left (Nat.mul_le_mul_left a radix) _)
  have piv : pivotSetupTime m r w H ≤ b*V :=
    (pivotSetupTime_radix_le m r m w hr).trans (Nat.mul_le_mul_left b radix)
  let cost := fun i : Fin m =>
    let C := 48*H*H+152*H+66
    (8*(i.val*H)+14*H+22)+(6*w+6+(14*H+16+(prime-2)*C+C+w*(12*H+15+prime*C)))+(2*H+2)+(4*H+4)
  have each (i : Fin m) : cost i ≤ childWeightTime prime w H i.val := by
    dsimp [cost,childWeightTime]; omega
  have sum (xs : List (Fin m)) : (xs.map cost).sum ≤ (xs.map fun i => childWeightTime prime w H i.val).sum := by
    induction xs with
    | nil => exact le_rfl
    | cons i xs ih => exact Nat.add_le_add (each i) ih
  have field := prefixSetup_volume_le w 0
  simp only [Nat.zero_add,pow_one,pow_zero] at field
  have poly : (w+1)*(H+1)^2 ≤ scale*V :=
    ((Nat.mul_le_mul_right _ (Nat.le_add_right (w+1) 1)).trans field).trans (Nat.mul_le_mul_left scale radix)
  have weights : ((List.finRange m).map cost).sum ≤ c*V := by
    have child := goodChildOverhead_le prime w H m 0 0
    simp only [Nat.add_zero,Nat.zero_add] at child
    apply (sum _).trans
    apply le_trans _ (show 2200*(prime+1)*(m+1)^4*((w+1)*(H+1)^2) ≤ c*V by
      dsimp only [c]
      rw [Nat.mul_assoc (2200*(prime+1)*(m+1)^4) scale V]
      exact Nat.mul_le_mul_left _ poly)
    rw [← Nat.mul_assoc]
    omega
  change depth*(6*H+6)+1+((4*H+4)+(recordConjugationTime m w H prefixWidth+(2*H+2))+(depth*(2*H+2)+1))+
    (4*(m*m*H)+4)+pivotSetupTime m r w H+(((List.finRange m).map cost).sum+1+(4*H+4)+(6*H+6))+
    (budget+overhead*V)+(1+(4*prefixWidth+4+(m*m*(4*(w+1)+4)+1)+1)) ≤ _
  grw [co,piv,weights,small,ticks]
  change _ ≤ budget+(12*m*m+4)*prefixWidth+(a+b+c+overhead+depth*16+12*m*m+60)*V
  obtain ⟨extra,eq⟩ := Nat.exists_eq_add_of_le one
  rw [eq]
  ring_nf
  omega

/-- At a stopped child, the cost of clearing the private bank can be absorbed
in the same precision-dependent rate as the child itself. -/
theorem ordinaryStoppedRow_rate (m overhead tapes push : ℕ) (active : 0 < m) (C : ℝ) :
    ∃ rate : ℝ, ∀ r w W prefixWidth budget, r ≤ m → 0 < W →
      let M := prime^(w+1)
      let V := M^(m+m)*W
      let scale := ((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau
      let elapsed := ordinaryRowTime m r w W M.size prefixWidth overhead budget +
        (1+(4*prefixWidth+4+(m*m*(4*(w+1)+4)+1)+1))
      prefixWidth ≤ V → (budget : ℝ) ≤ C*scale*V →
      ((elapsed+(4*tapes+1+tapes*(6*(push*elapsed))) : ℕ) : ℝ) ≤ rate*scale*V := by
  obtain ⟨base,bound⟩ := ordinaryRowTime_volume_le m overhead active
  let factor := 1+tapes*(6*push)
  let toll := 12*m*m+4+base
  refine ⟨(factor : ℝ)*(C+toll)+(4*tapes+1 : ℕ),?_⟩
  intro r w W prefixWidth budget hr hW M V scale elapsed hp child
  have vol : 1 ≤ V := Nat.mul_pos (pow_pos (pow_pos prime_prime.pos _) _) hW
  have scaled : 1 ≤ scale := Real.one_le_rpow (by exact_mod_cast Nat.le_add_left 1 w)
    M8.Machine.BudgetBound.exponent_range.1.le
  have elapsedBound : elapsed ≤ budget+toll*V := by
    apply (bound r w W prefixWidth budget hr hW).trans
    dsimp only [toll]; rw [Nat.add_mul (12*m*m+4) base V]
    exact (Nat.add_le_add_right (Nat.add_le_add_left (Nat.mul_le_mul_left _ hp) _) _).trans_eq (Nat.add_assoc ..)
  have volumeScale : (V : ℝ) ≤ scale*V := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right scaled (Nat.cast_nonneg V)
  have runtime : (elapsed : ℝ) ≤ (C+toll)*scale*V := by
    calc
      _ ≤ (budget : ℝ)+toll*V := by exact_mod_cast elapsedBound
      _ ≤ C*scale*V+toll*(scale*V) := add_le_add child (mul_le_mul_of_nonneg_left volumeScale (Nat.cast_nonneg toll))
      _ = _ := by ring
  have cleanup : elapsed+(4*tapes+1+tapes*(6*(push*elapsed))) = factor*elapsed+(4*tapes+1) := by
    dsimp [factor]; ring
  rw [cleanup,Nat.cast_add,Nat.cast_mul]
  calc
    _ ≤ (factor : ℝ)*((C+toll)*scale*V)+(4*tapes+1 : ℕ)*(scale*V) := by
      apply add_le_add (mul_le_mul_of_nonneg_left runtime (Nat.cast_nonneg factor))
      simpa only [mul_one] using mul_le_mul_of_nonneg_left
        ((show (1 : ℝ) ≤ V by exact_mod_cast vol).trans volumeScale) (Nat.cast_nonneg (4*tapes+1))
    _ = _ := by ring

open IntegerMultBounds.Machine IntegerMultBounds.Networks
open IntegerMultBounds.MathlibTM2.Stack Host Cover M8.RevMachine
open RecursiveInterchangeLayout (Descriptor)
open Matrix Finset IntegerMultBounds.Swap.LowerTriangular IntegerMultBounds.Swap.Modular

/-- Counter, selectors, matrix setup and traversal on the packed owner tape. -/
noncomputable def ordinaryOwnerScanTime (m d r w W H J records N prefixWidth archiveSize suffixSize left
    tapes push rareTapes rareRate preparePush overhead childBudget : ℕ) : ℕ :=
  let V := records*N
  let selector := left+(140+30*(m*m)+6*tapes)*V
  let init := directoryQueueInitRate m d*((1+m*m)*V+archiveSize+suffixSize)
  let queue := (12*m*m+4+directoryMatrixRate m d)*V+4
  let pad := 1+(4*prefixWidth+4+(m*m*(4*(w+1)+4)+1)+1)
  let elapsed := ordinaryRowTime m r w W H prefixWidth overhead childBudget+pad
  let base := elapsed+(4*tapes+1+tapes*(6*(push*elapsed)))+((d+1)*(d+1)*(4*H+4)+1)+4*N
  dimensionTime H J (d+1)+6*N+13*((d+1)*H+J)+8 + (selector + (
    (init+queue+(4*rareTapes+1+rareTapes*(6*(preparePush*init)))) +
    (records*(base+12*N+16)+(((∑ i ∈ range r, (i+1)*(m+1))*records)/prime)*(rareRate*N)+4)))

/-- The parent's directory setup is linear in the packed owner's volume. -/
theorem ordinaryParentSetup_volume_le (layout : Descriptor) (rows : ℕ) (split : layout.rows = 142080*rows) :
    let C := 366+16*64*64+19*64+344
    C*RecursiveInterchangeLayout.volume prime layout/(prime^layout.width*142080) ≤
      C*RecursiveInterchangeLayout.volume prime (RecursiveInterchangeLayout.role layout 142080) := by
  intro C
  have total := RecursiveInterchangeLayout.role_volume_mul prime 142080 layout ⟨rows,split⟩
  rw [← total,← Nat.mul_assoc]
  apply Nat.div_le_of_le_mul
  calc
    _ ≤ _ * (prime^layout.width*142080) := Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ (pow_pos prime_prime.pos _))
    _ = _ := Nat.mul_comm ..

/-- The packed counter and its dimension headers cost a constant per payload
symbol, uniformly in the radix and the spectator volume. -/
theorem ordinaryCounter_volume_le (M W : ℕ) (radix : 0 < M) (positive : 0 < W) :
    let H := M.size
    let J := W.size
    let N := M^128*W
    dimensionTime H J 128+6*N+13*(128*H+J)+8 ≤ 502951*N := by
  intro H J N
  have hM : H ≤ M := Nat.size_le.2 Nat.lt_two_pow_self
  have hW : J ≤ W := Nat.size_le.2 Nat.lt_two_pow_self
  have square := Nat.pow_le_pow_right radix (by decide : 2 ≤ 128)
  have linear := Nat.pow_le_pow_right radix (by decide : 1 ≤ 128)
  rw [pow_one] at linear
  have h : H ≤ N := (hM.trans linear).trans (Nat.le_mul_of_pos_right _ positive)
  have j : J ≤ N := hW.trans (Nat.le_mul_of_pos_left _ (pow_pos radix _))
  have hh : H*H ≤ N := (Nat.mul_le_mul hM hM).trans ((pow_two M ▸ square).trans (Nat.le_mul_of_pos_right _ positive))
  have hj : H*J ≤ N := Nat.mul_le_mul (hM.trans linear) hW
  have one : 1 ≤ N := Nat.mul_pos (pow_pos radix _) positive
  have dim := dimensionTime_le H J 128
  nlinarith only [dim,h,j,hh,hj,one]

private theorem scan_cost_sum (R N H counter elapsed budget bill tapes push rare prep init queue extra : ℕ)
    (records : 0 < R) (volume : 0 < N) (size : H ≤ N) (head : counter ≤ 502951*N)
    (row : elapsed ≤ budget+bill*N) :
    counter+((140+30*(64*64)+6*tapes)*(R*N)+
      ((init*((1+64*64)*(R*N))+(queue*(R*N)+4)+(4*rare+1+rare*(6*(prep*(init*((1+64*64)*(R*N)))))))+
       (R*(elapsed+(4*tapes+1+tapes*(6*(push*elapsed)))+(128*128*(4*H+4)+1)+4*N+12*N+16)+extra+4))) ≤
    (502951+(140+30*(64*64)+6*tapes)+(1+rare*(6*prep))*init*(1+64*64)+queue+4+
      (4*rare+1)+(1+tapes*(6*push))*bill+(4*tapes+1)+128*128*8+1+16+16+4)*(R*N)+
      R*((1+tapes*(6*push))*budget)+extra := by
  grw [head,row,size]
  obtain ⟨x,rfl⟩ := Nat.exists_eq_add_of_le volume
  obtain ⟨y,rfl⟩ := Nat.exists_eq_add_of_le records
  ring_nf
  omega

/-- Only the stopped child and the exceptional rows retain a precision-dependent
rate. All remaining work is linear in the packed volume. -/
theorem ordinaryOwnerScanTime_volume_le (tapes push rareTapes preparePush overhead : ℕ) :
    ∃ fixed : ℕ, ∀ r w W records prefixWidth rareRate childBudget, r ≤ 64 → 0 < W → 0 < records →
      let M := prime^(w+1)
      let N : ℕ := M^128*W
      prefixWidth ≤ N →
      ordinaryOwnerScanTime 64 127 r w W M.size W.size records N prefixWidth 0 0 0
        tapes push rareTapes rareRate preparePush overhead childBudget ≤
        fixed*(records*N) + records*((1+tapes*(6*push))*childBudget) +
        (((∑ i ∈ range r, (i+1)*65)*records)/prime)*(rareRate*N) := by
  obtain ⟨a,row⟩ := ordinaryRowTime_volume_le 64 overhead (by decide)
  let setup := directoryQueueInitRate 64 127
  let queue := directoryMatrixRate 64 127
  let factor := 1+tapes*(6*push)
  let bill := 12*64*64+4+a
  let fixed := 502951+(140+30*(64*64)+6*tapes)+
    (1+rareTapes*(6*preparePush))*setup*(1+64*64)+(12*64*64+4+queue)+4+
    (4*rareTapes+1)+factor*bill+(4*tapes+1)+128*128*8+1+16+16+4
  refine ⟨fixed,?_⟩
  intro r w W records prefixWidth rareRate childBudget rank hW live M N prefixBound
  have radix : 0 < M := pow_pos prime_prime.pos _
  have size : M.size ≤ N := (Nat.size_le.2 Nat.lt_two_pow_self : M.size ≤ M).trans
    ((show M ≤ M^128 by simpa using Nat.pow_le_pow_right radix (by decide : 1 ≤ 128)).trans (Nat.le_mul_of_pos_right _ hW))
  have one : 1 ≤ N := Nat.mul_pos (pow_pos radix _) hW
  have elapsed := row r w W prefixWidth childBudget rank hW
  have price := elapsed.trans (Nat.add_le_add_right (Nat.add_le_add_left (Nat.mul_le_mul_left _ prefixBound) childBudget) (a*N))
  have eq : childBudget+(12*64*64+4)*N+a*N = childBudget+bill*N := by dsimp [bill]; ring
  rw [eq] at price
  have sum := scan_cost_sum records N M.size _ _ childBudget bill tapes push rareTapes preparePush setup
    (12*64*64+4+queue) ((((∑ i ∈ range r, (i+1)*65)*records)/prime)*(rareRate*N))
    live one size (ordinaryCounter_volume_le M W radix hW) price
  simpa only [ordinaryOwnerScanTime,Nat.add_zero,Nat.zero_add] using sum

/-- Uniform precision rate for the complete clean PR589 scanner. The
exceptional coefficient is charged only at the certified label density. -/
theorem ordinaryOwnerScanTime_rate [M8.Machine.Net] (U : Type)
    (r tapes push rareTapes rarePush preparePush overhead : ℕ) (rank : r ≤ 64) (C : ℝ) :
    ∃ rate : ℝ, ∀ (w W records prefixWidth childBudget : ℕ), 0 < W → 0 < records →
      let M := prime^(w+1)
      let N : ℕ := M^128*W
      let power := ((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau
      prefixWidth ≤ N → (childBudget : ℝ) ≤ C*power*N →
      ((ordinaryOwnerScanTime 64 127 r w W M.size W.size records N prefixWidth 0 0 0 tapes push
        rareTapes (exceptionalVolumeRate U 127 64 rareTapes rarePush w) preparePush overhead childBudget : ℕ) : ℝ) ≤
        rate*power*(records*N : ℕ) := by
  obtain ⟨fixed,price⟩ := ordinaryOwnerScanTime_volume_le tapes push rareTapes preparePush overhead
  let coeff := exceptionalRecordTime_binary_le U 127 64 rareTapes rarePush
  let base := coeff.choose
  let swaps := coeff.choose_spec.choose
  let rare : ℝ := base + (swaps : ℝ)*(3808275+LeafCore.C)
  let labels := ∑ i ∈ range r, (i+1)*65
  let factor := 1+tapes*(6*push)
  refine ⟨fixed+(factor : ℝ)*C+(labels : ℝ)/prime*rare,?_⟩
  intro w W records prefixWidth childBudget hW live M N power width child
  have scaled : 1 ≤ power := Real.one_le_rpow (by exact_mod_cast Nat.le_add_left 1 w) M8.Machine.BudgetBound.exponent_range.1.le
  let fee := exceptionalVolumeRate U 127 64 rareTapes rarePush w
  have feeBound : (fee : ℝ) ≤ rare*power := by
    change ((base+swaps*swapVolumeRate w : ℕ) : ℝ) ≤ _
    rw [Nat.cast_add,Nat.cast_mul]
    calc
      _ ≤ base*power+(swaps : ℝ)*((3808275+LeafCore.C)*power) := by
        apply add_le_add _ (mul_le_mul_of_nonneg_left (swapVolumeRate_le w) (Nat.cast_nonneg _))
        simpa using mul_le_mul_of_nonneg_left scaled (Nat.cast_nonneg base)
      _ = _ := by dsimp only [rare]; ring
  have count : (((labels*records)/prime : ℕ) : ℝ) ≤ (labels : ℝ)/prime*records := by
    have h := Nat.div_mul_le_self (labels*records) prime
    have realBound : (((labels*records)/prime : ℕ) : ℝ)*prime ≤ (labels : ℝ)*records := by exact_mod_cast h
    rw [div_mul_eq_mul_div]
    exact (le_div_iff₀ (by exact_mod_cast prime_prime.pos)).2 realBound
  have bill := price r w W records prefixWidth fee childBudget rank hW live width
  apply (Nat.cast_le (α := ℝ)).mpr bill |>.trans
  change ((fixed*(records*N)+records*(factor*childBudget)+((labels*records)/prime)*(fee*N) : ℕ) : ℝ) ≤ _
  simp only [Nat.cast_add,Nat.cast_mul]
  calc
    _ ≤ ((fixed : ℝ)*power)*(records*N) + records*((factor : ℝ)*(C*power*N)) +
        ((labels : ℝ)/prime*records)*(rare*power*N) := by
      apply add_le_add (add_le_add ?_ ?_) ?_
      · exact mul_le_mul_of_nonneg_right (by simpa using mul_le_mul_of_nonneg_left scaled (Nat.cast_nonneg fixed)) (by positivity)
      · exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left child (Nat.cast_nonneg factor)) (Nat.cast_nonneg records)
      · exact mul_le_mul count (mul_le_mul_of_nonneg_right feeBound (Nat.cast_nonneg N)) (by positivity) (by positivity)
    _ = _ := by push_cast; ring

/-- Extra time charged to the stacks inherited from the parent. -/
theorem ordinaryOwnerScanTime_inherited (m d r w W H J records N prefixWidth archiveSize suffixSize left
    tapes push rareTapes rareRate preparePush overhead childBudget : ℕ) :
    ordinaryOwnerScanTime m d r w W H J records N prefixWidth archiveSize suffixSize left
      tapes push rareTapes rareRate preparePush overhead childBudget =
    ordinaryOwnerScanTime m d r w W H J records N prefixWidth 0 0 0
      tapes push rareTapes rareRate preparePush overhead childBudget +
      (left+(1+rareTapes*(6*preparePush))*directoryQueueInitRate m d*(archiveSize+suffixSize)) := by
  unfold ordinaryOwnerScanTime
  ring

/-- Charge the stopped ordinary row at the common prefix width of the live
directory. Only the exceptional fraction pays for the residual permutation. -/
theorem ordinaryDirectoryTime_le [M8.Machine.Net] {m d w W K H J B : ℕ} (U : Type)
    (proj : Matrix (Fin m) (Fin m) ℚ) (idem : proj*proj = proj)
    (factor : Factorization univ univ proj) (small : ∀ k ∈ factorizationDenominators factor, k < prime)
    (dimension : m+m = d+1) (directory v : Descriptor)
    (shape : directory.beforeH = B*prime^(m*((w+1)*m))) (parent : Fin m → ZMod (prime^(w+1)))
    (prefixes : ℕ → List (Fin (prime+4))) (tail : List (Fin (prime+4))) (schedule : List ℕ → List (Fin (prime+4)))
    (S : Stacks (66+K) prime) (overhead budget tapes push rareTapes rarePush : ℕ)
    (rows : ℕ → Fin (d+1) → Fin (d+1)) (negative : ℕ → Bool) (hW : 0 < W)
    (binary : H = (prime^(w+1)).size) (digits : J = W.size) :
    let M := prime^(w+1)
    let N := M^(m+m)*W
    let labels := List.range (LabelMask.records directory)
    let live := LabelStock.live m (w+1) 1
    let bad := fun j => fallbackBit proj.rank_le_height (reduce M proj) (physicalLabel m (w+1) j)
    let pad := fun width => 1+(4*width+4+(m*m*(4*(w+1)+4)+1)+1)
    let elapsed := fun width => ordinaryRowTime m proj.rank w W H width overhead budget + pad width
    let cleared := fun width => elapsed width+(4*tapes+1+tapes*(6*(push*elapsed width)))
    let advance := (d+1)*(d+1)*(4*H+4)+1
    let usual := fun j => (if live j then cleared (prefixes j).length else pad (prefixes j).length) + advance
    let rare := fun j => exceptionalRecordTime U (rows j) (negative j) m w W H J rareTapes rarePush (prefixes j).length
    let price := fun j => (if live j && bad j then rare j else usual j)+(if live j then 4 else 3)
    let base := cleared (prefixes 0).length+advance+4*N
    DirectoryReady v proj w W H J parent prefixes tail schedule S labels → (prefixes 0).length ≤ N →
    let fixed := (exceptionalRecordTime_binary_le U d m rareTapes rarePush).choose
    let swaps := (exceptionalRecordTime_binary_le U d m rareTapes rarePush).choose_spec.choose
    (labels.map (fun j => 6*N+6+price j+(4*N+4))).sum+2*labels.length+2+(2*(labels.length*N)+2) ≤
        labels.length*(base+12*N+16) + (((∑ k ∈ range proj.rank, (k+1)*(m+1))*labels.length)/prime)*
          ((fixed+swaps*swapVolumeRate w)*N)+4 := by
  subst H J
  intro M N labels live bad pad elapsed cleared advance usual rare price base ready first
  intro fixed swaps
  have bill := (exceptionalRecordTime_binary_le U d m rareTapes rarePush).choose_spec.choose_spec
  apply packedClassifiedTime_le idem factor small proj.rank_le_height directory shape usual rare base
  · intro j hj
    have zero : 0 ∈ labels := List.mem_range.mpr (lt_of_le_of_lt (Nat.zero_le _) (List.mem_range.mp hj))
    have same := (ready.2.1 j hj).symm.trans (ready.2.1 0 zero)
    dsimp only [usual,base]
    rw [same]
    split
    · omega
    · dsimp only [cleared,elapsed]
      omega
  · intro j hj
    have zero : 0 ∈ labels := List.mem_range.mpr (lt_of_le_of_lt (Nat.zero_le _) (List.mem_range.mp hj))
    have prefixWidth := ((ready.2.1 j hj).symm.trans (ready.2.1 0 zero)).le.trans first
    have bound := bill (rows j) (negative j) w W (prefixes j).length hW
    have volumeEq : (prime^(w+1))^(d+1)*W = N := congrArg (fun k => M^k*W) dimension.symm
    rw [volumeEq] at bound
    apply bound.trans
    change (fixed+swaps*swapVolumeRate w)*N+4*(prefixes j).length ≤ base+(fixed+swaps*swapVolumeRate w)*N
    dsimp only [base]
    linarith [Nat.mul_le_mul_left 4 prefixWidth]

end IntegerMultBounds.MathlibTM2.M6.BitNode
