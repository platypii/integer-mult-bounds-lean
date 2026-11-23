module

public import IntegerMultBounds.MathlibTM2.M6.BitFlatSweepHandoff
public import IntegerMultBounds.MathlibTM2.M6.BitPackedIdleWindow

/-! Match mixed idle charges to the parent's physical child directory. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks RecursiveInterchangeLayout
open Shared50ModularControl (prime)

/-- With both child rates zero, the window charge consists exactly of its
local work. Adding the scheduled child budgets recovers its physical bill. -/
theorem mixedIdleBill (U : Type) (node : Descriptor) (w groups W cutoff : ℕ)
    (width : node.width = 64*(w+1)) (rows : node.rows = 142080*(142080*groups))
    (spectator : W = node.beforeRows*groups*node.beforeH*node.between*node.afterD)
    (rate : ℝ) (time : Fin nodeChildren5.length → ℕ) (i : Fin 9) :
    let child := scheduledChild prime node
    let budget := fun j => if cutoff < (child j).width then time j else
      ⌊(rate*((child j).width : ℝ)^M8.Machine.BudgetBound.tau)*volume prime (child j)⌋₊
    (idleCopies.map (fun k => idleCutoffCharge U i w W cutoff rate k
      (time (idleDirectoryIndex (i,idleCopyIndex k))))).sum =
      (idleCopies.map (fun k => idleCutoffCharge U i w W cutoff 0 k 0)).sum +
      ∑ j : Fin idleCopies.length, budget (idleDirectoryIndex (i,j)) := by
  intro child budget
  rw [← sumIndexed idleCopies idleCopyIndex idleCopyIndex_at (fun j => budget (idleDirectoryIndex (i,j))),
    ← List.sum_map_add]
  apply congrArg List.sum
  apply List.map_congr_left
  intro k _
  let e := idleInterval i k.2
  let lane := phaseIntervalChild (e.1+1) (e.2+1) (w+1) W 64
  let j := idleDirectoryIndex (i,idleCopyIndex k)
  obtain ⟨same,_,size⟩ := alignedIntervalMeasures node (w+1) groups W (Nat.succ_pos _) width rows spectator i k
  change lane.width = (child j).width at same
  change volume prime lane*142080 = volume prime (child j) at size
  rw [show volume prime lane = (prime^(w+1))^128*W from intervalChild_volume
    (Nat.succ_le_succ (idleBounds i k.2).1) (Nat.succ_le_succ (idleBounds i k.2).2) _ _] at size
  dsimp only [idleCutoffCharge,budget]
  change _ + (if cutoff < lane.width then _ else _) =
    (_ + (if cutoff < lane.width then _ else _)) + (if cutoff < (child j).width then _ else _)
  rw [← same,← size]
  dsimp only [lane,e] at same ⊢
  split <;> simp only [zero_mul,Nat.floor_zero,Nat.add_zero] <;> omega

open Certificates.PR589 in
/-- The sweep ranges and charged idle windows together pay one cutoff budget
per scheduled occurrence, plus precisely the local idle work. -/
theorem mixedNodeDirectoryBill (U : Type) (node : Descriptor) (w groups W cutoff : ℕ)
    (width : node.width = 64*(w+1)) (rows : node.rows = 142080*(142080*groups))
    (spectator : W = node.beforeRows*groups*node.beforeH*node.between*node.afterD)
    (rate : ℝ) (time : Fin nodeChildren5.length → ℕ) :
    let child := scheduledChild prime node
    let budget := fun j => if cutoff < (child j).width then time j else
      ⌊(rate*((child j).width : ℝ)^M8.Machine.BudgetBound.tau)*volume prime (child j)⌋₊
    let atPos := fun n => if h : n < nodeChildren5.length then budget ⟨n,h⟩ else 0
    let sweep := fun i => ((List.range' (stageChildStart i)
      (stageRuns.flatMap (fun _ => Geometry.Moves.localPaid)).length).map atPos).sum
    let idle := fun i => (idleCopies.map (fun k => idleCutoffCharge U i w W cutoff rate k
      (time (idleDirectoryIndex (i,idleCopyIndex k))))).sum
    (∑ i, sweep i) + (∑ i, idle i) =
      (∑ i, (idleCopies.map (fun k => idleCutoffCharge U i w W cutoff 0 k 0)).sum) + ∑ j, budget j := by
  intro child budget atPos sweep idle
  let own := fun i => (idleCopies.map (fun k => idleCutoffCharge U i w W cutoff 0 k 0)).sum
  let children := fun i => ∑ j : Fin idleCopies.length, budget (idleDirectoryIndex (i,j))
  have windows (i) : idle i = own i + children i :=
    mixedIdleBill U node w groups W cutoff width rows spectator rate time i
  have partition : (∑ i, sweep i) + (∑ i, children i) = ∑ j, budget j := by
    simpa only [atPos,Fin.isLt,dite_eq_left,Fin.eta] using nodeChildDirectoryBill atPos
  change _ = (∑ i, own i) + _
  simp only [windows,Finset.sum_add_distrib]
  omega

/-- A uniform coefficient pays the local idle charge on either side of the
cutoff, including header setup, interval packing, row splitting and merging. -/
theorem idleCutoffLocal_bound (U : Type) :
    ∃ D : ℝ, 0 < D ∧ ∀ i w W cutoff k, 0 < W →
      (idleCutoffCharge U i w W cutoff 0 k 0 : ℝ) ≤
        D*((prime^(w+1))^128*W : ℕ)*((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau := by
  obtain ⟨setup,swaps,toll⟩ := intervalChildToll_le U
  obtain ⟨D,pos,bound⟩ := copyReturn_parentCost (setup+10^14) swaps
  refine ⟨D,pos,?_⟩
  intro i w W cutoff k hW
  let V := (prime^(w+1))^128*W
  have atom : w+1 ≤ V := (Nat.lt_pow_self Shared50ModularControl.prime_prime.one_lt).le.trans
    ((Nat.le_self_pow (by decide : 128 ≠ 0) _).trans (Nat.le_mul_of_pos_right _ hW))
  let e := idleInterval i k.2
  have fee := toll e.1.succ e.2.succ (Nat.succ_le_succ (idleBounds i k.2).1)
    (Nat.succ_le_succ (idleBounds i k.2).2) w W hW
  have arithmetic (v d t c : ℕ) (active : Prop) [Decidable active] (hd : d ≤ v) (hv : 0 < v)
      (ht : t ≤ c*v) :
      (149*(intervalSplitTapes+5)+5)*(v*142080)+24+
        (if active then 21*d+13+(t+(149*(v*142080)*(intervalSplitTapes+5)+6))
         else 142081*(8*v+10)+1+(149*(v*142080)*(intervalSplitTapes+5)+6)) ≤
      2*((c+10^14)*v) := by
    rw [Nat.add_mul c (10^14) v]
    norm_num [intervalSplitTapes]
    split <;> omega
  have localBill : idleCutoffCharge U i w W cutoff 0 k 0 ≤
      0+2*((setup+10^14+swaps*Cover.Fallback.swapVolumeRate w)*V) := by
    rw [show setup+10^14+swaps*Cover.Fallback.swapVolumeRate w =
      (setup+swaps*Cover.Fallback.swapVolumeRate w)+10^14 by omega]
    simpa only [idleCutoffCharge,zero_mul,Nat.floor_zero,Nat.add_zero,Nat.zero_add] using
      arithmetic V (w+1) _ (setup+swaps*Cover.Fallback.swapVolumeRate w)
        (cutoff < (phaseIntervalChild (e.1+1) (e.2+1) (w+1) W 64).width) atom (by omega) fee
  simpa only [Nat.cast_zero,zero_add] using bound w V 0 _ localBill

/-- Summing all idle windows changes only the width-independent coefficient. -/
theorem idleNodeLocal_bound (U : Type) :
    ∃ D : ℝ, 0 < D ∧ ∀ w W cutoff, 0 < W →
      ((∑ i : Fin 9, (idleCopies.map (fun k => idleCutoffCharge U i w W cutoff 0 k 0)).sum : ℕ) : ℝ) ≤
        D*((prime^(w+1))^128*W : ℕ)*((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau := by
  obtain ⟨D,pos,job⟩ := idleCutoffLocal_bound U
  refine ⟨9*35520*D, by positivity, ?_⟩
  intro w W cutoff hW
  let R := D*((prime^(w+1))^128*W : ℕ)*((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau
  have stage (i : Fin 9) (xs : List _) :
      ((xs.map (fun k => idleCutoffCharge U i w W cutoff 0 k 0)).sum : ℝ) ≤ xs.length*R := by
    induction xs with
    | nil => simp
    | cons k xs ih =>
      simp only [List.map_cons,List.sum_cons,Nat.cast_add,List.length_cons,Nat.cast_one,add_mul,one_mul]
      linarith [show (idleCutoffCharge U i w W cutoff 0 k 0 : ℝ) ≤ R from job i w W cutoff k hW]
  rw [Nat.cast_sum]
  calc
    _ ≤ ∑ _ : Fin 9, (idleCopies.length : ℝ)*R := Finset.sum_le_sum fun i _ => stage i idleCopies
    _ = _ := by simp [idleCopies_length,R]; ring

private theorem nodeBill_reorder (overhead sweep idle : Fin 9 → ℕ) (own calls copy bridge : ℕ)
    (bill : (∑ i, sweep i)+(∑ i, idle i) = own+calls) :
    (∑ i, (overhead i+sweep i))+(∑ i, (idle i+1+copy+1))+bridge+2 =
      (∑ i, overhead i)+own+9*(1+copy+1)+bridge+2+calls := by
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul]
  omega

open Certificates.PR589 in
/-- Assemble the physical mixed node with one budget per directory entry.
The sweep suppliers expose their own overhead separately from their calls. -/
theorem mixedDirectoryHandoff {U : Type} (minimum : ℝ := 0) :
    ∃ (states : ℕ) (rate : ℝ), 0 ≤ rate ∧ minimum ≤ rate ∧ ∀ {Q : ℕ}, states ≤ Q →
    ∀ (node : Descriptor) (w groups W cutoff : ℕ),
      node.width = 64*(w+1) → node.rows = 142080*(142080*groups) →
      W = node.beforeRows*groups*node.beforeH*node.between*node.afterD → 0 < W →
    let Job := (Fin 32 × Fin 5) × Fin 222
    let V := (prime^(w+1))^128*W
    let m := (prime^(w+1))^128*(W*142080)
    let lane := fun i (k : Job) => let e := idleInterval i k.2
      phaseIntervalChild (e.1+1) (e.2+1) (w+1) W 64
    ∀ (atom : Fin 9 → Job → ℕ) (time : Fin nodeChildren5.length → ℕ) (overhead : Fin 9 → ℕ),
    let child := scheduledChild prime node
    let budget := fun j => if cutoff < (child j).width then time j else
      ⌊(rate*((child j).width : ℝ)^M8.Machine.BudgetBound.tau)*volume prime (child j)⌋₊
    let atPos := fun n => if h : n < nodeChildren5.length then budget ⟨n,h⟩ else 0
    let sweep := fun i => ((List.range' (stageChildStart i)
      (stageRuns.flatMap (fun _ => Geometry.Moves.localPaid)).length).map atPos).sum
    (∀ i k, cutoff < (lane i k).width → (lane i k).width = 64*atom i k) →
    (∀ i k, cutoff < (lane i k).width → (lane i k).width < 64*(w+1) →
      PackedWindowHandoff U Q V (packedChildOutput (atom i k) V)
        (time (idleDirectoryIndex (i,idleCopyIndex k)))) →
    (∀ i, PackedWindowHandoff U Q m (fun x y => ∀ j : Fin (W*142080),
      let addr := fun z => flatWindowEquiv (w+1) (W*142080) (windowState (w+1) z,j)
      readRoles addr y = (Piece.stage i).run (readRoles addr x)) (overhead i+sweep i)) →
    let localIdle := ∑ i, (idleCopies.map (fun k => idleCutoffCharge U i w W cutoff 0 k 0)).sum
    PackedWindowHandoff U Q m (packedChildOutput (w+1) m)
      ((∑ i, overhead i)+localIdle+9*(1+142081*(8*m+10)+1)+
        9*(2*(76*17760*m*(142081+7)+6)+1+(142081*(8*m+10)+1))+2+∑ j, budget j) := by
  obtain ⟨states,rate,pos,enough,assemble⟩ := mixedFlatNode (U := U) minimum
  refine ⟨states,rate,pos,enough,?_⟩
  intro Q room node w groups W cutoff width rows spectator live Job V m lane atom time overhead
    child budget atPos sweep aligned children sweeps localIdle
  have run := assemble room live cutoff atom (fun i k => time (idleDirectoryIndex (i,idleCopyIndex k)))
    (fun i => overhead i+sweep i) aligned children sweeps
  have bill := mixedNodeDirectoryBill U node w groups W cutoff width rows spectator rate time
  exact (congrArg (PackedWindowHandoff U Q m (packedChildOutput (w+1) m))
    (nodeBill_reorder overhead sweep _ localIdle _ _ _ bill)).mp run

open Certificates.PR589 Stack Host M8.RevMachine in
/-- Execute the mixed directory node from nine packed stage contracts. -/
theorem mixedPackedNode {U : Type} (minimum : ℝ := 0) :
    ∃ (states : ℕ) (rate C : ℝ) (base nt : ℕ), 0 ≤ rate ∧ minimum ≤ rate ∧ ∀ {Q : ℕ}, states ≤ Q →
    ∀ (node : Descriptor) (w groups W B cutoff : ℕ),
      node.width = 64*(w+1) → node.rows = 142080*(142080*groups) →
      W = node.beforeRows*groups*node.beforeH*node.between*node.afterD → 0 < W → node.beforeH = B*prime^(64*((w+1)*64)) →
    let rows := 142080*groups
    let K := node.beforeRows*rows*node.between*node.afterD
    0 < B → 0 < K → ({node with rows := rows} : Descriptor).Positive →
    let Job := (Fin 32 × Fin 5) × Fin 222
    let V := (prime^(w+1))^128*W
    let m := (prime^(w+1))^128*(W*142080)
    let lane := fun i (k : Job) => let e := idleInterval i k.2
      phaseIntervalChild (e.1+1) (e.2+1) (w+1) W 64
    ∀ (atom : Fin 9 → Job → ℕ) (time : Fin nodeChildren5.length → ℕ) (P : Fin 9 → Type)
      (t : Fin 9 → StageRun → ℕ) (body : ∀ i j, P i → Pr (P i) (t i j) Q prime U)
      (coeff : Fin 9 → StageRun → ℝ) (required : Fin 9 → (ℕ → ℕ) → Prop),
    let overhead := fun i => ⌊(stageSetupCost base nt m (w+1) : ℝ)+
      (C+|stagePackingRate i+(stageRuns.map (coeff i)).sum|)*m*((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau⌋₊+
      142081*(8*m+10)+1
    let child := scheduledChild prime node
    let budget := fun j => if cutoff < (child j).width then time j else
      ⌊(rate*((child j).width : ℝ)^M8.Machine.BudgetBound.tau)*volume prime (child j)⌋₊
    let atPos := fun n => if h : n < nodeChildren5.length then budget ⟨n,h⟩ else 0
    (∀ i k, cutoff < (lane i k).width → (lane i k).width = 64*atom i k) →
    (∀ i k, cutoff < (lane i k).width → (lane i k).width < 64*(w+1) →
      PackedWindowHandoff U Q V (packedChildOutput (atom i k) V)
        (time (idleDirectoryIndex (i,idleCopyIndex k)))) →
    (∀ i, PackedStageExecution (w := w+1) (B := B) (K := K) i (t i) (body i) (coeff i) (required i)) →
    (∀ i, required i atPos) →
    let localIdle := ∑ i, (idleCopies.map (fun k => idleCutoffCharge U i w W cutoff 0 k 0)).sum
    PackedWindowHandoff U Q m (packedChildOutput (w+1) m)
      ((∑ i, overhead i)+localIdle+9*(1+142081*(8*m+10)+1)+
        9*(2*(76*17760*m*(142081+7)+6)+1+(142081*(8*m+10)+1))+2+∑ j, budget j) := by
  obtain ⟨states,rate,pos,enough,assemble⟩ := mixedDirectoryHandoff (U := U) minimum
  obtain ⟨C,base,nt,stageStates,stage⟩ := flatSweepFromPacked
  let divStates := (fun {q : ℕ} (_ : Program 38 q prime) => q) (RecursiveRowsNodeHeaders.program 142080)
  refine ⟨max states (max divStates stageStates),rate,|C|,base,nt,pos,enough,?_⟩
  intro Q room node w groups W B cutoff width split spectator live label rows K hB hK positive Job V m lane
    atom time P t body coeff required overhead child budget atPos aligned children runs ready localIdle
  refine assemble ((le_max_left _ _).trans room) node w groups W cutoff width split spectator live atom time overhead aligned children ?_
  intro i
  have caps := (le_max_right _ _).trans room
  have call := stage node i (t i) (body i) (coeff i) (required i) ((le_max_left _ _).trans caps)
    width split label ((le_max_right _ _).trans caps) hB hK positive (runs i) atPos (ready i)
  have shape : B*prime^(64*((w+1)*64))*K = W*142080 := by
    rw [spectator,label]
    dsimp only [K,rows]
    ac_rfl
  let calls := ((List.range' (stageChildStart i)
    (stageRuns.flatMap (fun _ => Geometry.Moves.localPaid)).length).map atPos).sum
  let result (suffix : ℕ) := let v := (prime^(w+1))^128*suffix
    PackedWindowHandoff U Q v (fun x y => ∀ j : Fin suffix,
      let addr := fun z => flatWindowEquiv (w+1) suffix (windowState (w+1) z,j)
      readRoles addr y = (Piece.stage i).run (readRoles addr x))
      (⌊(stageSetupCost base nt v (w+1) : ℝ)+(C+|stagePackingRate i+(stageRuns.map (coeff i)).sum|)*
        v*((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau+calls⌋₊+142081*(8*v+10)+1)
  apply handoff_le ((congrArg result shape).mp call)
  exact collectSweep C _ _ _ m calls _ (Real.rpow_nonneg (Nat.cast_nonneg _) _)

end IntegerMultBounds.MathlibTM2.M6.BitNode
