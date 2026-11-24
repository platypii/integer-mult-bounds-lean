module

public import IntegerMultBounds.MathlibTM2.M6.BitCompactPhase

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback
open M8.RevMachine RecursiveInterchangeLayout Certificates.PR589
open Shared50ModularControl (prime)

/-- An active phase calls the packed child between the forward and reverse
field permutations. The caller reads the result at its inherited addresses. -/
theorem packedPhaseChild [M8.Machine.Net] {P U : Type} {T Q : ℕ}
    (capacity : rowSwapBlock.states ≤ Q) (ports : Fin (rowSwapBlock.tapes+35) ↪ Fin T)
    (body : P → Pr P T Q prime U) (entry worker : P) (edge : ℕ × ℕ)
    (checked : Geometry.Moves.CheckedPair edge) (positive : 0 < Geometry.moveRank edge.1 edge.2) :
    let lo := min (Geometry.Dimensions.value edge.1) (Geometry.Dimensions.value edge.2)
    let hi := max (Geometry.Dimensions.value edge.1) (Geometry.Dimensions.value edge.2)
    let order := phasePackSchedule lo hi
    let pack := fun js => statePlacedNormalized ports capacity swapStates_pos Empty.elim (packSchedule 16 js)
    body entry = (pack order).seq ((Prog.call worker).seq (pack order.reverse)) →
    ∃ setup swaps : ℕ, ∀ (p : CutoffNodeInput) (i : Fin nodeChildren5.length),
      nodeChildren5[i.val] = Geometry.moveRank edge.1 edge.2 →
      let child := scheduledChild prime p.node i
      let W := p.stageWidth
      let V := (prime^(p.w+1))^16*W
      let lane := phaseIntervalChild lo hi (p.w+1) W
      let size := phaseIntervalChild_volume (phaseInterval_bounds checked positive).1.le
        (phaseInterval_bounds checked positive).2 (p.w+1) W
      ∃ packed : Fin (volume prime child) ≃ Fin V,
        (∀ k, (packed k).val = (CopyChildLayout.packActive child k).val) ∧
        ∀ position : Fin (volume prime child) ≃ Fin V, InheritedIntervalPositions child lane size position →
        ∀ record price, ScheduledChildExec p.node child p.w W ports record packed body worker price true →
        ScheduledChildExec p.node child p.w W ports record position body entry
          (price+4+(setup+swaps*swapVolumeRate p.w)*V) true := by
  intro lo hi order pack installed
  obtain ⟨setup,swaps,compile⟩ := phasePackedCall_exec true capacity edge checked positive ports body worker
  refine ⟨setup,swaps,?_⟩
  intro p i rank child
  generalize hW : p.stageWidth = tail
  intro W V lane size
  have align : p.B*prime^(64*((p.w+1)*64))*((prime^(p.w+1))^112*p.stageFactor) = W := by
    dsimp only [W]; rw [← hW]; dsimp only [CutoffNodeInput.stageWidth]; ring
  have volumePos : 0 < V := by
    dsimp only [V,W]; rw [← hW,p.stageCells]
    exact Nat.mul_pos (pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _) (Nat.mul_pos p.idlePositive (by decide))
  dsimp only [W] at *
  clear hW
  subst tail
  have build := compile p.node i p.w p.B p.rowsPerStage rank p.width p.rows p.label
  obtain ⟨packed,address,run⟩ := build (Nat.pos_of_mul_pos_left volumePos)
  refine ⟨packed,address,?_⟩
  intro position coords record price childExec smaller u S x stored clean
  obtain ⟨z,F,n,same,paid,exec,out,fresh,frame⟩ := run u S record (fun _ => blank) 0 x price childExec stored clean
  rw [installed]
  refine ⟨z,F,n,_,exec,paid,same,out,fresh,frame,?_⟩
  apply (coords.transpose_iff _ x _).2 rfl
  change lane.width = nodeChildren5[i.val]*(p.node.width/64)
  rw [rank,p.width,Nat.mul_div_cancel_left _ (by decide : 0 < 64)]
  exact phaseIntervalChild_width checked (p.w+1) W


/-- Run a complete scalar phase with packed active children. Each active call
pays its forward and reverse permutations; the stopped branch keeps its leaf cost. -/
theorem packedCompactPhase [M8.Machine.Net] (n : Fin 9) (p : Fin 32 × Fin 5) (afterCopy : Bool) :
    let J := Fin (selectedPhaseSchedule afterCopy).1.length
    let index := selectedPhaseIndex afterCopy
    ∃ (C : ℝ) (tapes : J → ℕ) (regs : ∀ j, Fin (rowSwapBlock.tapes+35) ↪ Fin (tapes j))
      (T states : ℕ) (fan : Fin (142081+2) ↪ Fin T) (bank : ∀ j, Fin (tapes j) ↪ Fin T),
    ∀ {P U : Type} {Q : ℕ}, states ≤ Q →
      ∀ (large : ∀ j, P → Pr (Option (WorkerLabel (Option P))) (tapes j) Q prime U) (f : J → P),
      ∃ body : ∀ j, Option (WorkerLabel (Option P)) → Pr (Option (WorkerLabel (Option P))) (tapes j) Q prime U,
      (∀ j g, body j (some (.active (some g))) = large j g) ∧
      let host := fun g : J × Option (WorkerLabel (Option P)) => embProg (bank g.1) (Prod.mk g.1) (body g.1 g.2)
      ∃ (code : Pr (J × Option (WorkerLabel (Option P))) T Q prime U) (localRate : ℕ) (base swaps : J → ℕ) (setup : Pr Empty (T+7) Q prime U), ∀ c : CutoffNodeInput,
      let W := c.stageWidth
      let V := (prime^(c.w+1))^16*W
      let child := fun j : J => scheduledChild prime c.node (phaseChildPositions.choose (n,p,index j))
      ∃ (pos : ∀ j, Fin (volume prime (child j)) ≃ Fin V),
      (∀ j k, (pos j k).val = (CopyChildLayout.packActive (child j) k).val) ∧
      ∀ shared : Stacks (142081+2) prime, ∃ prepared : Stacks T prime, embStk fan prepared = shared ∧
      PhaseSeedExec setup fan (selectedPhaseSchedule afterCopy).1.length c prepared ∧
      ∀ (rate : ℝ) (time : J → ℕ), C ≤ rate →
      let price := fun j => if c.cutoff < (child j).width then time j+4+(base j+swaps j*swapVolumeRate c.w)*V else
        ⌊(rate*((child j).width : ℝ)^M8.Machine.BudgetBound.tau)*volume prime (child j)⌋₊
      (∀ j, c.cutoff < (child j).width → ScheduledChildExec c.node (child j) c.w W (regs j)
        (binSyms c.root.width.size c.cutoff) (pos j) (body j) (some (.active (some (f j)))) (time j) true) →
      ∀ (x : Fin 142081 → Fin V → ZMod 2) u S, HelperFan fan x S →
      (∀ k, (∀ h, fan h ≠ k) → S.L k = prepared.L k ∧ S.R k = prepared.R k) →
      ∃ z F t, Exec host code (mk u S) t (mk z F) ∧ z.user = u.user ∧
        CleanupBound S F (t+tapeCharge cleanupWeight (frameSlots fan) F)
          ((List.ofFn price).sum+localRate*c.cells+tapeCharge cleanupWeight (frameSlots fan) S) ∧
        HelperFan fan (invocationPhaseOutput (w := c.w+1) (W := W) n p afterCopy x) F := by
  classical
  intro J index
  obtain ⟨C,tapes,regs,T,states,fan,bank,compile⟩ := compactPhase n p afterCopy
  refine ⟨C,tapes,regs,T,max states rowSwapBlock.states,fan,bank,?_⟩
  intro P U Q capacity large f
  have room := (le_max_right states rowSwapBlock.states).trans capacity
  let edge (j : J) := (Geometry.Moves.phaseEdges.filter positiveMove)[(index j).val]'(index j).isLt
  let order (j : J) :=
    let a := Geometry.Dimensions.value (edge j).1
    let b := Geometry.Dimensions.value (edge j).2
    phasePackSchedule (min a b) (max a b)
  let pack (j : J) (js : List ℕ) : Pr (Option (WorkerLabel (Option P))) (tapes j) Q prime U :=
    statePlacedNormalized (regs j) room swapStates_pos Empty.elim (packSchedule 16 js)
  let active (j : J) : Option P → Pr (Option (WorkerLabel (Option P))) (tapes j) Q prime U
    | none => (pack j (order j)).seq ((Prog.call (some (.active (some (f j))))).seq (pack j (order j).reverse))
    | some g => large j g
  obtain ⟨body,installed,code,localRate,setup,phase⟩ := compile ((le_max_left ..).trans capacity) active (fun _ => none)
  have mem (j : J) := List.mem_filter.mp (List.getElem_mem (l := Geometry.Moves.phaseEdges.filter positiveMove) (index j).isLt)
  have checked (j : J) := Geometry.Moves.phase_checked (edge j) (mem j).1
  have positive (j : J) : 0 < Geometry.moveRank (edge j).1 (edge j).2 := Nat.pos_of_ne_zero (bne_iff_ne.mp (mem j).2)
  choose base swaps adapt using fun j : J => packedPhaseChild room (regs j) (body j) (some (.active none))
    (some (.active (some (f j)))) (edge j) (checked j) (positive j) (installed j none)
  refine ⟨body,fun j g => installed j (some g),code,localRate,base,swaps,setup,?_⟩
  intro c W V child
  obtain ⟨position,size,coords,prepare⟩ := phase c
  choose packed address wrap using fun j : J => adapt j c (phaseChildPositions.choose (n,p,index j))
    (phaseChildPositions.choose_spec n p (index j)).1
  refine ⟨packed,address,?_⟩
  intro shared
  obtain ⟨seed,view,loaded,run⟩ := prepare shared
  refine ⟨seed,view,loaded,?_⟩
  intro rate time enough price work
  exact run rate (fun j => time j+4+(base j+swaps j*swapVolumeRate c.w)*V) enough
    (fun j live => wrap j (position j) (coords j) _ (time j) (work j live))

/-- Over the first range above the stopping band, all active field permutations
in the phase fit a single cutoff-power allowance, independently of the child prices. -/
theorem packedPhaseRoutingBound [M8.Machine.Net] {J : Type} [Fintype J]
    (base swaps : J → ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : CutoffNodeInput) (live : J → Bool),
      49*(p.w+1) ≤ 64*p.cutoff →
      ((∑ j, if live j then 4+(base j+swaps j*swapVolumeRate p.w)*p.cells else 0 : ℕ) : ℝ) ≤
        C*p.cells*(p.cutoff : ℝ)^M8.Machine.BudgetBound.tau := by
  classical
  let τ := M8.Machine.BudgetBound.tau
  have nonneg : 0 ≤ τ := M8.Machine.BudgetBound.exponent_range.1.le
  obtain ⟨A,pos,bound⟩ := copyReturn_parentCost (∑ j, (base j+4)) (∑ j, swaps j)
  refine ⟨A*2^τ,mul_pos pos (Real.rpow_pos_of_pos (by norm_num) _),?_⟩
  intro p live band
  have cells : 0 < p.cells := Nat.mul_pos (pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _)
    (Nat.mul_pos p.idlePositive (by decide))
  have route : (∑ j, if live j then 4+(base j+swaps j*swapVolumeRate p.w)*p.cells else 0) ≤
      ((∑ j, (base j+4))+(∑ j, swaps j)*swapVolumeRate p.w)*p.cells := by
    rw [Finset.sum_mul,← Finset.sum_add_distrib,Finset.sum_mul]
    apply Finset.sum_le_sum
    intro j _
    split
    · have := Nat.le_mul_of_pos_right 4 cells
      simp only [Nat.add_mul]
      omega
    · exact Nat.zero_le _
  have h := bound p.w p.cells 0 _ (route.trans (by omega))
  rw [Nat.cast_zero,zero_add] at h
  have width : ((p.w+1 : ℕ) : ℝ) ≤ 2*(p.cutoff : ℝ) := by
    exact_mod_cast (show p.w+1 ≤ 2*p.cutoff by omega)
  have power := Real.rpow_le_rpow (by positivity) width nonneg
  rw [Real.mul_rpow (by norm_num) (Nat.cast_nonneg _)] at power
  apply h.trans
  calc
    _ ≤ A*p.cells*(2^τ*(p.cutoff : ℝ)^τ) := mul_le_mul_of_nonneg_left power (by positivity)
    _ = _ := by ring

end IntegerMultBounds.MathlibTM2.M6.BitNode
