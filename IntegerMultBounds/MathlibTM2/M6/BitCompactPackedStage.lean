module

public import IntegerMultBounds.MathlibTM2.M6.BitCompactFlatStage

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback
open M8.RevMachine RecursiveInterchangeLayout Certificates.PR589
open Shared50ModularControl (prime)

-- The preinitialized outer chart execution is available at 746f2627.
private theorem compactChartCost [M8.Machine.Net] (base coreRate : ℕ) (C : ℝ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ w V : ℕ, 0 < V →
      ((base*V+coreRate*LeafCore.coreCost V (w+1)+
        ⌈C*V*((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau⌉₊+(142081*(12*V+14)+1) : ℕ) : ℝ) ≤
        D*((V : ℝ)*((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau) := by
  let D := (base : ℝ)+coreRate*|LeafCore.C|+|C|+1+(142081*26+1)
  refine ⟨D,by dsimp [D]; positivity,?_⟩
  intro w V positive
  let scale := (V : ℝ)*((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau
  have vol : (V : ℝ) ≤ scale := le_mul_of_one_le_right (Nat.cast_nonneg _)
    (Real.one_le_rpow (by exact_mod_cast Nat.le_add_left 1 w) M8.Machine.BudgetBound.exponent_range.1.le)
  have one : 1 ≤ scale := (show (1 : ℝ) ≤ V by exact_mod_cast positive).trans vol
  have core := RevBudget.coreCost_le V (w+1) (L := ((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau)
    (by rw [max_eq_right (by omega : 1 ≤ w+1)])
  have coreBound : (LeafCore.coreCost V (w+1) : ℝ) ≤ |LeafCore.C| * scale := by simpa only [scale,mul_assoc] using core
  have rounded : (⌈C*V*((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau⌉₊ : ℝ) ≤ |C| *scale+1 := by
    rw [mul_assoc]
    exact (Nat.cast_le.mpr (Nat.ceil_mono (mul_le_mul_of_nonneg_right (le_abs_self C) (zero_le_one.trans one)))).trans
      (Nat.ceil_lt_add_one (mul_nonneg (abs_nonneg C) (zero_le_one.trans one))).le
  change _ ≤ D*scale
  dsimp only [D]
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one]
  simp only [Nat.cast_add,Nat.cast_one] at rounded
  linarith only [mul_le_mul_of_nonneg_left vol (Nat.cast_nonneg base : (0:ℝ) ≤ base),
    mul_le_mul_of_nonneg_left coreBound (Nat.cast_nonneg coreRate : (0:ℝ) ≤ coreRate),rounded,vol,one]

open SweepFile in
/-- A complete compact stage from packed input to packed output in the stopping band. -/
private theorem packedCompactBandExecution [M8.Machine.Net] (n : Fin 9) :
    ∃ states : ℕ, ∀ {U : Type} {Q : ℕ}, states ≤ Q →
    ∃ (T : ℕ) (src dst : Fin (142081+2) ↪ Fin T) (Label : Type) (host : Label → Pr Label T Q prime U)
      (code : Pr Label T Q prime U) (base coreRate : ℕ) (rate C : ℝ) (initial : CutoffNodeInput → Stacks T prime),
      LoadsPackedSeed nodeSeedWords CutoffNodeInput.cells initial ∧ ∀ c : CutoffNodeInput, 7*(c.w+1) ≤ c.cutoff →
      ∀ σ : ℝ, 0 ≤ σ →
      let seed := initial c
      let w := c.w+1
      let V := (prime^w)^16*c.stageWidth
      let W := c.B*prime^(64*(w*64))*c.stageFactor
      let price := base*c.cells+coreRate*LeafCore.coreCost c.cells w+
        ⌊rate*((c.node.width : ℝ)^σ*(c.cutoff : ℝ)^(M8.Machine.BudgetBound.tau-σ)*c.cells)⌋₊
      ∀ x u S, ParentStageWords (fun i => src (i.castAdd 2)) src V x S →
        (∀ j, (∀ i, src i ≠ j) → S.L j = seed.L j ∧ S.R j = seed.R j) →
        ∃ z F k y, Exec host code (mk u S) k (mk z F) ∧
          (∀ js : List _, js.Nodup → k+counterCharge dst F+tapeCharge cleanupWeight js F ≤
            tapeCharge cleanupWeight js S+(price+⌈C*V*(w : ℝ)^M8.Machine.BudgetBound.tau⌉₊)+
              (142081*(12*V+14)+1)+counterCharge src S) ∧ z.user = u.user ∧
          ParentStageWords (fun i => dst (i.castAdd 2)) dst V y F ∧ ∀ j : Fin W,
            let address := fun v => (flatWindowEquiv w W (windowState w v,j)).cast c.sweepVolume
            readRoles address y = (Piece.stage n).run (readRoles address x) := by
  obtain ⟨q,build⟩ := recordFlatCompactStage n
  refine ⟨q,?_⟩
  intro U Q fits
  obtain ⟨t,H,fan,mid,src,P,host,worker,inner,base,k,C,rate,install,apart,run⟩ := build (U := U) fits
  obtain ⟨seed,load,read⟩ := loadSweepWorkerSeed fan mid src apart install
  let live := fan.trans mid
  obtain ⟨code,pack⟩ := flatWordStageWithCounterReserve live host worker
  let place := Exit.chart 0 H
  refine ⟨_,live.trans place,returnedFan live,P,fun f => embProg place id (host f),code,base,k,rate,C,
    fun c => flatStageSeed (seed c),load.flatStage,?_⟩
  intro c band σ nonneg initial w V W price
  apply pack (seed c)
  intro x u S words fresh
  obtain ⟨stock,headers,clear⟩ := read c S fresh
  obtain ⟨z,F,m,y,exec,user,out,act,bill⟩ := run c band σ nonneg x u S words.helperFan stock headers clear
  refine ⟨z,F,m,y,exec,?_,user,out,act⟩
  intro js nd
  have h := bill js nd
  change (m : ℝ)+tapeCharge cleanupWeight (frameSlots live) F+tapeCharge cleanupWeight js F ≤
    tapeCharge cleanupWeight js S+price+C*c.cells*(w : ℝ)^M8.Machine.BudgetBound.tau+
      tapeCharge cleanupWeight (frameSlots live) S at h
  have hv : V = c.cells := c.stageCells
  rw [← hv] at h
  have rounded := Nat.le_ceil (C*V*(w : ℝ)^M8.Machine.BudgetBound.tau)
  exact_mod_cast (by linarith only [h,rounded] :
    (m : ℝ)+tapeCharge cleanupWeight (frameSlots live) F+tapeCharge cleanupWeight js F ≤
      tapeCharge cleanupWeight js S+(price+(⌈C*V*(w : ℝ)^M8.Machine.BudgetBound.tau⌉₊ : ℝ))+
        tapeCharge cleanupWeight (frameSlots live) S)

/-- The packed stage has one rate for all stopping-band nodes and all nonnegative exponents. -/
theorem packedCompactBandStage [M8.Machine.Net] (n : Fin 9) :
    ∃ states : ℕ, ∀ {U : Type} {Q : ℕ}, states ≤ Q →
    ∃ (T : ℕ) (src dst : Fin (142081+2) ↪ Fin T) (Label : Type) (host : Label → Pr Label T Q prime U)
      (code : Pr Label T Q prime U) (rate : ℝ) (initial : CutoffNodeInput → Stacks T prime),
      LoadsPackedSeed nodeSeedWords CutoffNodeInput.cells initial ∧ ∀ c : CutoffNodeInput, 7*(c.w+1) ≤ c.cutoff →
      ∀ σ : ℝ, 0 ≤ σ →
      let seed := initial c
      let w := c.w+1
      let V := (prime^w)^16*c.stageWidth
      let W := c.B*prime^(64*(w*64))*c.stageFactor
      PackedPieceHandoffWithReserve cleanupWeight (fun l r => ∑ j, cleanupWeight (l j) (r j)) V
        (fun x y => ∀ j : Fin W,
          let address := fun v => (flatWindowEquiv w W (windowState w v,j)).cast c.sweepVolume
          readRoles address y = (Piece.stage n).run (readRoles address x)) host code src dst seed
        ⌊rate*((c.node.width : ℝ)^σ*(c.cutoff : ℝ)^(M8.Machine.BudgetBound.tau-σ)*c.cells)⌋₊ := by
  obtain ⟨states,build⟩ := packedCompactBandExecution n
  refine ⟨states,?_⟩
  intro U Q fits
  obtain ⟨T,src,dst,Label,host,code,base,coreRate,rate,C,initial,load,run⟩ := build (U := U) fits
  obtain ⟨D,hD,charts⟩ := compactChartCost base coreRate C
  refine ⟨T,src,dst,Label,host,code,D+max 0 rate,initial,load,?_⟩
  intro c band σ nonneg
  have execute := run c band σ nonneg
  intro seed
  intro w V W x u S words fresh
  obtain ⟨z,F,k,y,exec,bill,user,out,effect⟩ := execute x u S words fresh
  refine ⟨z,F,k,y,exec,?_,user,out,effect⟩
  let scale := (c.node.width : ℝ)^σ*(c.cutoff : ℝ)^(M8.Machine.BudgetBound.tau-σ)*c.cells
  have hs : 0 ≤ scale := by dsimp [scale]; positivity
  have hv : 0 < c.cells := Nat.mul_pos (pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _)
    (Nat.mul_pos c.idlePositive (by decide))
  have width := Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.cast_le.mpr (by omega : c.w+1 ≤ c.cutoff))
    M8.Machine.BudgetBound.exponent_range.1.le
  have bound := mul_le_mul_of_nonneg_right (width.trans (cutoffScale_le c σ nonneg (by omega))) (Nat.cast_nonneg c.cells)
  have chart := (charts c.w c.cells hv).trans (mul_le_mul_of_nonneg_left
    ((mul_comm _ _).le.trans bound) hD)
  let overhead := base*c.cells+coreRate*LeafCore.coreCost c.cells w+
    ⌈C*c.cells*(w : ℝ)^M8.Machine.BudgetBound.tau⌉₊+(142081*(12*c.cells+14)+1)
  change (overhead : ℝ) ≤ D*scale at chart
  have cost : overhead+⌊rate*scale⌋₊ ≤ ⌊(D+max 0 rate)*scale⌋₊ := by
    apply Nat.le_floor
    rw [Nat.cast_add,add_mul]
    apply add_le_add chart
    exact (Nat.cast_le.mpr (Nat.floor_mono (mul_le_mul_of_nonneg_right (le_max_right 0 rate) hs))).trans
      (Nat.floor_le (mul_nonneg (le_max_left ..) hs))
  intro js nd
  have paid := bill js nd
  rw [c.stageCells] at paid
  dsimp only [overhead,w,scale] at cost
  change k+counterCharge dst F+tapeCharge cleanupWeight js F ≤ tapeCharge cleanupWeight js S+(_+counterCharge src S)
  omega

end IntegerMultBounds.MathlibTM2.M6.BitNode
