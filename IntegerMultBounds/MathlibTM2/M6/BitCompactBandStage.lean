module

public import IntegerMultBounds.MathlibTM2.M6.BitCompactInitializedStage
public import IntegerMultBounds.MathlibTM2.M6.BitSweepChildWidth
public import IntegerMultBounds.MathlibTM2.M6.BitNodeSeedWords

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback
open M8.RevMachine RecursiveInterchangeLayout Certificates.PR589
open Shared50ModularControl (prime)

/-- With only stopped children, the whole stage directory is bounded by one
cutoff-width leaf charge per entry, all at the same role volume. -/
theorem stoppedDirectoryCost [M8.Machine.Net] (c : CutoffNodeInput) (rate : ℝ) (indices : List ℕ) :
    (indices.map (stageBranchTime c.node c.cutoff rate (fun _ => 0))).sum ≤
      indices.length*⌊max 0 rate*(c.cutoff : ℝ)^M8.Machine.BudgetBound.tau*c.cells⌋₊ := by
  have bound i : stageBranchTime c.node c.cutoff rate (fun _ => 0) i ≤
      ⌊max 0 rate*(c.cutoff : ℝ)^M8.Machine.BudgetBound.tau*c.cells⌋₊ := by
    unfold stageBranchTime
    split
    · rename_i h
      dsimp only
      split
      · exact Nat.zero_le _
      · rename_i stop
        let d := scheduledChild prime c.node ⟨i,h⟩
        have share := (scheduledChild_measures prime c.node ⟨_,c.width⟩ ⟨_,c.rows⟩ ⟨i,h⟩).2
        have mass : volume prime d = c.cells := by
          apply Nat.eq_of_mul_eq_mul_right (by decide : 0 < 142080)
          exact share.trans c.cells_share.symm
        change ⌊rate*(d.width : ℝ)^M8.Machine.BudgetBound.tau*volume prime d⌋₊ ≤ _
        rw [mass]
        apply Nat.floor_mono
        apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
        exact mul_le_mul (le_max_right ..) (Real.rpow_le_rpow (Nat.cast_nonneg _)
          (Nat.cast_le.mpr (le_of_not_gt stop)) M8.Machine.BudgetBound.exponent_range.1.le)
          (Real.rpow_nonneg (Nat.cast_nonneg _) _) (le_max_left ..)
    · exact Nat.zero_le _
  induction indices with
  | nil => simp
  | cons i xs ih =>
    simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.succ_mul]
    exact (Nat.add_le_add (bound i) ih).trans_eq (Nat.add_comm ..)

private theorem bandStageBill [M8.Machine.Net] (c : CutoffNodeInput) (fits : c.w+1 ≤ c.cutoff)
    (pack rate : ℝ) (localRate calls : ℕ) :
    let τ := M8.Machine.BudgetBound.tau
    let C := max 0 pack+1+localRate+calls*max 0 rate
    ⌈pack*((c.cells : ℝ)*((c.w+1 : ℕ) : ℝ)^τ)⌉₊+localRate*c.cells+
      calls*⌊max 0 rate*(c.cutoff : ℝ)^τ*c.cells⌋₊ ≤ ⌊C*((c.cutoff : ℝ)^τ*c.cells)⌋₊ := by
  intro τ C
  let scale := (c.cutoff : ℝ)^τ*c.cells
  have pos : 0 < c.cells := Nat.mul_pos (pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _)
    (Nat.mul_pos c.idlePositive (by decide))
  have unit : 1 ≤ (c.cutoff : ℝ)^τ := Real.one_le_rpow (by exact_mod_cast (by omega : 1 ≤ c.cutoff))
    M8.Machine.BudgetBound.exponent_range.1.le
  have cells : (c.cells : ℝ) ≤ scale := le_mul_of_one_le_left (by positivity) unit
  have one : 1 ≤ scale := (show (1 : ℝ) ≤ c.cells by exact_mod_cast pos).trans cells
  have width := Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.cast_le.mpr fits : ((c.w+1 : ℕ) : ℝ) ≤ c.cutoff)
    M8.Machine.BudgetBound.exponent_range.1.le
  have packLe : pack*((c.cells : ℝ)*((c.w+1 : ℕ) : ℝ)^τ) ≤ max 0 pack*scale := by
    rw [mul_comm (c.cells : ℝ)]
    exact mul_le_mul (le_max_right ..) (mul_le_mul_of_nonneg_right width (by positivity)) (by positivity) (le_max_left ..)
  have rounded := (Nat.cast_le (α := ℝ)).mpr (Nat.ceil_mono packLe)
  have upper := Nat.ceil_lt_add_one (mul_nonneg (le_max_left 0 pack) (zero_le_one.trans one))
  have leaf := Nat.floor_le (mul_nonneg (mul_nonneg (le_max_left 0 rate) (zero_le_one.trans unit)) (Nat.cast_nonneg c.cells))
  apply Nat.le_floor
  push_cast
  change _ ≤ C*scale
  dsimp only [C]
  have child := mul_le_mul_of_nonneg_left leaf (Nat.cast_nonneg calls : (0 : ℝ) ≤ calls)
  change _ ≤ (calls : ℝ)*(max 0 rate*(c.cutoff : ℝ)^τ*c.cells) at child
  conv at child => rhs; rw [mul_assoc (max 0 rate)]
  change _ ≤ (calls : ℝ)*(max 0 rate*scale) at child
  push_cast at rounded
  linarith only [rounded,upper,one,child,mul_le_mul_of_nonneg_left cells (Nat.cast_nonneg localRate : (0 : ℝ) ≤ localRate)]

private theorem placedFrameCharge {k t h : ℕ} (fan : Fin k ↪ Fin t) (bank : Fin t ↪ Fin h)
    (S : Stacks h prime) :
    tapeCharge cleanupWeight (frameSlots fan) (embStk bank S) =
      tapeCharge cleanupWeight (frameSlots (fan.trans bank)) S := by
  simp [tapeCharge,frameSlots,List.map_reverse,Function.comp_def,embStk]

/-- Sequence preparation with a worker embedded in the prepared bank.
The preparation allowance covers both the selected tapes and the live frame. -/
theorem runPreparedStage {T H Q k V : ℕ} {P U : Type} (bank : Fin T ↪ Fin H)
    (fan : Fin (k+2) ↪ Fin T) (body : P → Pr P T Q prime U) (worker : Pr P T Q prime U)
    (setup : Pr P H Q prime U) (u v : HS H Q prime U) (S D : Stacks H prime)
    (n setupCost : ℕ) (effect : (Fin k → Fin V → ZMod 2) → Prop)
    (start : Exec (fun f => embProg bank id (body f)) setup (mk u S) n (mk v D))
    (user : v.user = u.user) (paid : CleanupBound S D n setupCost)
    {z F m y} (run : Exec body worker (mk (embDn bank v) (embStk bank D)) m (mk z F))
    (same : z.user = v.user) (done : HelperFan fan y F) (act : effect y) :
    ∃ w G, Exec (fun f => embProg bank id (body f)) (setup.seq (embProg bank id worker))
        (mk u S) (n+m) (mk w G) ∧ w.user = u.user ∧ HelperFan (fan.trans bank) y G ∧ effect y ∧
      ∀ price, (∀ js, js.Nodup →
        m+tapeCharge cleanupWeight (frameSlots fan) F+tapeCharge cleanupWeight js F ≤
          tapeCharge cleanupWeight js (embStk bank D)+price+tapeCharge cleanupWeight (frameSlots fan) (embStk bank D)) →
        ∀ js, js.Nodup →
          n+m+tapeCharge cleanupWeight (frameSlots (fan.trans bank)) G+tapeCharge cleanupWeight js G ≤
          tapeCharge cleanupWeight js S+(2*setupCost+price)+tapeCharge cleanupWeight (frameSlots (fan.trans bank)) S := by
  obtain ⟨w,G,placed,_,last,view,off⟩ := exec_emb (ι := id) (body' := fun f => embProg bank id (body f))
    bank.injective (fun _ => rfl) run v rfl D rfl
  subst F
  refine ⟨w,G,start.seq placed,last.trans (same.trans user),done,act,?_⟩
  intro price bill js nd
  let slots := frameSlots (fan.trans bank)
  have after := placedCleanup_cost_le bank D G cleanupWeight (m+tapeCharge cleanupWeight slots G)
    (price+tapeCharge cleanupWeight slots D) off (fun is unique => by
      simpa only [placedFrameCharge,Nat.add_assoc,slots] using bill is unique) js nd
  have pre := paid js nd
  have frame := paid slots (frameSlots_nodup _)
  change n+tapeCharge cleanupWeight js D ≤ tapeCharge cleanupWeight js S+setupCost at pre
  change n+tapeCharge cleanupWeight slots D ≤ tapeCharge cleanupWeight slots S+setupCost at frame
  change n+m+tapeCharge cleanupWeight slots G+_ ≤ _+_+tapeCharge cleanupWeight slots S
  omega

private theorem cutoffScale_le [M8.Machine.Net] (c : CutoffNodeInput) (σ : ℝ) (nonneg : 0 ≤ σ)
    (positive : 0 < c.cutoff) : (c.cutoff : ℝ)^M8.Machine.BudgetBound.tau ≤
      (c.node.width : ℝ)^σ*(c.cutoff : ℝ)^(M8.Machine.BudgetBound.tau-σ) := by
    have width := Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.cast_le.mpr c.active) nonneg
    have pos : (0 : ℝ) < c.cutoff := by exact_mod_cast positive
    calc
      _ = (c.cutoff : ℝ)^σ*(c.cutoff : ℝ)^(M8.Machine.BudgetBound.tau-σ) := by
        rw [← Real.rpow_add pos,add_sub_cancel ..]
      _ ≤ _ := mul_le_mul_of_nonneg_right width (Real.rpow_nonneg pos.le _)

/-- In the seven-atom stopping band the compact stage executes on its fixed
tapes with no recursive worker supplied by the caller. -/
theorem compactBandStage [M8.Machine.Net] (n : Fin 9) :
    ∃ (T states : ℕ) (fan : Fin (142081+2) ↪ Fin T),
    ∀ {U : Type} {Q : ℕ}, states ≤ Q → ∃ Label : Type,
    let scratch := Fin.castAddEmb LeafCore.small (n := T+273)
    let owner := (Fin.castAddEmb 273 (n := T)).trans scratch
    let stage := Fin.natAddEmb 80 (m := (T+273)+LeafCore.small)
    let H := 80+((T+273)+LeafCore.small)
    let place := Fin.castAddEmb 37 (n := H)
    let outer := Fin.castAddEmb 7 (n := H+37)
    let ext := Fin.natAddEmb (H+37) (m := 7)
    let liveFan := (((fan.trans owner).trans stage).trans place).trans outer
    ∃ (host : Label → Pr Label ((H+37)+7) Q prime U) (code : Pr Label ((H+37)+7) Q prime U) (stageRate : ℝ),
    ∀ c : CutoffNodeInput, 7*(c.w+1) ≤ c.cutoff →
      let w := c.w
      let W := c.stageWidth
      let V := (prime^(w+1))^16*W
      ∀ (x : Fin 142081 → Fin V → ZMod 2) u S, HelperFan ((fan.trans owner).trans stage) x (embStk place (embStk outer S)) →
      (∀ i : Fin 37, (embStk outer S).R (i.natAdd H) = callerHeaderBank (fun j => (Routines.hdr c.node j).map bitSymbol) i) →
      (∀ j, let k := place (archiveSetupPlacement 80 T LeafCore.small j); (embStk outer S).L k = [] ∧ (embStk outer S).R k = []) →
      (∀ j : Fin LeafCore.small, (embStk place (embStk outer S)).L (stage (j.natAdd (T+273))) = [] ∧ (embStk place (embStk outer S)).R (stage (j.natAdd (T+273))) = []) →
      (∀ j, (∀ h, fan h ≠ j) → (embStk place (embStk outer S)).L (stage (owner j)) = [] ∧ (embStk place (embStk outer S)).R (stage (owner j)) = []) →
      S.R (ext 0) = binSyms (prime^(w+1)).size (prime^(w+1)) → S.R (ext 1) = binSyms W.size W →
      S.R (ext 2) = binSyms 1 1 → S.R (ext 3) = binSyms (w+1).size (w+1) →
      S.R (ext 4) = [] → S.R (ext 5) = [] → S.R (ext 6) = binSyms c.root.width.size c.cutoff →
      ∃ z F t y, Exec host code (mk u S) t (mk z F) ∧ z.user = u.user ∧ HelperFan ((fan.trans owner).trans stage) y (embStk place (embStk outer F)) ∧
        RestoredBorrowedStage n (w+1) c.B c.stageFactor x y ∧
        ∀ (σ : ℝ), 0 ≤ σ → ∀ js : List (Fin ((H+37)+7)), js.Nodup →
          t+tapeCharge cleanupWeight (frameSlots liveFan) F+tapeCharge cleanupWeight js F ≤
            tapeCharge cleanupWeight js S+⌊stageRate*((c.node.width : ℝ)^σ*(c.cutoff : ℝ)^(M8.Machine.BudgetBound.tau-σ)*c.cells)⌋₊+
            tapeCharge cleanupWeight (frameSlots liveFan) S := by
  obtain ⟨C,tapes,regs,T,states,fan,build⟩ := compactInitializedStage n
  refine ⟨T,states,fan,?_⟩
  intro U Q cap
  obtain ⟨body,_,host,code,localRate,packRate,run⟩ := build (P := Unit) (U := U) cap
    (fun _ _ _ _ => .act .done) (fun _ _ _ => ())
  refine ⟨Σ _ : Fin 32 × Fin 5, (Σ j, Fin (invocationCounts (selectedPhaseSchedule false).1.length (selectedPhaseSchedule true).1.length j) × Option (WorkerLabel Unit)),?_⟩
  intro scratch owner stage H place outer ext liveFan
  let calls := (stageRuns.flatMap (fun _ => Geometry.Moves.localPaid)).length
  refine ⟨host,code,max 0 packRate+1+localRate+calls*max 0 C,?_⟩
  intro c band w W V
  obtain ⟨pos,geom,execute⟩ := run c
  have stageRun := execute C (fun _ => 0) le_rfl (fun p j i active =>
    False.elim ((not_lt_of_ge ((sweepChildWidth_le c n p _ _ j i).trans band)) active))
  intro x u S live words free empty blank modulus spectator unit atom ht hs cut
  obtain ⟨z,F,t,y,exec,user,ready,act,bill⟩ := stageRun x u S live words free empty blank modulus spectator unit atom ht hs cut
  refine ⟨z,F,t,y,exec,user,ready,act,?_⟩
  intro σ nonneg js nd
  let D := max 0 packRate+1+localRate+calls*max 0 C
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have scale := cutoffScale_le c σ nonneg (by omega)
  apply Nat.le_trans _ (Nat.add_le_add_right (Nat.add_le_add_left (Nat.floor_mono
    (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right scale (Nat.cast_nonneg c.cells)) hD)) _) _)
  dsimp only [D]
  have children := stoppedDirectoryCost c C (List.range' (stageChildStart n) calls)
  rw [List.length_range'] at children
  have total := bandStageBill c (by omega) packRate C localRate calls
  have charge (A : Stacks ((H+37)+7) prime) :
      tapeCharge cleanupWeight (frameSlots fan) (embStk (owner.trans stage) (embStk place (embStk outer A))) =
        tapeCharge cleanupWeight (frameSlots liveFan) A := by
    simp only [placedFrameCharge]
    rfl
  have h := bill js nd
  rw [charge,charge] at h
  rw [show (prime^(c.w+1))^16*c.stageWidth = c.cells from c.stageCells] at h
  dsimp only [calls] at children total ⊢
  dsimp only [owner,stage,scratch,outer,place,H] at *
  omega

noncomputable def compactHeaderSeed (c : CutoffNodeInput) : Stacks 37 prime :=
  ⟨[],[],fun _ => [],callerHeaderBank (fun j => (Routines.hdr c.node j).map bitSymbol)⟩

/-- Populate the compact descriptor bank directly from the caller's node
words. The remaining thirty-one tapes, including both copy registers, end blank. -/
theorem compactSweepHeaderLoader :
    LoadsPackedSeed sweepSeedWords CutoffNodeInput.cells compactHeaderSeed := by
  classical
  let field (j : Fin 6) : Fin 10 := (j.castAdd 3).succ
  have read (c : CutoffNodeInput) (j : Fin 6) :
      sweepSeedWords c (field j) = (Routines.hdr c.node j).map bitSymbol := by
    simp only [field,sweepSeedWords,Fin.cons_succ]
    exact congrFun (parentArchiveSeed_words c.node c.w) (j.castAdd 3) |>.trans (Fin.addCases_left ..)
  let tmp : Fin 37 := 6
  let saved : Fin 37 := 7
  have away (j : Fin 6) : callerHeaderPorts j ≠ tmp ∧ callerHeaderPorts j ≠ saved := by
    constructor <;> intro h <;> have v := congrArg Fin.val h
    · change j.val = 6 at v
      omega
    · change j.val = 7 at v
      omega
  have load := LoadsPackedSeed.headers sweepSeedWords CutoffNodeInput.cells callerHeaderPorts field tmp saved
    (by decide) (fun j => (away j).1) (fun j => (away j).2) (133*142080) (by
      intro c
      simp only [read]
      have pos : 0 < c.cells := Nat.mul_pos (pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _)
        (Nat.mul_pos c.idlePositive (by decide))
      have h := descriptorSeedBill c.node (c.cells_share ▸ Nat.mul_pos pos (by decide))
      rw [← c.cells_share] at h
      exact h.trans_eq (by ring))
  convert load using 1
  funext c
  unfold compactHeaderSeed
  congr 1
  funext j
  by_cases h : j.val < 6
  · let i : Fin 6 := ⟨j.val,h⟩
    have atPort := callerHeaderPorts.injective.extend_apply (fun i => sweepSeedWords c (field i))
      (fun _ => []) i
    change Function.extend _ _ _ j = _ at atPort
    rw [atPort,read]
    exact dite_eq_left h
  · have off : ¬ ∃ i, callerHeaderPorts i = j := by
      rintro ⟨i,rfl⟩
      exact h i.isLt
    rw [Function.extend_apply' _ _ _ off]
    exact dite_eq_right h

theorem compactHeaderSeed_load :
    LoadsPackedSeed nodeSeedWords CutoffNodeInput.cells compactHeaderSeed :=
  nodeSweepLoader id compactSweepHeaderLoader

/-- The common sweep record can be installed on any ten private ports.
Two other tapes in the bank serve as the copy registers. -/
theorem compactSweepRecordLoader {T : ℕ} (ports : Fin 10 ↪ Fin T) (tmp saved : Fin T)
    (distinct : tmp ≠ saved) (ht : ∀ i, ports i ≠ tmp) (hs : ∀ i, ports i ≠ saved) :
    LoadsPackedSeed nodeSeedWords CutoffNodeInput.cells (fun c => ⟨[],[],fun _ => [],
      Function.extend ports (sweepSeedWords c) (fun _ => [])⟩) := by
  apply nodeSweepLoader id (seed := fun c => ⟨[],[],fun _ => [],Function.extend ports (sweepSeedWords c) (fun _ => [])⟩)
  apply LoadsPackedSeed.headers sweepSeedWords CutoffNodeInput.cells ports id tmp saved distinct ht hs
    (133*142080+65+142)
  intro c
  have archive := archiveSeedLoadCost c
  have cutoff := c.remainderSetup_le 1
  have bill : seedLoadBill (fun i => sweepSeedWords c (id i)) =
      8*c.root.width.size+6+seedLoadBill (fun i => (parentArchiveSeed c.node c.w).R (parentArchivePorts i)) := by
    unfold seedLoadBill
    rw [Fin.sum_univ_succ]
    simp only [id_eq,sweepSeedWords,Fin.cons_zero,Fin.cons_succ,length_binSyms,Nat.add_assoc]
  rw [bill,Nat.add_mul]
  omega

noncomputable def compactDimensionSeed (c : CutoffNodeInput) : Stacks 7 prime :=
  let M := prime^(c.w+1)
  let W := c.stageWidth
  ⟨[],[],fun _ => [],![binSyms M.size M,binSyms W.size W,binSyms 1 1,binSyms (c.w+1).size (c.w+1),
    [],[],binSyms c.root.width.size c.cutoff]⟩

/-- The inner correction chart and the compact stage use the same four
dimension words. The cutoff occupies the seventh tape, outside the chart. -/
theorem prepareCompactDimensions {P U : Type} {H Q : ℕ} (body : P → Pr P H Q prime U)
    (archive : Fin (80+273) ↪ Fin H) (outer : Fin 6 ↪ Fin H) (dims : Fin 7 ↪ Fin H)
    (capacity : (fun {q : ℕ} (_ : Program 38 q prime) => q) (RecursiveRowsNodeHeaders.program 142080) ≤ Q)
    (outerOff : ∀ i j, outer i ≠ archive j) (dimsOff : ∀ i j, dims i ≠ archive j)
    (apart : ∀ i j, outer i ≠ dims j) :
    ∃ code rate, ∀ (c : CutoffNodeInput) u S,
      ParentArchiveInput c.node c.w (embStk archive S) →
      (∀ i, S.R (outer i) = []) → (∀ i : Fin 6, S.R (dims (i.castAdd 1)) = []) →
      S.R (dims 6) = binSyms c.root.width.size c.cutoff →
      ∃ z F t, Exec body code (mk u S) t (mk z F) ∧ z.user = u.user ∧ CleanupBound S F t (rate*c.cells) ∧
        (∀ i, F.R (dims i) = (compactDimensionSeed c).R i) ∧
        (∀ i : Fin 4, F.R (outer (i.castAdd 2)) =
          stageChartWords (c.w+1) (c.idleWidth*142080) false i) ∧
        ∀ j, (∀ i, archive i ≠ j) → (∀ i, outer i ≠ j) → (∀ i, dims i ≠ j) →
          F.L j = S.L j ∧ F.R j = S.R j := by
  let inner := (Fin.castAddEmb 1 (n := 6)).trans dims
  obtain ⟨code,rate,prepare⟩ := parentStageChartCallers body archive outer inner capacity outerOff
    (fun i => dimsOff _) (fun i j => apart i _)
  refine ⟨code,rate,?_⟩
  intro c u S ready clear blank cutoff
  obtain ⟨z,F,t,exec,user,paid,flat,owned,scratch,frame⟩ := prepare c u S ready clear blank
  rw [c.stageCells] at paid
  refine ⟨z,F,t,exec,user,paid,?_,?_,fun j a b d => frame j a (fun i => b _) (fun i => d _)⟩
  · let W := c.B*prime^(64*((c.w+1)*64))*c.stageFactor
    have suffix : (prime^(c.w+1))^112*W = c.stageWidth := by simp only [W,CutoffNodeInput.stageWidth,Nat.mul_assoc]
    have kept := frame (dims 6) (fun j => (dimsOff 6 j).symm) (fun i => apart _ _)
      (fun i => dims.injective.ne (by fin_cases i <;> decide))
    have spectator : F.R (dims 1) = binSyms c.stageWidth.size c.stageWidth := by
      rw [← suffix]
      exact owned 1
    intro i
    fin_cases i <;> first | exact owned 0 | exact spectator | exact owned 2 | exact owned 3 |
      exact (scratch 0).2 | exact (scratch 1).2 | exact kept.2.trans cutoff
  · simpa only [c.stageTail] using flat

/-- Read the node fields with the cutoff already on the seventh dimension tape.
The archive is private scratch and starts empty. -/
theorem loadCompactDimensions {P U : Type} {H Q : ℕ} (body : P → Pr P H Q prime U)
    (archive : Fin (80+273) ↪ Fin H) (outer : Fin 6 ↪ Fin H) (dims : Fin 7 ↪ Fin H)
    (source : Fin 9 → Fin H) (away : ∀ i j, archive i ≠ source j)
    (capacity : (fun {q : ℕ} (_ : Program 38 q prime) => q) (RecursiveRowsNodeHeaders.program 142080) ≤ Q)
    (outerOff : ∀ i j, outer i ≠ archive j) (dimsOff : ∀ i j, dims i ≠ archive j)
    (apart : ∀ i j, outer i ≠ dims j) :
    ∃ code rate, ∀ (c : CutoffNodeInput) u S,
      (∀ i, S.R (source i) = sweepSeedWords c i.succ) →
      (∀ i, S.L (archive i) = [] ∧ S.R (archive i) = []) →
      (∀ i, S.R (outer i) = []) → (∀ i : Fin 6, S.R (dims (i.castAdd 1)) = []) →
      S.R (dims 6) = sweepSeedWords c 0 →
      ∃ z F t, Exec body code (mk u S) t (mk z F) ∧ z.user = u.user ∧ CleanupBound S F t (rate*c.cells) ∧
        (∀ i, F.R (dims i) = (compactDimensionSeed c).R i) ∧
        (∀ i : Fin 4, F.R (outer (i.castAdd 2)) =
          stageChartWords (c.w+1) (c.idleWidth*142080) false i) ∧
        ∀ j, (∀ i, archive i ≠ j) → (∀ i, outer i ≠ j) → (∀ i, dims i ≠ j) →
          F.L j = S.L j ∧ F.R j = S.R j := by
  have regs i : [source i,archive (parentArchivePorts i),archive 0,archive 1].Nodup := by
    have zero := (by decide : ∀ i, parentArchivePorts i ≠ 0) i
    have one := (by decide : ∀ i, parentArchivePorts i ≠ 1) i
    simp [List.nodup_cons,fun j => (away j i).symm,archive.injective.eq_iff,zero,one]
  obtain ⟨a,load⟩ := loadParentArchiveSeed body archive source (archive 0) (archive 1)
    (fun i j => away _ _) regs
  obtain ⟨b,rate,prepare⟩ := prepareCompactDimensions body archive outer dims capacity outerOff dimsOff apart
  refine ⟨a.seq b,(133*142080+65)+rate,?_⟩
  intro c u S words vacant clear blank cutoff
  obtain ⟨v,D,n,start,user,price,stored,keep⟩ := load c.node c.w u S words vacant (vacant 0).2 (vacant 1).2
  have ready : ParentArchiveInput c.node c.w (embStk archive D) :=
    parentInput_congr (funext (fun i => (stored i).1.symm)) (funext (fun i => (stored i).2.symm))
      (parentArchiveSeed_ready c.node c.w)
  obtain ⟨z,F,m,finish,last,bill,dim,flat,frame⟩ := prepare c v D ready
    (fun i => (keep _ (fun j => (outerOff i j).symm)).2.trans (clear i))
    (fun i => (keep _ (fun j => (dimsOff _ j).symm)).2.trans (blank i))
    ((keep _ (fun j => (dimsOff 6 j).symm)).2.trans cutoff)
  refine ⟨z,F,n+m,start.seq finish,last.trans user,?_,dim,flat,?_⟩
  · intro js nd
    apply ((price.seq bill) js nd).trans
    rw [Nat.add_mul]
    exact Nat.add_le_add_left (Nat.add_le_add_right (archiveSeedLoadCost c) _) _
  · intro j ar out d
    exact ⟨(frame j ar out d).1.trans (keep j ar).1,(frame j ar out d).2.trans (keep j ar).2⟩

/-- Install the descriptor and dimension words read by the stage worker.
The caller places its cutoff on the last dimension tape. -/
theorem loadCompactStageInputs {P U : Type} {H Q : ℕ} (body : P → Pr P H Q prime U)
    (archive : Fin (80+273) ↪ Fin H) (outer : Fin 6 ↪ Fin H) (dims : Fin 7 ↪ Fin H)
    (header : Fin 37 ↪ Fin H) (source : Fin 10 → Fin H) (cut : source 0 = dims 6)
    (capacity : (fun {q : ℕ} (_ : Program 38 q prime) => q) (RecursiveRowsNodeHeaders.program 142080) ≤ Q)
    (outerOff : ∀ i j, outer i ≠ archive j) (dimsOff : ∀ i j, dims i ≠ archive j)
    (apart : ∀ i j, outer i ≠ dims j) (away : ∀ i j, archive i ≠ source j)
    (ha : ∀ i j, header i ≠ archive j) (ho : ∀ i j, header i ≠ outer j)
    (hd : ∀ i j, header i ≠ dims j) (hs : ∀ i j, header i ≠ source j) :
    ∃ code rate, ∀ (c : CutoffNodeInput) u S, (∀ i, S.R (source i) = sweepSeedWords c i) →
      (∀ i, S.L (header i) = [] ∧ S.R (header i) = []) →
      (∀ i, S.L (archive i) = [] ∧ S.R (archive i) = []) →
      (∀ i, S.R (outer i) = []) → (∀ i : Fin 6, S.R (dims (i.castAdd 1)) = []) →
      ∃ z F t, Exec body code (mk u S) t (mk z F) ∧ z.user = u.user ∧ CleanupBound S F t (rate*c.cells) ∧
        (∀ i, F.R (header i) = (compactHeaderSeed c).R i) ∧
        (∀ i, F.R (dims i) = (compactDimensionSeed c).R i) ∧
        (∀ i : Fin 4, F.R (outer (i.castAdd 2)) = stageChartWords (c.w+1) (c.idleWidth*142080) false i) ∧
        ∀ j, (∀ i, header i ≠ j) → (∀ i, archive i ≠ j) → (∀ i, outer i ≠ j) → (∀ i, dims i ≠ j) →
          F.L j = S.L j ∧ F.R j = S.R j := by
  obtain ⟨r,compile⟩ := compactSweepHeaderLoader
  obtain ⟨a,load⟩ := compile body header source hs
  obtain ⟨b,v,prepare⟩ := loadCompactDimensions body archive outer dims (source ∘ Fin.succ)
    (fun i j => away i _) capacity outerOff dimsOff apart
  refine ⟨a.seq b,r+v,?_⟩
  intro c u S words free vacant clear blank
  obtain ⟨p,D,n,start,user,paid,set,keep⟩ := load c u S words free
  have read i := (keep (source i) (fun j => hs j i)).2.trans (words i)
  obtain ⟨z,F,m,finish,last,bill,dim,flat,frame⟩ := prepare c p D
    (fun i => read i.succ)
    (fun i => ⟨(keep _ (fun j => ha j i)).1.trans (vacant i).1,(keep _ (fun j => ha j i)).2.trans (vacant i).2⟩)
    (fun i => (keep _ (fun j => ho j i)).2.trans (clear i))
    (fun i => (keep _ (fun j => hd j _)).2.trans (blank i))
    (by rw [← cut]; exact read 0)
  refine ⟨z,F,n+m,start.seq finish,last.trans user,?_,?_,dim,flat,?_⟩
  · simpa only [Nat.add_mul] using paid.seq bill
  · intro i
    exact (frame _ (fun j => (ha i j).symm) (fun j => (ho i j).symm) (fun j => (hd i j).symm)).2.trans (set i).2
  · intro j h ar out d
    exact ⟨(frame j ar out d).1.trans (keep j h).1,(frame j ar out d).2.trans (keep j h).2⟩

/-- Place the preparation workspace beyond the worker's tapes. All tapes of
the stage core, including its live data and its scratch, survive preparation. -/
theorem prepareCompactWorker (H : ℕ) {P U : Type} {Q : ℕ}
    (body : P → Pr P (((H+37)+7)+(353+6+9)) Q prime U)
    (capacity : (fun {q : ℕ} (_ : Program 38 q prime) => q) (RecursiveRowsNodeHeaders.program 142080) ≤ Q) :
    let bank := Fin.castAddEmb (353+6+9) (n := (H+37)+7)
    let core := ((Fin.castAddEmb 37 (n := H)).trans (Fin.castAddEmb 7)).trans bank
    let header := ((Fin.natAddEmb H (m := 37)).trans (Fin.castAddEmb 7)).trans bank
    let dims := (Fin.natAddEmb (H+37) (m := 7)).trans bank
    let extra := Fin.natAddEmb ((H+37)+7) (m := 353+6+9)
    let archive := ((Fin.castAddEmb 6 (n := 353)).trans (Fin.castAddEmb 9)).trans extra
    let outer := ((Fin.natAddEmb 353 (m := 6)).trans (Fin.castAddEmb 9)).trans extra
    let source := Fin.cons (α := fun _ : Fin 10 => Fin (((H+37)+7)+(353+6+9))) (dims 6)
      ((Fin.natAddEmb (353+6) (m := 9)).trans extra)
    ∃ code rate, ∀ (c : CutoffNodeInput) u S, (∀ i, S.R (source i) = sweepSeedWords c i) →
      (∀ i, S.L (header i) = [] ∧ S.R (header i) = []) →
      (∀ i, S.L (archive i) = [] ∧ S.R (archive i) = []) →
      (∀ i, S.R (outer i) = []) → (∀ i : Fin 6, S.R (dims (i.castAdd 1)) = []) →
      ∃ z F t, Exec body code (mk u S) t (mk z F) ∧ z.user = u.user ∧ CleanupBound S F t (rate*c.cells) ∧
        (∀ i, F.R (header i) = (compactHeaderSeed c).R i) ∧
        (∀ i, F.R (dims i) = (compactDimensionSeed c).R i) ∧
        (∀ i : Fin 4, F.R (outer (i.castAdd 2)) = stageChartWords (c.w+1) (c.idleWidth*142080) false i) ∧
        ∀ i, F.L (core i) = S.L (core i) ∧ F.R (core i) = S.R (core i) := by
  intro bank core header dims extra archive outer source
  have separate {a b : ℕ} {f : Fin a ↪ Fin (((H+37)+7)+(353+6+9))} {g : Fin b ↪ Fin (((H+37)+7)+(353+6+9))}
      (h : ∀ i j, (f i).val ≠ (g j).val) (i) (j) : f i ≠ g j := fun eq => h i j (congrArg Fin.val eq)
  obtain ⟨code,rate,run⟩ := loadCompactStageInputs body archive outer dims header source rfl capacity
    (by apply separate; intro i j; change ((H+37)+7)+(353+i.val) ≠ ((H+37)+7)+j.val; omega)
    (by apply separate; intro i j; change H+37+i.val ≠ ((H+37)+7)+j.val; omega)
    (by apply separate; intro i j; change ((H+37)+7)+(353+i.val) ≠ H+37+j.val; omega)
    (by intro i j; induction j using Fin.cases <;> intro eq <;> have h := congrArg Fin.val eq
        · change ((H+37)+7)+i.val = H+37+6 at h; omega
        · rename_i j; change ((H+37)+7)+i.val = ((H+37)+7)+(359+j.val) at h; omega)
    (by apply separate; intro i j; change H+i.val ≠ ((H+37)+7)+j.val; omega)
    (by apply separate; intro i j; change H+i.val ≠ ((H+37)+7)+(353+j.val); omega)
    (by apply separate; intro i j; change H+i.val ≠ H+37+j.val; omega)
    (by intro i j; induction j using Fin.cases <;> intro eq <;> have h := congrArg Fin.val eq
        · change H+i.val = H+37+6 at h; omega
        · rename_i j; change H+i.val = ((H+37)+7)+(359+j.val) at h; omega)
  refine ⟨code,rate,?_⟩
  intro c u S words free vacant clear blank
  obtain ⟨z,F,t,exec,user,paid,heads,dimensions,flat,keep⟩ := run c u S words free vacant clear blank
  refine ⟨z,F,t,exec,user,paid,heads,dimensions,flat,fun i => keep _ ?_ ?_ ?_ ?_⟩
  all_goals intro j eq; have h := congrArg Fin.val eq
  · change H+j.val = i.val at h; omega
  · change ((H+37)+7)+j.val = i.val at h; omega
  · change ((H+37)+7)+(353+j.val) = i.val at h; omega
  · change H+37+j.val = i.val at h; omega

private theorem owner_ne_scratch {T L : ℕ} (i : Fin T) (j : Fin L) :
    ((i.castAdd 273).castAdd L).natAdd 80 ≠ (j.natAdd (T+273)).natAdd 80 := by
  intro h
  have v := congrArg Fin.val h
  change 80+i.val = 80+(T+273+j.val) at v
  omega

/-- Execute a stopping-band stage directly from the node record and live data. -/
theorem preparedCompactBandStage [M8.Machine.Net] (n : Fin 9) :
    ∃ (H states : ℕ) (fan : Fin (142081+2) ↪ Fin H),
    let bank := Fin.castAddEmb (353+6+9) (n := (H+37)+7)
    let core := ((Fin.castAddEmb 37 (n := H)).trans (Fin.castAddEmb 7)).trans bank
    let header := ((Fin.natAddEmb H (m := 37)).trans (Fin.castAddEmb 7)).trans bank
    let dims := (Fin.natAddEmb (H+37) (m := 7)).trans bank
    let extra := Fin.natAddEmb ((H+37)+7) (m := 353+6+9)
    let archive := ((Fin.castAddEmb 6 (n := 353)).trans (Fin.castAddEmb 9)).trans extra
    let outer := ((Fin.natAddEmb 353 (m := 6)).trans (Fin.castAddEmb 9)).trans extra
    let source := Fin.cons (α := fun _ : Fin 10 => Fin (((H+37)+7)+(353+6+9))) (dims 6)
      ((Fin.natAddEmb (353+6) (m := 9)).trans extra)
    ∀ {U : Type} {Q : ℕ}, states ≤ Q →
    ∃ (P : Type) (host : P → Pr P (((H+37)+7)+(353+6+9)) Q prime U) (code : Pr P (((H+37)+7)+(353+6+9)) Q prime U) (rate : ℕ) (stageRate : ℝ),
      ∀ (c : CutoffNodeInput), 7*(c.w+1) ≤ c.cutoff →
      ∀ (x : Fin 142081 → Fin ((prime^(c.w+1))^16*c.stageWidth) → ZMod 2) u S,
      HelperFan (fan.trans core) x S → (∀ i, (∀ j, fan j ≠ i) → S.L (core i) = [] ∧ S.R (core i) = []) →
      (∀ i, S.R (source i) = sweepSeedWords c i) →
      (∀ i, S.L (header i) = [] ∧ S.R (header i) = []) →
      (∀ i, S.L (archive i) = [] ∧ S.R (archive i) = []) →
      (∀ i, S.R (outer i) = []) → (∀ i : Fin 6, S.R (dims (i.castAdd 1)) = []) →
      ∃ z F t y, Exec host code (mk u S) t (mk z F) ∧ z.user = u.user ∧ HelperFan (fan.trans core) y F ∧
        RestoredBorrowedStage n (c.w+1) c.B c.stageFactor x y ∧
        ∀ σ : ℝ, 0 ≤ σ → ∀ js, js.Nodup →
          t+tapeCharge cleanupWeight (frameSlots (fan.trans core)) F+tapeCharge cleanupWeight js F ≤
          tapeCharge cleanupWeight js S+(rate*c.cells+
            ⌊stageRate*((c.node.width : ℝ)^σ*(c.cutoff : ℝ)^(M8.Machine.BudgetBound.tau-σ)*c.cells)⌋₊)+
            tapeCharge cleanupWeight (frameSlots (fan.trans core)) S := by
  obtain ⟨T,q,localFan,build⟩ := compactBandStage n
  generalize _h : LeafCore.small = L at build
  let H := 80+((T+273)+L)
  let owner := ((Fin.castAddEmb 273 (n := T)).trans (Fin.castAddEmb L)).trans (Fin.natAddEmb 80)
  let fan := localFan.trans owner
  refine ⟨H,max q ((fun {q : ℕ} (_ : Program 38 q prime) => q) (RecursiveRowsNodeHeaders.program 142080)),fan,?_⟩
  intro bank core header dims extra archive outer source U Q fits
  obtain ⟨P,body,worker,price,run⟩ := build (U := U) ((le_max_left ..).trans fits)
  let host := fun f => embProg bank id (body f)
  obtain ⟨setup,r,prepare⟩ := prepareCompactWorker H host ((le_max_right ..).trans fits)
  refine ⟨P,host,setup.seq (embProg bank id worker),2*r,price,?_⟩
  intro c band x u S live free words vacant clean clear blank
  obtain ⟨v,D,a,start,user,paid,heads,dim,_,keep⟩ := prepare c u S words vacant clean clear blank
  have ready : HelperFan (fan.trans core) x D := by
    intro i j
    change _ = readAt _ (D.L (core (fan i))) (D.R (core (fan i))) _
    rw [(keep _).1,(keep _).2]
    exact live i j
  have empty i (away : ∀ j, fan j ≠ i) :=
    And.intro ((keep i).1.trans (free i away).1) ((keep i).2.trans (free i away).2)
  obtain ⟨z,F,m,y,exec,same,done,act,bill⟩ := run c band x (embDn bank v) (embStk bank D) ready heads
    (fun j => empty _ (fun i => ((archiveSetupPlacement_frame j).1 (localFan i)).symm))
    (fun j => empty _ (fun i => owner_ne_scratch (localFan i) j))
    (fun j away => empty _ (fun i h => away i (owner.injective h)))
    (dim 0) (dim 1) (dim 2) (dim 3) (dim 4) (dim 5) (dim 6)
  let inside := (fan.trans (Fin.castAddEmb 37)).trans (Fin.castAddEmb 7)
  obtain ⟨w,G,placed,last,out,action,cost⟩ := runPreparedStage bank inside body worker setup u v S D a (r*c.cells)
    (RestoredBorrowedStage n (c.w+1) c.B c.stageFactor x) start user paid exec same done act
  refine ⟨w,G,a+m,y,placed,last,out,action,?_⟩
  intro σ nonneg js nd
  have ports : inside.trans bank = fan.trans core := by ext i; rfl
  simpa only [ports,Nat.mul_assoc] using cost _ (bill σ nonneg) js nd

/-- The packed caller supplies a single private-tape seed for each node.
The worker and its live tape placement are independent of that node. -/
theorem seededCompactBandStage [M8.Machine.Net] (n : Fin 9) :
    ∃ (T states : ℕ) (fan : Fin (142081+2) ↪ Fin T), ∀ {U : Type} {Q : ℕ}, states ≤ Q →
      ∃ (Label : Type) (host : Label → Pr Label T Q prime U) (code : Pr Label T Q prime U) (rate : ℝ),
      ∃ seed : CutoffNodeInput → Stacks T prime,
      LoadsPackedSeed nodeSeedWords CutoffNodeInput.cells seed ∧
      ∀ c : CutoffNodeInput, 7*(c.w+1) ≤ c.cutoff →
      ∀ (x : Fin 142081 → Fin ((prime^(c.w+1))^16*c.stageWidth) → ZMod 2) u S, HelperFan fan x S →
      (∀ j, (∀ i, fan i ≠ j) → S.L j = (seed c).L j ∧ S.R j = (seed c).R j) →
      ∃ z F t y, Exec host code (mk u S) t (mk z F) ∧ z.user = u.user ∧ HelperFan fan y F ∧
        RestoredBorrowedStage n (c.w+1) c.B c.stageFactor x y ∧
        ∀ σ : ℝ, 0 ≤ σ → ∀ js : List _, js.Nodup →
          t+tapeCharge cleanupWeight (frameSlots fan) F+tapeCharge cleanupWeight js F ≤
          tapeCharge cleanupWeight js S+⌊rate*((c.node.width : ℝ)^σ*(c.cutoff : ℝ)^(M8.Machine.BudgetBound.tau-σ)*c.cells)⌋₊+
            tapeCharge cleanupWeight (frameSlots fan) S := by
  classical
  obtain ⟨H,q,fan,build⟩ := preparedCompactBandStage n
  let T := ((H+37)+7)+(353+6+9)
  let core := ((Fin.castAddEmb 37 (n := H)).trans (Fin.castAddEmb 7)).trans (Fin.castAddEmb (353+6+9))
  let ports : Fin 10 ↪ Fin T := ⟨Fin.cons (α := fun _ : Fin 10 => Fin T)
    ⟨H+43,by dsimp [T]; omega⟩ (fun i : Fin 9 => ⟨H+403+i.val,by dsimp [T]; omega⟩),by
      intro i j eq
      induction i using Fin.cases <;> induction j using Fin.cases
      · rfl
      · rename_i j; have h := congrArg Fin.val eq; change H+43 = H+403+j.val at h; omega
      · rename_i i; have h := congrArg Fin.val eq; change H+403+i.val = H+43 at h; omega
      · rename_i i j; have h := congrArg Fin.val eq; change H+403+i.val = H+403+j.val at h
        exact congrArg Fin.succ (Fin.ext (by omega))⟩
  have off (j : Fin T) (lo : j.val < H+403) (cut : j.val ≠ H+43) : ∀ i, ports i ≠ j := by
    intro i eq
    have h := congrArg Fin.val eq
    induction i using Fin.cases with
    | zero => exact cut h.symm
    | succ i => change H+403+i.val = j.val at h; omega
  let seed (c : CutoffNodeInput) : Stacks T prime := ⟨[],[],fun _ => [],
    Function.extend ports (sweepSeedWords c) (fun _ => [])⟩
  have loader : LoadsPackedSeed nodeSeedWords CutoffNodeInput.cells seed :=
    compactSweepRecordLoader ports ⟨H,by dsimp [T]; omega⟩ ⟨H+1,by dsimp [T]; omega⟩
      (fun eq => by have h := congrArg Fin.val eq; dsimp at h; omega)
      (off _ (by dsimp; omega) (by dsimp; omega)) (off _ (by dsimp; omega) (by dsimp; omega))
  refine ⟨T,q,fan.trans core,?_⟩
  intro U Q fits
  obtain ⟨Label,host,code,r,rate,run⟩ := build (U := U) fits
  refine ⟨Label,host,code,r+max 0 rate,seed,loader,?_⟩
  intro c band x u S live fresh
  have clear (j : Fin T) (away : ∀ i, core (fan i) ≠ j) (lo : j.val < H+403) (cut : j.val ≠ H+43) :
      S.L j = [] ∧ S.R j = [] := by
    obtain ⟨l,right⟩ := fresh j away
    exact ⟨l,right.trans (Function.extend_apply' (sweepSeedWords c) (fun _ => []) j (fun ⟨i,h⟩ => off j lo cut i h))⟩
  have above (j : Fin T) (h : H ≤ j.val) : ∀ i, core (fan i) ≠ j := by
    intro i eq
    have v := congrArg Fin.val eq
    change (fan i).val = j.val at v
    omega
  have words i : S.R (ports i) = sweepSeedWords c i := by
    have high : H ≤ (ports i).val := by
      induction i using Fin.cases with
      | zero => change H ≤ H+43; omega
      | succ i => change H ≤ H+403+i.val; omega
    exact (fresh _ (above _ high)).2.trans (ports.injective.extend_apply (sweepSeedWords c) (fun _ => []) i)
  obtain ⟨z,F,t,y,exec,user,out,act,bill⟩ := run c band x u S live
    (fun i away => clear _ (fun j h => away j (core.injective h)) (by change i.val < _; omega)
      (by change i.val ≠ _; omega))
    (fun i => by
      apply Eq.trans _ (words i)
      apply congrArg S.R
      apply Fin.ext
      induction i using Fin.cases with
      | zero => change H+37+6 = H+43; omega
      | succ j => change H+37+7+(359+j.val) = H+403+j.val; omega)
    (fun i => clear _ (above _ (by change H ≤ H+i.val; omega)) (by change H+i.val < _; omega) (by change H+i.val ≠ _; omega))
    (fun i => clear _ (above _ (by change H ≤ H+37+7+i.val; omega)) (by change H+37+7+i.val < _; omega)
      (by change H+37+7+i.val ≠ _; omega))
    (fun i => (clear _ (above _ (by change H ≤ H+37+7+(353+i.val); omega)) (by change H+37+7+(353+i.val) < _; omega)
      (by change H+37+7+(353+i.val) ≠ _; omega)).2)
    (fun i => (clear _ (above _ (by change H ≤ H+37+i.val; omega)) (by change H+37+i.val < _; omega)
      (by change H+37+i.val ≠ _; omega)).2)
  refine ⟨z,F,t,y,exec,user,out,act,?_⟩
  intro σ nonneg js nd
  let scale := (c.node.width : ℝ)^σ*(c.cutoff : ℝ)^(M8.Machine.BudgetBound.tau-σ)*c.cells
  have cut : 1 ≤ c.cutoff := by omega
  have unit := (Real.one_le_rpow (by exact_mod_cast cut : (1 : ℝ) ≤ c.cutoff)
    M8.Machine.BudgetBound.exponent_range.1.le).trans (cutoffScale_le c σ nonneg (by omega))
  have vol : (c.cells : ℝ) ≤ scale := le_mul_of_one_le_left (Nat.cast_nonneg _) unit
  have scalePos := (Nat.cast_nonneg c.cells (α := ℝ)).trans vol
  have price : r*c.cells+⌊rate*scale⌋₊ ≤ ⌊(r+max 0 rate)*scale⌋₊ := by
    apply Nat.le_floor
    push_cast
    rw [add_mul]
    exact add_le_add (mul_le_mul_of_nonneg_left vol (Nat.cast_nonneg _)) ((Nat.cast_le.mpr
      (Nat.floor_mono (mul_le_mul_of_nonneg_right (le_max_right 0 rate) scalePos))).trans
      (Nat.floor_le (mul_nonneg (le_max_left ..) scalePos)))
  exact (bill σ nonneg js nd).trans (Nat.add_le_add_right (Nat.add_le_add_left price _) _)

theorem CutoffNodeInput.sweepVolume (c : CutoffNodeInput) :
    (prime^(c.w+1))^128*(c.B*prime^(64*((c.w+1)*64))*c.stageFactor) =
    (prime^(c.w+1))^16*c.stageWidth := by
  rw [← ordinaryCompact_width]
  simp [CutoffNodeInput.stageWidth,Nat.mul_assoc]

private theorem correctedSweepRead {w B K : ℕ} (n : Fin 9)
    (size : (prime^w)^128*(B*prime^(64*(w*64))*K) = (prime^w)^16*((prime^w)^112*B*prime^(64*(w*64))*K))
    (x y : Fin 142081 → Fin ((prime^w)^16*((prime^w)^112*B*prime^(64*(w*64))*K)) → ZMod 2)
    (action : ∀ b t g, borrowedStageRead n b t g y = (Piece.stage n).run (borrowedStageRead n b t g x)) :
    ∀ j, sweepRoles n 0 j (sweepView size y) = (Piece.stage n).run (sweepRoles n 0 j (sweepView size x)) := by
  intro j
  obtain ⟨b,g,t,rfl⟩ := borrowedSpectator_covers j
  have read (data : Fin 142081 → Fin _ → ZMod 2) :
      sweepRoles n 0 (borrowedSpectator b g t) (sweepView size data) = borrowedStageRead n b t g data := by
    rw [borrowedStageRead_eq_sweepRoles]
    rfl
  exact (read y).trans ((action b t g).trans (congrArg (Piece.stage n).run (read x).symm))

/-- Run both port corrections from the six prepared dimension tapes, retaining the
inner worker's record loader and the live-frame allowance. -/
theorem placedCorrectedCompactStage [M8.Machine.Net] (n : Fin 9) :
    ∃ (t states space : ℕ) (fan : Fin (142081+2) ↪ Fin t), ∀ {U : Type} {Q : ℕ}, states ≤ Q →
      ∃ (P : Type) (body : P → Pr P t Q prime U) (seed : CutoffNodeInput → Stacks t prime),
      LoadsPackedSeed nodeSeedWords CutoffNodeInput.cells seed ∧
      ∀ {T K : ℕ} (mid : Fin t ↪ Fin T) (entry ret : Fin (rowSwapBlock.tapes+35) ↪ Fin T) (caller : Fin 6 ↪ Fin T),
      let outer := mid.trans (Fin.castAddEmb (24+K))
      let live := fan.trans outer
      space ≤ K → (∀ i j, entry i ≠ mid j) → (∀ i j, ret i ≠ mid j) →
      (∀ i j, caller i ≠ mid j) → (∀ i j, entry i ≠ caller j) →
      (∀ i j, ret i ≠ caller j) → (∀ i j, ret i ≠ entry j) →
      ∃ (code : Pr P (T+(24+K)) Q prime U) (rate coreRate : ℕ) (stageRate : ℝ),
      ∀ (c : CutoffNodeInput), 7*(c.w+1) ≤ c.cutoff → ∀ σ : ℝ, 0 ≤ σ →
      ∀ (x : Fin 142081 → Fin ((prime^(c.w+1))^16*c.stageWidth) → ZMod 2) u S, HelperFan live x S →
      (∀ j, (∀ i, fan i ≠ j) → S.L (outer j) = (seed c).L j ∧ S.R (outer j) = (seed c).R j) →
      (∀ i : Fin 6, S.R ((caller i).castAdd _) = (compactDimensionSeed c).R (i.castAdd 1)) →
      (∀ i, i.val ≠ 24 → S.L ((entry i).castAdd _) = [] ∧ S.R ((entry i).castAdd _) = []) →
      (∀ i, i.val ≠ 24 → S.L ((ret i).castAdd _) = [] ∧ S.R ((ret i).castAdd _) = []) →
      (∀ j : Fin (24+K), S.L (j.natAdd T) = [] ∧ S.R (j.natAdd T) = []) →
      ∃ z F m y, Exec (fun f => embProg outer id (body f)) code (mk u S) m (mk z F) ∧
        z.user = u.user ∧ HelperFan live y F ∧
        (∀ j, sweepRoles n 0 j (sweepView c.sweepVolume y) = (Piece.stage n).run (sweepRoles n 0 j (sweepView c.sweepVolume x))) ∧
        ∀ js, js.Nodup → m+tapeCharge cleanupWeight (frameSlots live) F+tapeCharge cleanupWeight js F ≤
          tapeCharge cleanupWeight js S+(rate*c.cells+coreRate*LeafCore.coreCost c.cells (c.w+1)+
          ⌊stageRate*((c.node.width : ℝ)^σ*(c.cutoff : ℝ)^(M8.Machine.BudgetBound.tau-σ)*c.cells)⌋₊)+
          tapeCharge cleanupWeight (frameSlots live) S := by
  obtain ⟨t,q,fan,build⟩ := seededCompactBandStage n
  obtain ⟨r,k,charts⟩ := correctedFanWorkerWithReserve n
  refine ⟨t,max q r,k,fan,?_⟩
  intro U Q fits
  obtain ⟨P,body,worker,C,seed,load,stage⟩ := build (U := U) ((le_max_left ..).trans fits)
  refine ⟨P,body,seed,load,?_⟩
  intro T K mid entry ret caller outer live room ea ra ca ec rc re
  obtain ⟨code,rate,coreRate,run⟩ := charts body worker fan (frameSlots fan) (frameSlots_nodup fan) mid entry ret caller
    ((le_max_right ..).trans fits) room ea ra ca ec rc re
  refine ⟨code,rate,coreRate,C,?_⟩
  intro c band σ nonneg x u S ready stock dims vacant fresh free
  let price := ⌊C*((c.node.width : ℝ)^σ*(c.cutoff : ℝ)^(M8.Machine.BudgetBound.tau-σ)*c.cells)⌋₊
  have pos : 0 < c.stageWidth := Nat.pos_of_mul_pos_left (c.stageCells ▸
    (show 0 < c.cells from Nat.mul_pos (pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _)
      (Nat.mul_pos c.idlePositive (by decide))))
  obtain ⟨z,F,m,y,exec,user,bill,out,act⟩ := run c.w c.B c.stageFactor pos price (seed c) (by
    intro data v D inFan privateTapes
    obtain ⟨z,F,m,y,exec,user,out,act,cost⟩ := stage c band data v D inFan privateTapes
    exact ⟨z,F,m,y,exec,user,cost σ nonneg,out,act⟩) x u S ready stock
    (dims 0) (dims 1) (dims 2) (dims 3) (dims 4) (dims 5) vacant fresh free
  refine ⟨z,F,m,y,exec,user,out,correctedSweepRead n c.sweepVolume x y act,?_⟩
  have slots : (frameSlots fan).map outer = frameSlots live := by
    simp [frameSlots,live,List.map_reverse,Function.comp_def]
  intro js nd
  have h := bill js nd
  change m+_+_ ≤ _+(rate*((prime^(c.w+1))^16*c.stageWidth)+coreRate*LeafCore.coreCost
    ((prime^(c.w+1))^16*c.stageWidth) (c.w+1)+price)+_ at h
  dsimp only [outer] at slots
  simpa only [slots,c.stageCells] using h

/-- Prepare the correction dimensions from the sweep record and execute the
corrected compact worker on the same bank. -/
theorem recordCorrectedCompactStage [M8.Machine.Net] (n : Fin 9) :
    ∃ (t states : ℕ) (fan : Fin (142081+2) ↪ Fin t), ∀ {U : Type} {Q : ℕ}, states ≤ Q →
    ∃ (T : ℕ) (mid : Fin t ↪ Fin T) (source : Fin 10 ↪ Fin T) (P : Type) (host : P → Pr P T Q prime U)
      (code : Pr P T Q prime U) (seed : CutoffNodeInput → Stacks t prime)
      (rate coreRate : ℕ) (stageRate : ℝ),
      LoadsPackedSeed nodeSeedWords CutoffNodeInput.cells seed ∧
      (∀ i j, mid i ≠ source j) ∧
      ∀ (c : CutoffNodeInput), 7*(c.w+1) ≤ c.cutoff → ∀ σ : ℝ, 0 ≤ σ →
      ∀ (x : Fin 142081 → Fin ((prime^(c.w+1))^16*c.stageWidth) → ZMod 2) u S, HelperFan (fan.trans mid) x S →
      (∀ j, (∀ i, fan i ≠ j) → S.L (mid j) = (seed c).L j ∧ S.R (mid j) = (seed c).R j) →
      (∀ i, S.R (source i) = sweepSeedWords c i) →
      (∀ j, (∀ i, mid i ≠ j) → (∀ i, source i ≠ j) → S.L j = [] ∧ S.R j = []) →
      ∃ z F m y, Exec host code (mk u S) m (mk z F) ∧ z.user = u.user ∧ HelperFan (fan.trans mid) y F ∧
        (∀ j, sweepRoles n 0 j (sweepView c.sweepVolume y) = (Piece.stage n).run (sweepRoles n 0 j (sweepView c.sweepVolume x))) ∧
        ∀ js, js.Nodup → m+tapeCharge cleanupWeight (frameSlots (fan.trans mid)) F+tapeCharge cleanupWeight js F ≤
          tapeCharge cleanupWeight js S+(rate*c.cells+coreRate*LeafCore.coreCost c.cells (c.w+1)+
          ⌊stageRate*((c.node.width : ℝ)^σ*(c.cutoff : ℝ)^(M8.Machine.BudgetBound.tau-σ)*c.cells)⌋₊)+
          tapeCharge cleanupWeight (frameSlots (fan.trans mid)) S := by
  obtain ⟨t,q,k,fan,build⟩ := placedCorrectedCompactStage n
  refine ⟨t,max q ((fun {q : ℕ} (_ : Program 38 q prime) => q) (RecursiveRowsNodeHeaders.program 142080)),fan,?_⟩
  intro U Q fits
  obtain ⟨P,body,seed,loader,charts⟩ := build (U := U) ((le_max_left ..).trans fits)
  let b := rowSwapBlock.tapes+35
  let h := t+b+b
  let T := h+353+6+7+9
  let ext := Fin.castAddEmb (24+k) (n := T)
  let mid : Fin t ↪ Fin T := chartSlice 0 (by dsimp [T,h]; omega)
  let entry : Fin b ↪ Fin T := chartSlice t (by dsimp [T,h]; omega)
  let ret : Fin b ↪ Fin T := chartSlice (t+b) (by dsimp [T,h]; omega)
  let ar : Fin 353 ↪ Fin T := chartSlice h (by dsimp [T]; omega)
  let flat : Fin 6 ↪ Fin T := chartSlice (h+353) (by dsimp [T]; omega)
  let dims : Fin 7 ↪ Fin T := chartSlice (h+359) (by dsimp [T]; omega)
  let src : Fin 10 ↪ Fin T := chartSlice (h+365) (by dsimp [T]; omega)
  let caller := (Fin.castAddEmb 1 (n := 6)).trans dims
  let host := fun f => embProg (mid.trans ext) id (body f)
  obtain ⟨work,r,cr,C,run⟩ := charts (K := k) mid entry ret caller le_rfl
    (by intro i j eq; have v := congrArg Fin.val eq; change t+i.val = 0+j.val at v; omega)
    (by intro i j eq; have v := congrArg Fin.val eq; change t+b+i.val = 0+j.val at v; omega)
    (by intro i j eq; have v := congrArg Fin.val eq; change h+359+i.val = 0+j.val at v; simp only [h] at v; omega)
    (by intro i j eq; have v := congrArg Fin.val eq; change t+i.val = h+359+j.val at v; simp only [h] at v; omega)
    (by intro i j eq; have v := congrArg Fin.val eq; change t+b+i.val = h+359+j.val at v; simp only [h] at v; omega)
    (by intro i j eq; have v := congrArg Fin.val eq; change t+b+i.val = t+j.val at v; omega)
  obtain ⟨prep,a,prepare⟩ := loadCompactDimensions host (ar.trans ext) (flat.trans ext) (dims.trans ext)
    (fun i => ext (src i.succ)) (by intro i j eq; have v := congrArg Fin.val eq; change h+i.val = h+365+(j.val+1) at v; dsimp only [h] at v; omega)
    ((le_max_right ..).trans fits) (by intro i j eq; have v := congrArg Fin.val eq; change h+353+i.val = h+j.val at v; dsimp only [h] at v; omega) (by intro i j eq; have v := congrArg Fin.val eq; change h+359+i.val = h+j.val at v; dsimp only [h] at v; omega) (by intro i j eq; have v := congrArg Fin.val eq; change h+353+i.val = h+359+j.val at v; dsimp only [h] at v; omega)
  refine ⟨_,mid.trans ext,src.trans ext,P,host,prep.seq work,seed,2*a+r,cr,C,loader,
    by intro i j eq; have v := congrArg Fin.val eq; change 0+i.val = h+365+j.val at v; dsimp only [h] at v; omega,?_⟩
  intro c band σ nonneg x u S live stock words blank
  have clear (j : Fin T) (lo : t ≤ j.val) (hi : j.val < h+365) := blank (ext j)
    (fun i eq => by have v := congrArg Fin.val (ext.injective eq); change 0+i.val = j.val at v; omega)
    (fun i eq => by have v := congrArg Fin.val (ext.injective eq); change h+365+i.val = j.val at v; omega)
  obtain ⟨v,D,m,start,user,paid,dim,_,frame⟩ := prepare c u S (fun i => words i.succ)
    (fun i => clear _ (by change t ≤ h+i.val; dsimp [h]; omega) (by change h+i.val < _; omega))
    (fun i => (clear _ (by change t ≤ h+353+i.val; dsimp [h]; omega) (by change h+353+i.val < _; omega)).2)
    (fun i => (clear _ (by change t ≤ h+359+i.val; dsimp [h]; omega) (by change h+359+i.val < _; omega)).2)
    (by apply Eq.trans _ (words 0); apply congrArg S.R; apply congrArg ext; apply Fin.ext; change h+359+6 = h+365+0; omega)
  have kept (j : Fin T) (before : j.val < h) := frame (ext j)
    (fun i eq => by have v := congrArg Fin.val (ext.injective eq); change h+i.val = j.val at v; omega)
    (fun i eq => by have v := congrArg Fin.val (ext.injective eq); change h+353+i.val = j.val at v; omega)
    (fun i eq => by have v := congrArg Fin.val (ext.injective eq); change h+359+i.val = j.val at v; omega)
  have core i := kept (mid i) (by change 0+i.val < h; dsimp [h,b]; omega)
  have ready : HelperFan (fan.trans (mid.trans ext)) x D := by
    intro i j
    change _ = readAt _ (D.L (ext (mid (fan i)))) (D.R (ext (mid (fan i)))) _
    rw [(core _).1,(core _).2]
    exact live i j
  have clean (j : Fin T) (lo : t ≤ j.val) (hi : j.val < h) :=
    And.intro ((kept j hi).1.trans (clear j lo (by omega)).1) ((kept j hi).2.trans (clear j lo (by omega)).2)
  have off (i : Fin (24+k)) (j : Fin T) : ext j ≠ i.natAdd T := by
    intro eq
    have v := congrArg Fin.val eq
    change j.val = T+i.val at v
    omega
  obtain ⟨z,F,l,y,finish,last,out,act,bill⟩ := run c band σ nonneg x v D ready
    (fun i away => ⟨(core i).1.trans (stock i away).1,(core i).2.trans (stock i away).2⟩)
    (fun i => dim (i.castAdd 1))
    (fun i _ => clean _ (by change t ≤ t+i.val; omega) (by change t+i.val < h; dsimp [h]; omega))
    (fun i _ => clean _ (by change t ≤ t+b+i.val; omega) (by change t+b+i.val < h; dsimp [h]; omega))
    (fun i => by
      have keep := frame _ (fun _ => off i _) (fun _ => off i _) (fun _ => off i _)
      have free := blank _ (fun _ => off i _) (fun _ => off i _)
      exact ⟨keep.1.trans free.1,keep.2.trans free.2⟩)
  refine ⟨z,F,m+l,y,start.seq finish,last.trans user,out,act,?_⟩
  intro js nd
  let slots := frameSlots (fan.trans (mid.trans ext))
  have p := paid js nd
  have f := paid slots (frameSlots_nodup _)
  change m+tapeCharge cleanupWeight js D ≤ tapeCharge cleanupWeight js S+a*c.cells at p
  change m+tapeCharge cleanupWeight slots D ≤ tapeCharge cleanupWeight slots S+a*c.cells at f
  have total := bill js nd
  change l+tapeCharge cleanupWeight slots F+_ ≤ _+_+tapeCharge cleanupWeight slots D at total
  change m+l+tapeCharge cleanupWeight slots F+_ ≤ _+_+tapeCharge cleanupWeight slots S
  rw [Nat.add_mul,Nat.mul_assoc]
  omega

/-- Correct the input and output ports of the seeded compact worker. Every
borrowed spectator now sees the scheduled stage in its own coordinates. -/
theorem correctedCompactBandStage [M8.Machine.Net] (n : Fin 9) :
    ∃ states : ℕ, ∀ {U : Type} {Q : ℕ}, states ≤ Q →
    ∃ (T : ℕ) (fan : Fin (142081+2) ↪ Fin T) (Label : Type) (host : Label → Pr Label T Q prime U)
      (code : Pr Label T Q prime U) (base coreRate : ℕ) (rate : ℝ) (seed : CutoffNodeInput → Stacks T prime),
      LoadsPackedSeed nodeSeedWords CutoffNodeInput.cells seed ∧ ∀ c : CutoffNodeInput, 7*(c.w+1) ≤ c.cutoff →
      ∀ σ : ℝ, 0 ≤ σ →
      ∀ (x : Fin 142081 → Fin ((prime^(c.w+1))^16*c.stageWidth) → ZMod 2) u S, HelperFan fan x S →
      (∀ j, (∀ i, fan i ≠ j) → S.L j = (seed c).L j ∧ S.R j = (seed c).R j) →
      ∃ z F t y, Exec host code (mk u S) t (mk z F) ∧ z.user = u.user ∧ HelperFan fan y F ∧
        (∀ j : Fin (c.B*prime^(64*((c.w+1)*64))*c.stageFactor),
          sweepRoles n 0 j (sweepView c.sweepVolume y) =
            (Piece.stage n).run (sweepRoles n 0 j (sweepView c.sweepVolume x))) ∧
        ∀ js : List _, js.Nodup → t+tapeCharge cleanupWeight (frameSlots fan) F+tapeCharge cleanupWeight js F ≤
          tapeCharge cleanupWeight js S+(base*c.cells+coreRate*LeafCore.coreCost c.cells (c.w+1)+
          ⌊rate*((c.node.width : ℝ)^σ*(c.cutoff : ℝ)^(M8.Machine.BudgetBound.tau-σ)*c.cells)⌋₊)+
          tapeCharge cleanupWeight (frameSlots fan) S := by
  classical
  obtain ⟨t,q,fan,build⟩ := recordCorrectedCompactStage n
  refine ⟨q,?_⟩
  intro U Q fits
  obtain ⟨T,mid,src,P,host,code,inner,r,k,C,install,apart,run⟩ := build (U := U) fits
  let sweep (c : CutoffNodeInput) : Stacks T prime :=
    ⟨[],[],fun _ => [],Function.extend src (sweepSeedWords c) (fun _ => [])⟩
  let seed (c : CutoffNodeInput) : Stacks T prime := ⟨[],[],
    Function.extend mid (inner c).L (sweep c).L,Function.extend mid (inner c).R (sweep c).R⟩
  have innerRead c i : (seed c).L (mid i) = (inner c).L i ∧ (seed c).R (mid i) = (inner c).R i :=
    ⟨mid.injective.extend_apply ..,mid.injective.extend_apply ..⟩
  have outside c j (away : ∀ i, mid i ≠ j) :
      (seed c).L j = (sweep c).L j ∧ (seed c).R j = (sweep c).R j := by
    have miss : ¬∃ i, mid i = j := fun ⟨i,h⟩ => away i h
    exact ⟨Function.extend_apply' _ _ _ miss,Function.extend_apply' _ _ _ miss⟩
  have empty c j (away : ∀ i, src i ≠ j) : (sweep c).L j = [] ∧ (sweep c).R j = [] :=
    ⟨rfl,Function.extend_apply' (sweepSeedWords c) (fun _ => []) j (fun ⟨i,h⟩ => away i h)⟩
  have sweepLoad : LoadsPackedSeed nodeSeedWords CutoffNodeInput.cells sweep :=
    compactSweepRecordLoader src (mid (fan 0)) (mid (fan 1)) (mid.injective.ne (fan.injective.ne (by decide)))
      (fun j => (apart _ j).symm) (fun j => (apart _ j).symm)
  refine ⟨T,fan.trans mid,P,host,code,r,k,C,seed,?_,?_⟩
  · obtain ⟨a,load⟩ := sweepLoad
    obtain ⟨b,fill⟩ := install
    refine ⟨a+b,?_⟩
    intro A V N R body bank words disjoint
    obtain ⟨first,start⟩ := load body bank words disjoint
    obtain ⟨second,finish⟩ := fill body (mid.trans bank) words (fun i j => disjoint _ j)
    refine ⟨first.seq second,?_⟩
    intro c u S hdr vacant
    obtain ⟨v,D,m,beginRun,user,paid,set,keep⟩ := start c u S hdr vacant
    obtain ⟨z,F,l,endRun,last,bill,stored,frame⟩ := finish c v D
      (fun i => (keep _ (fun j => disjoint j i)).2.trans (hdr i)) (by
        intro i
        have clear := empty c (mid i) (fun j => (apart i j).symm)
        exact ⟨(set _).1.trans clear.1,(set _).2.trans clear.2⟩)
    refine ⟨z,F,m+l,beginRun.seq endRun,last.trans user,by simpa only [Nat.add_mul] using paid.seq bill,?_,?_⟩
    · intro j
      by_cases h : ∃ i, mid i = j
      · obtain ⟨i,rfl⟩ := h
        exact ⟨(stored i).1.trans (innerRead c i).1.symm,(stored i).2.trans (innerRead c i).2.symm⟩
      have miss i : mid i ≠ j := fun eq => h ⟨i,eq⟩
      have kept := frame (bank j) (fun i => bank.injective.ne (miss i))
      exact ⟨kept.1.trans ((set j).1.trans (outside c j miss).1.symm),
        kept.2.trans ((set j).2.trans (outside c j miss).2.symm)⟩
    · intro j away
      have kept := frame j (fun i => away _)
      exact ⟨kept.1.trans (keep j away).1,kept.2.trans (keep j away).2⟩
  · intro c band σ nonneg x u S live fresh
    apply run c band σ nonneg x u S live
    · intro j away
      have h := fresh (mid j) (fun i => mid.injective.ne (away i))
      exact ⟨h.1.trans (innerRead c j).1,h.2.trans (innerRead c j).2⟩
    · intro i
      have h := fresh (src i) (fun j => apart _ _)
      exact h.2.trans ((outside c _ (fun j => apart j i)).2.trans
        (src.injective.extend_apply (sweepSeedWords c) (fun _ => []) i))
    · intro j m d
      have h := fresh j (fun i => m _)
      exact ⟨h.1.trans ((outside c j m).1.trans (empty c j d).1),
        h.2.trans ((outside c j m).2.trans (empty c j d).2)⟩

-- The preinitialized port-correction proof is available at ed84bd4d.
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
    ∃ (C : ℝ) (states : ℕ), ∀ {U : Type} {Q : ℕ}, states ≤ Q →
    ∃ (T : ℕ) (src dst : Fin (142081+2) ↪ Fin T) (Label : Type) (host : Label → Pr Label T Q prime U)
      (code : Pr Label T Q prime U) (base coreRate : ℕ) (rate : ℝ), ∀ c : CutoffNodeInput, 7*(c.w+1) ≤ c.cutoff →
      ∀ σ : ℝ, 0 ≤ σ → ∃ seed : Stacks T prime,
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
  obtain ⟨q,build⟩ := correctedCompactBandStage n
  obtain ⟨C,r,charts⟩ := flatChartWorkerWithReserve
  refine ⟨C,max q r,?_⟩
  intro U Q fits
  obtain ⟨T,fan,Label,body,worker,base,coreRate,rate,initialFor,_,run⟩ := build (U := U) ((le_max_left ..).trans fits)
  let reserve := tapeCharge cleanupWeight (frameSlots fan)
  obtain ⟨H,bank,code,chart⟩ := charts n fan body worker reserve
    (fun bank => chartOwnerReserveGrowth fan bank) ((le_max_right ..).trans fits)
  let live := fan.trans bank
  let table := fun f => embProg bank id (body f)
  obtain ⟨program,pack⟩ := flatWordStageWithCounterReserve live table code
  let place := Exit.chart 0 H
  refine ⟨_,live.trans place,returnedFan live,Label,fun f => embProg place id (table f),program,base,coreRate,rate,?_⟩
  intro c band σ nonneg
  let initial := initialFor c
  have correct := run c band σ nonneg
  let price := base*c.cells+coreRate*LeafCore.coreCost c.cells (c.w+1)+
    ⌊rate*((c.node.width : ℝ)^σ*(c.cutoff : ℝ)^(M8.Machine.BudgetBound.tau-σ)*c.cells)⌋₊
  have positive : 0 < c.B*prime^(64*((c.w+1)*64))*c.stageFactor := by
    rw [c.stageTail]
    exact Nat.mul_pos c.idlePositive (by decide)
  obtain ⟨seed,_,execute⟩ := chart c.sweepVolume price initial (by omega) positive (by
    intro x u S ready fresh
    obtain ⟨z,F,k,y,exec,user,out,effect,bill⟩ := correct x u S ready fresh
    exact ⟨z,F,k,y,exec,fun js nd => (bill js nd).trans_eq (by simp only [price,reserve,Nat.add_assoc]),user,out,effect⟩)
    ⟨[],[],fun _ => [],fun _ => []⟩
  refine ⟨flatStageSeed seed,?_⟩
  intro w V W bill
  apply pack seed
  intro x u S words fresh
  obtain ⟨z,F,k,y,exec,paid,user,out,act⟩ := execute x u S words.helperFan fresh
  refine ⟨z,F,k,y,exec,?_,user,out,act⟩
  intro js nd
  have charge (A : Stacks H prime) : reserve (embStk bank A) = tapeCharge cleanupWeight (frameSlots live) A :=
    placedFrameCharge ..
  have h := paid js nd
  rw [charge,charge] at h
  have integral := Nat.le_ceil (C*V*(w : ℝ)^M8.Machine.BudgetBound.tau)
  exact_mod_cast (by linarith only [h,integral] :
    (k : ℝ)+tapeCharge cleanupWeight (frameSlots live) F+tapeCharge cleanupWeight js F ≤
      tapeCharge cleanupWeight js S+(price+(⌈C*V*(w : ℝ)^M8.Machine.BudgetBound.tau⌉₊ : ℝ))+
        tapeCharge cleanupWeight (frameSlots live) S)

/-- The packed stage has one rate for all stopping-band nodes and all nonnegative exponents. -/
theorem packedCompactBandStage [M8.Machine.Net] (n : Fin 9) :
    ∃ states : ℕ, ∀ {U : Type} {Q : ℕ}, states ≤ Q →
    ∃ (T : ℕ) (src dst : Fin (142081+2) ↪ Fin T) (Label : Type) (host : Label → Pr Label T Q prime U)
      (code : Pr Label T Q prime U) (rate : ℝ), ∀ c : CutoffNodeInput, 7*(c.w+1) ≤ c.cutoff →
      ∀ σ : ℝ, 0 ≤ σ → ∃ seed : Stacks T prime,
      let w := c.w+1
      let V := (prime^w)^16*c.stageWidth
      let W := c.B*prime^(64*(w*64))*c.stageFactor
      PackedPieceHandoffWithReserve cleanupWeight (fun l r => ∑ j, cleanupWeight (l j) (r j)) V
        (fun x y => ∀ j : Fin W,
          let address := fun v => (flatWindowEquiv w W (windowState w v,j)).cast c.sweepVolume
          readRoles address y = (Piece.stage n).run (readRoles address x)) host code src dst seed
        ⌊rate*((c.node.width : ℝ)^σ*(c.cutoff : ℝ)^(M8.Machine.BudgetBound.tau-σ)*c.cells)⌋₊ := by
  obtain ⟨C,states,build⟩ := packedCompactBandExecution n
  refine ⟨states,?_⟩
  intro U Q fits
  obtain ⟨T,src,dst,Label,host,code,base,coreRate,rate,run⟩ := build (U := U) fits
  obtain ⟨D,hD,charts⟩ := compactChartCost base coreRate C
  refine ⟨T,src,dst,Label,host,code,D+max 0 rate,?_⟩
  intro c band σ nonneg
  obtain ⟨seed,execute⟩ := run c band σ nonneg
  refine ⟨seed,?_⟩
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
