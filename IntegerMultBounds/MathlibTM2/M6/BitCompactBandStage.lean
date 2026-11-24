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
theorem compactHeaderSeed_load :
    LoadsPackedSeed nodeSeedWords CutoffNodeInput.cells compactHeaderSeed := by
  classical
  let field (j : Fin 6) : Fin 12 := ((j.castAdd 3).succ).castAdd 2
  have read (c : CutoffNodeInput) (j : Fin 6) :
      nodeSeedWords c (field j) = (Routines.hdr c.node j).map bitSymbol := by
    simp only [field,nodeSeedWords,Fin.addCases_left,sweepSeedWords,Fin.cons_succ]
    exact congrFun (parentArchiveSeed_words c.node c.w) (j.castAdd 3) |>.trans (Fin.addCases_left ..)
  let tmp : Fin 37 := 6
  let saved : Fin 37 := 7
  have away (j : Fin 6) : callerHeaderPorts j ≠ tmp ∧ callerHeaderPorts j ≠ saved := by
    constructor <;> intro h <;> have v := congrArg Fin.val h
    · change j.val = 6 at v
      omega
    · change j.val = 7 at v
      omega
  have load := LoadsPackedSeed.headers nodeSeedWords CutoffNodeInput.cells callerHeaderPorts field tmp saved
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
    have atPort := callerHeaderPorts.injective.extend_apply (fun i => nodeSeedWords c (field i))
      (fun _ => []) i
    change Function.extend _ _ _ j = _ at atPort
    rw [atPort,read]
    exact dite_eq_left h
  · have off : ¬ ∃ i, callerHeaderPorts i = j := by
      rintro ⟨i,rfl⟩
      exact h i.isLt
    rw [Function.extend_apply' _ _ _ off]
    exact dite_eq_right h

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
    (header : Fin 37 ↪ Fin H) (source : Fin 12 → Fin H) (cut : source 0 = dims 6)
    (capacity : (fun {q : ℕ} (_ : Program 38 q prime) => q) (RecursiveRowsNodeHeaders.program 142080) ≤ Q)
    (outerOff : ∀ i j, outer i ≠ archive j) (dimsOff : ∀ i j, dims i ≠ archive j)
    (apart : ∀ i j, outer i ≠ dims j) (away : ∀ i j, archive i ≠ source j)
    (ha : ∀ i j, header i ≠ archive j) (ho : ∀ i j, header i ≠ outer j)
    (hd : ∀ i j, header i ≠ dims j) (hs : ∀ i j, header i ≠ source j) :
    ∃ code rate, ∀ (c : CutoffNodeInput) u S, (∀ i, S.R (source i) = nodeSeedWords c i) →
      (∀ i, S.L (header i) = [] ∧ S.R (header i) = []) →
      (∀ i, S.L (archive i) = [] ∧ S.R (archive i) = []) →
      (∀ i, S.R (outer i) = []) → (∀ i : Fin 6, S.R (dims (i.castAdd 1)) = []) →
      ∃ z F t, Exec body code (mk u S) t (mk z F) ∧ z.user = u.user ∧ CleanupBound S F t (rate*c.cells) ∧
        (∀ i, F.R (header i) = (compactHeaderSeed c).R i) ∧
        (∀ i, F.R (dims i) = (compactDimensionSeed c).R i) ∧
        (∀ i : Fin 4, F.R (outer (i.castAdd 2)) = stageChartWords (c.w+1) (c.idleWidth*142080) false i) ∧
        ∀ j, (∀ i, header i ≠ j) → (∀ i, archive i ≠ j) → (∀ i, outer i ≠ j) → (∀ i, dims i ≠ j) →
          F.L j = S.L j ∧ F.R j = S.R j := by
  obtain ⟨r,compile⟩ := compactHeaderSeed_load
  obtain ⟨a,load⟩ := compile body header source hs
  let field (i : Fin 9) := i.succ.castAdd 2
  obtain ⟨b,v,prepare⟩ := loadCompactDimensions body archive outer dims (source ∘ field)
    (fun i j => away i _) capacity outerOff dimsOff apart
  refine ⟨a.seq b,r+v,?_⟩
  intro c u S words free vacant clear blank
  obtain ⟨p,D,n,start,user,paid,set,keep⟩ := load c u S words free
  have read i := (keep (source i) (fun j => hs j i)).2.trans (words i)
  obtain ⟨z,F,m,finish,last,bill,dim,flat,frame⟩ := prepare c p D
    (fun i => by simpa only [Function.comp_apply,field,nodeSeedWords,Fin.addCases_left] using read (field i))
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

private noncomputable def compactWorkerSeed (H : ℕ) (c : CutoffNodeInput) : Stacks ((H+37)+7) prime :=
  ⟨[],[],fun _ => [],Fin.addCases (Fin.addCases (fun _ => []) (compactHeaderSeed c).R) (compactDimensionSeed c).R⟩

private theorem compactWorkerSeed_load (H : ℕ)
    (dims : LoadsPackedSeed nodeSeedWords CutoffNodeInput.cells compactDimensionSeed) :
    LoadsPackedSeed nodeSeedWords CutoffNodeInput.cells (compactWorkerSeed H) := by
  let blank : Stacks H prime := ⟨[],[],fun _ => [],fun _ => []⟩
  have empty := LoadsPackedSeed.fixed nodeSeedWords CutoffNodeInput.cells (fun c =>
    Nat.mul_pos (pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _) (Nat.mul_pos c.idlePositive (by decide))) blank
  convert (empty.join compactHeaderSeed_load).join dims using 1
  funext c
  unfold compactWorkerSeed adjacentStageStacks
  congr 1
  funext j
  induction j using Fin.addCases with
  | right j => rw [Fin.addCases_right]; rfl
  | left j =>
    simp only [Fin.addCases_left]
    induction j using Fin.addCases <;> simp [blank,compactHeaderSeed]

private theorem headerSeedReady {k H a b : ℕ} (fan : Fin k ↪ Fin H)
    (header : Fin a → List (Fin (prime+4))) (dims : Fin b → List (Fin (prime+4))) :
    let place := Fin.castAddEmb a (n := H)
    let outer := Fin.castAddEmb b (n := H+a)
    let seed : Stacks ((H+a)+b) prime := ⟨[],[],fun _ => [],Fin.addCases (Fin.addCases (fun _ => []) header) dims⟩
    ∀ S : Stacks ((H+a)+b) prime, (∀ j, (∀ i, outer (place (fan i)) ≠ j) → S.L j = seed.L j ∧ S.R j = seed.R j) →
    (∀ j, S.R (j.natAdd (H+a)) = dims j) ∧ (∀ j, S.R (outer (j.natAdd H)) = header j) ∧
      ∀ j, (∀ i, fan i ≠ j) → S.L (outer (place j)) = [] ∧ S.R (outer (place j)) = [] := by
  intro place outer seed S fresh
  constructor
  · intro j
    have h := fresh (j.natAdd (H+a)) (fun i eq => by
      have v := congrArg Fin.val eq
      change (place (fan i)).val = (H+a)+j.val at v
      omega)
    simpa only [seed,Fin.addCases_right] using h.2
  constructor
  · intro j
    have h := fresh (outer (j.natAdd H)) (fun i eq => by
      have v := congrArg Fin.val (outer.injective eq)
      change (fan i).val = H+j.val at v
      omega)
    simpa only [seed,outer,Fin.castAddEmb_apply,Fin.addCases_left,Fin.addCases_right] using h.2
  · intro j away
    have h := fresh (outer (place j)) (fun i eq => away i (place.injective (outer.injective eq)))
    simpa only [seed,place,outer,Fin.castAddEmb_apply,Fin.addCases_left] using h

private theorem owner_ne_scratch {T L : ℕ} (i : Fin T) (j : Fin L) :
    ((i.castAdd 273).castAdd L).natAdd 80 ≠ (j.natAdd (T+273)).natAdd 80 := by
  intro h
  have v := congrArg Fin.val h
  change 80+i.val = 80+(T+273+j.val) at v
  omega

/-- The packed caller supplies a single private-tape seed for each node.
The worker and its live tape placement are independent of that node. -/
theorem seededCompactBandStage [M8.Machine.Net] (n : Fin 9) :
    ∃ (T states : ℕ) (fan : Fin (142081+2) ↪ Fin T), ∀ {U : Type} {Q : ℕ}, states ≤ Q →
      ∃ (Label : Type) (host : Label → Pr Label T Q prime U) (code : Pr Label T Q prime U) (rate : ℝ),
      ∃ seed : CutoffNodeInput → Stacks T prime,
      (LoadsPackedSeed nodeSeedWords CutoffNodeInput.cells compactDimensionSeed →
        LoadsPackedSeed nodeSeedWords CutoffNodeInput.cells seed) ∧
      ∀ c : CutoffNodeInput, 7*(c.w+1) ≤ c.cutoff →
      ∀ (x : Fin 142081 → Fin ((prime^(c.w+1))^16*c.stageWidth) → ZMod 2) u S, HelperFan fan x S →
      (∀ j, (∀ i, fan i ≠ j) → S.L j = (seed c).L j ∧ S.R j = (seed c).R j) →
      ∃ z F t y, Exec host code (mk u S) t (mk z F) ∧ z.user = u.user ∧ HelperFan fan y F ∧
        RestoredBorrowedStage n (c.w+1) c.B c.stageFactor x y ∧
        ∀ σ : ℝ, 0 ≤ σ → ∀ js : List _, js.Nodup →
          t+tapeCharge cleanupWeight (frameSlots fan) F+tapeCharge cleanupWeight js F ≤
          tapeCharge cleanupWeight js S+⌊rate*((c.node.width : ℝ)^σ*(c.cutoff : ℝ)^(M8.Machine.BudgetBound.tau-σ)*c.cells)⌋₊+
            tapeCharge cleanupWeight (frameSlots fan) S := by
  obtain ⟨T,states,fan,build⟩ := compactBandStage n
  generalize _h : LeafCore.small = L at build
  let H := 80+((T+273)+L)
  let inner := ((Fin.castAddEmb 273 (n := T)).trans (Fin.castAddEmb L)).trans (Fin.natAddEmb 80)
  let place := Fin.castAddEmb 37 (n := H)
  let outer := Fin.castAddEmb 7 (n := H+37)
  let live := ((fan.trans inner).trans place).trans outer
  refine ⟨_,states,live,?_⟩
  intro U Q fits
  obtain ⟨Label,host,code,rate,run⟩ := build (U := U) fits
  refine ⟨Label,host,code,rate,compactWorkerSeed H,compactWorkerSeed_load H,?_⟩
  intro c band
  let dims := (compactDimensionSeed c).R
  let header := (compactHeaderSeed c).R
  intro x u S ready fresh
  obtain ⟨external,words,blank⟩ := headerSeedReady (fan.trans inner) header dims S fresh
  exact run c band x u S ready words
    (fun j => blank _ (fun i => ((archiveSetupPlacement_frame j).1 (fan i)).symm))
    (fun j => blank _ (fun i => owner_ne_scratch (fan i) j))
    (fun j away => blank _ (fun i h => away i (inner.injective h)))
    (external 0) (external 1) (external 2) (external 3) (external 4) (external 5) (external 6)

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

/-- Correct the input and output ports of the seeded compact worker. Every
borrowed spectator now sees the scheduled stage in its own coordinates. -/
theorem correctedCompactBandStage [M8.Machine.Net] (n : Fin 9) :
    ∃ base tapes states : ℕ, ∀ {U : Type} {Q : ℕ}, states ≤ Q →
    ∃ (T : ℕ) (fan : Fin (142081+2) ↪ Fin T) (Label : Type) (host : Label → Pr Label T Q prime U)
      (code : Pr Label T Q prime U) (rate : ℝ), ∀ c : CutoffNodeInput, 7*(c.w+1) ≤ c.cutoff →
      ∀ σ : ℝ, 0 ≤ σ → ∃ seed : Stacks T prime,
      ∀ (x : Fin 142081 → Fin ((prime^(c.w+1))^16*c.stageWidth) → ZMod 2) u S, HelperFan fan x S →
      (∀ j, (∀ i, fan i ≠ j) → S.L j = seed.L j ∧ S.R j = seed.R j) →
      ∃ z F t y, Exec host code (mk u S) t (mk z F) ∧ z.user = u.user ∧ HelperFan fan y F ∧
        (∀ j : Fin (c.B*prime^(64*((c.w+1)*64))*c.stageFactor),
          sweepRoles n 0 j (sweepView c.sweepVolume y) =
            (Piece.stage n).run (sweepRoles n 0 j (sweepView c.sweepVolume x))) ∧
        ∀ js : List _, js.Nodup → t+tapeCharge cleanupWeight (frameSlots fan) F+tapeCharge cleanupWeight js F ≤
          tapeCharge cleanupWeight js S+25*((base*c.cells+17760*(2*LeafCore.coreCost c.cells (c.w+1)+14))*(tapes+5)+12)+
          ⌊rate*((c.node.width : ℝ)^σ*(c.cutoff : ℝ)^(M8.Machine.BudgetBound.tau-σ)*c.cells)⌋₊+
          tapeCharge cleanupWeight (frameSlots fan) S := by
  obtain ⟨t,q,localFan,build⟩ := seededCompactBandStage n
  obtain ⟨base,tapes,r,charts⟩ := borrowedCorrectionMachines
  obtain ⟨a,b,qa,qb,stages⟩ := charts n
  refine ⟨base,tapes,max q r,?_⟩
  intro U Q fits
  obtain ⟨Label,body,worker,rate,seedFor,_,run⟩ := build (U := U) ((le_max_left ..).trans fits)
  let reserve := tapeCharge cleanupWeight (frameSlots localFan)
  obtain ⟨T,bank,code,allocate⟩ := allocatedChartWorkerWithReserve localFan body worker a b
    (qa.trans ((le_max_right ..).trans fits)) (qb.trans ((le_max_right ..).trans fits))
    reserve 12 (fun bank => chartOwnerReserveGrowth localFan bank)
  refine ⟨T,localFan.trans bank,Label,fun f => embProg bank id (body f),code,rate,?_⟩
  intro c band σ nonneg
  let initial := seedFor c
  have workerRun := run c band
  have cells : 0 < c.cells := Nat.mul_pos (pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _)
    (Nat.mul_pos c.idlePositive (by decide))
  rw [← c.stageCells] at cells
  obtain ⟨enter,leave,ha,hb,sa,sb,paid,action⟩ := stages (c.w+1) c.B c.stageFactor (by omega)
    (Nat.pos_of_mul_pos_left cells)
  let price := ⌊rate*((c.node.width : ℝ)^σ*(c.cutoff : ℝ)^(M8.Machine.BudgetBound.tau-σ)*c.cells)⌋₊
  obtain ⟨seed,_,execute⟩ := allocate (RestoredBorrowedStage n (c.w+1) c.B c.stageFactor)
    price initial enter leave ha hb sa sb (by
      intro x u S ready fresh
      obtain ⟨z,F,k,y,exec,user,out,effect,bill⟩ := workerRun x u S ready fresh
      exact ⟨z,F,k,y,exec,bill σ nonneg,user,out,effect⟩) ⟨[],[],fun _ => [],fun _ => []⟩
  refine ⟨seed,?_⟩
  intro x u S live fresh
  obtain ⟨z,F,k,y,exec,bill,user,out,effect⟩ := execute x u S live fresh
  refine ⟨z,F,k,leave.transform y,exec,user,out,?_,?_⟩
  · exact correctedSweepRead n c.sweepVolume x _ (action x y effect)
  intro js nd
  have h := bill js nd
  change _ ≤ (base*((prime^(c.w+1))^16*c.stageWidth)+17760*(2*LeafCore.coreCost
    ((prime^(c.w+1))^16*c.stageWidth) (c.w+1)+14))*(tapes+5) at paid
  rw [c.stageCells] at paid
  have charge (A : Stacks T prime) : reserve (embStk bank A) =
      tapeCharge cleanupWeight (frameSlots (localFan.trans bank)) A := placedFrameCharge ..
  rw [charge,charge] at h
  dsimp only [price] at h
  exact h.trans (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_left
    (Nat.mul_le_mul_left 25 (Nat.add_le_add_right paid 12)) _) _) _)

private theorem compactChartCost [M8.Machine.Net] (base tapes : ℕ) (C : ℝ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ w V : ℕ, 0 < V →
      ((25*((base*V+17760*(2*LeafCore.coreCost V (w+1)+14))*(tapes+5)+12)+
        ⌈C*V*((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau⌉₊+(142081*(12*V+14)+1) : ℕ) : ℝ) ≤
        D*((V : ℝ)*((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau) := by
  let D := 25*((base+17760*(2 * |LeafCore.C|+14))*(tapes+5 : ℕ)+12)+|C|+1+(142081*26+1)
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
  have inner : (base : ℝ)*V+17760*(2*(LeafCore.coreCost V (w+1) : ℝ)+14) ≤
      (base+17760*(2 * |LeafCore.C|+14))*scale := by
    linarith only [mul_le_mul_of_nonneg_left vol (Nat.cast_nonneg base : (0:ℝ) ≤ base),coreBound,one]
  change _ ≤ D*scale
  dsimp only [D]
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one]
  simp only [Nat.cast_add,Nat.cast_one] at rounded
  linarith only [mul_le_mul_of_nonneg_right inner (show (0:ℝ) ≤ tapes+5 by positivity),rounded,vol,one]

open SweepFile in
/-- A complete compact stage from packed input to packed output in the stopping band. -/
private theorem packedCompactBandExecution [M8.Machine.Net] (n : Fin 9) :
    ∃ (C : ℝ) (base tapes states : ℕ), ∀ {U : Type} {Q : ℕ}, states ≤ Q →
    ∃ (T : ℕ) (src dst : Fin (142081+2) ↪ Fin T) (Label : Type) (host : Label → Pr Label T Q prime U)
      (code : Pr Label T Q prime U) (rate : ℝ), ∀ c : CutoffNodeInput, 7*(c.w+1) ≤ c.cutoff →
      ∀ σ : ℝ, 0 ≤ σ → ∃ seed : Stacks T prime,
      let w := c.w+1
      let V := (prime^w)^16*c.stageWidth
      let W := c.B*prime^(64*(w*64))*c.stageFactor
      let price := 25*((base*c.cells+17760*(2*LeafCore.coreCost c.cells w+14))*(tapes+5)+12)+
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
  obtain ⟨base,tapes,q,build⟩ := correctedCompactBandStage n
  obtain ⟨C,r,charts⟩ := flatChartWorkerWithReserve
  refine ⟨C,base,tapes,max q r,?_⟩
  intro U Q fits
  obtain ⟨T,fan,Label,body,worker,rate,run⟩ := build (U := U) ((le_max_left ..).trans fits)
  let reserve := tapeCharge cleanupWeight (frameSlots fan)
  obtain ⟨H,bank,code,chart⟩ := charts n fan body worker reserve
    (fun bank => chartOwnerReserveGrowth fan bank) ((le_max_right ..).trans fits)
  let live := fan.trans bank
  let table := fun f => embProg bank id (body f)
  obtain ⟨program,pack⟩ := flatWordStageWithCounterReserve live table code
  let place := Exit.chart 0 H
  refine ⟨_,live.trans place,returnedFan live,Label,fun f => embProg place id (table f),program,rate,?_⟩
  intro c band σ nonneg
  obtain ⟨initial,correct⟩ := run c band σ nonneg
  let price := 25*((base*c.cells+17760*(2*LeafCore.coreCost c.cells (c.w+1)+14))*(tapes+5)+12)+
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
  obtain ⟨C,base,tapes,states,build⟩ := packedCompactBandExecution n
  obtain ⟨D,hD,charts⟩ := compactChartCost base tapes C
  refine ⟨states,?_⟩
  intro U Q fits
  obtain ⟨T,src,dst,Label,host,code,rate,run⟩ := build (U := U) fits
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
  let overhead := 25*((base*c.cells+17760*(2*LeafCore.coreCost c.cells w+14))*(tapes+5)+12)+
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
