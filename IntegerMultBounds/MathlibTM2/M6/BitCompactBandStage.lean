module

public import IntegerMultBounds.MathlibTM2.M6.BitCompactInitializedStage
public import IntegerMultBounds.MathlibTM2.M6.BitSweepChildWidth

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
  have scale : (c.cutoff : ℝ)^M8.Machine.BudgetBound.tau ≤
      (c.node.width : ℝ)^σ*(c.cutoff : ℝ)^(M8.Machine.BudgetBound.tau-σ) := by
    have width := Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.cast_le.mpr c.active) nonneg
    have pos : (0 : ℝ) < c.cutoff := by exact_mod_cast (by omega : 0 < c.cutoff)
    calc
      _ = (c.cutoff : ℝ)^σ*(c.cutoff : ℝ)^(M8.Machine.BudgetBound.tau-σ) := by
        rw [← Real.rpow_add pos,add_sub_cancel ..]
      _ ≤ _ := mul_le_mul_of_nonneg_right width (Real.rpow_nonneg pos.le _)
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

end IntegerMultBounds.MathlibTM2.M6.BitNode
