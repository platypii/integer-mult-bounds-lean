module

public import IntegerMultBounds.MathlibTM2.M6.BitStoppedIntervalCaller
public import IntegerMultBounds.MathlibTM2.M6.BitPhysicalIntervalHeaders

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback M8.RevMachine
open RecursiveInterchangeLayout IntervalDescriptor
open Shared50ModularControl (prime)

/-- Generate the physical interval descriptor directly on the child's six private
tapes. The stopped call clears them when it returns the transposed caller record. -/
theorem generatedStoppedInterval [M8.Machine.Net] {Q : ℕ} {U : Type} (capacity : columnCapacity ≤ Q)
    (mergeCap : let q := 7+(CyclicRowCycle.states 142080+5)+4; q+q ≤ Q) :
    ∃ (C : ℝ) (N : ℕ) (body : Unit → Pr Unit (72+N) Q prime U), 0 ≤ C ∧
    let bank := Fin.castAddEmb N (n := 72)
    ∀ lo hi, lo < hi → hi ≤ 64 → ∃ code : Pr Unit (72+N) Q prime U, ∀ a W, 0 < a → 0 < W →
      let M := prime^a
      let lane := phaseIntervalChild lo hi a W 64
      let wide := {lane with afterD := lane.afterD*142080}
      ∀ (child : Descriptor) (position : Fin (volume prime child) ≃ Fin (volume prime wide)),
      InheritedIntervalPositions child wide rfl position → lane.width = child.width →
      ∀ (word : Fin (volume prime wide) → ZMod 2) u S,
      S.R (bank 2) = binSyms M.size M → S.R (bank 28) = binSyms 1 1 →
      S.R (bank 53) = binSyms W.size W → (S.R (bank 71)).length = a →
      (∀ i : Fin 72, 59 ≤ i.val → i.val ≤ 65 → S.R (bank i) = []) →
      RecordPayload (bank 24) (fun _ => blank) 0 word S → S.L (bank 59) = [] →
      (∀ i, S.L (bank (descriptorPorts i)) = [] ∧ S.R (bank (descriptorPorts i)) = []) →
      (∀ j : Fin N, S.L (j.natAdd 72) = [] ∧ S.R (j.natAdd 72) = []) →
      ∃ z F t changed, Exec body code (mk u S) t (mk z F) ∧
        t ≤ ⌊C*(child.width : ℝ)^M8.Machine.BudgetBound.tau*volume prime child⌋₊ ∧
        z.user = u.user ∧ RecordPayload (bank 24) (fun _ => blank) 0 changed F ∧
        (∀ j, changed (position j) = Shared50RecursiveNodeRows.transpose (one_dvd child.rows) (word ∘ position) j) ∧
        ∀ j, j ≠ bank 24 → F.L j = S.L j ∧ F.R j = S.R j := by
  obtain ⟨C,N,table,port,master,pos,apart,build⟩ := seededStoppedInterval (U := U) capacity mergeCap
  let bank := Fin.castAddEmb N (n := 72)
  obtain ⟨place,shared,privateTape⟩ := adjacentStagePlacement descriptorPorts master
  let body := fun f => embProg place id (table f)
  have outside (i : Fin N) (j : Fin 72) (away : ∀ h, descriptorPorts h ≠ j) : place i ≠ bank j := by
    by_cases hit : ∃ h, master h = i
    · obtain ⟨h,rfl⟩ := hit
      rw [shared]
      exact bank.injective.ne (away h)
    · rw [privateTape i (fun h eq => hit ⟨h,eq⟩)]
      intro eq
      have e := congrArg Fin.val eq
      change 72+i.val = j.val at e
      omega
  have regs (i) := And.intro (outside i 24 (by decide)) (And.intro (outside i 59 (by decide))
    (And.intro (outside i 60 (by decide)) (outside i 61 (by decide))))
  have distinct : [bank 60,place port,bank 24,bank 61,bank 59].Nodup := by
    obtain ⟨a,b,c,d⟩ := regs port
    simp [a,b,c.symm,d,bank.injective.eq_iff]
  obtain ⟨call,run⟩ := build body place id (fun _ => rfl) _ _ _ _ distinct regs
  refine ⟨C+1,N,body,by positivity,?_⟩
  intro _ lo hi ordered fits
  refine ⟨(intervalHeadersFor bank lo hi true).seq call,?_⟩
  intro a W live positive M lane wide child position coords width word u S base unit tail atom scratch source tl slotsEmpty unused
  have slots i : bank (descriptorPorts i) = place (master i) := (shared i).symm
  have fresh j : S.L (place j) = [] ∧ S.R (place j) = [] := by
    by_cases hit : ∃ i, master i = j
    · obtain ⟨i,rfl⟩ := hit
      rw [← slots]
      exact slotsEmpty i
    · rw [privateTape j (fun i eq => hit ⟨i,eq⟩)]
      exact unused j
  obtain ⟨v,D,k,setup,paid,initial,left,fields,off⟩ := physicalIntervalHeaders_exec body bank lo hi a W
    ordered.le fits live positive u S base unit tail atom scratch (fun i => (slotsEmpty i).2)
  have keep (j) (away : ∀ i, place i ≠ j) := off j (fun i => by rw [slots]; exact (away (master i)).symm)
  have volumeEq : volume prime lane = M^(64+64)*W := intervalChild_volume ordered.le fits a W
  have hp := pow_pos Shared50ModularControl.prime_prime.pos a
  have volumePos : 0 < volume prime lane := by rw [volumeEq]; exact Nat.mul_pos (pow_pos hp _) positive
  have widthPos : 0 < lane.width := Nat.mul_pos (Nat.sub_pos_of_lt ordered) live
  obtain ⟨z,F,t,y,exec,cost,user,out,act,clean,frame⟩ := run lane child position coords width volumePos widthPos word v D
    (fun j => by simpa only [left,keep (bank 24) (fun i => (regs i).1)] using source j) (by rw [left]; exact tl)
    ((keep (bank 59) (fun i => (regs i).2.1)).trans (scratch 59 (by decide) (by decide)))
    ((off _ (fun i => by rw [slots]; exact (place.injective.ne (apart i)).symm)).trans (fresh port).2)
    ((keep (bank 60) (fun i => (regs i).2.2.1)).trans (scratch 60 (by decide) (by decide))) ((keep (bank 61) (fun i => (regs i).2.2.2)).trans (scratch 61 (by decide) (by decide)))
    (fun i => by rw [← slots]; exact fields i) (fun j => by rw [left]; exact (fresh j).1)
    (fun j _ away => (off _ (fun i => by rw [slots]; exact (place.injective.ne (away i)).symm)).trans (fresh j).2)
  refine ⟨z,F,_,y,setup.seq exec,?_,user.trans initial,out,act,?_⟩
  · have mass := Fintype.card_congr position
    simp only [Fintype.card_fin] at mass
    have wideSize : volume prime wide = volume prime lane*142080 := by simp [wide,volume,Nat.mul_assoc]
    have hk : k ≤ volume prime child := by
      rw [mass,wideSize,volumeEq]
      exact paid.trans ((Nat.mul_le_mul_right W (Nat.pow_le_pow_right hp (by decide : 64 ≤ 64+64))).trans
        (Nat.le_mul_of_pos_right _ (by decide)))
    let power := (child.width : ℝ)^M8.Machine.BudgetBound.tau
    have one : 1 ≤ power := Real.one_le_rpow (by exact_mod_cast width ▸ widthPos) M8.Machine.BudgetBound.exponent_range.1.le
    have scale := mul_le_mul_of_nonneg_right one (Nat.cast_nonneg (α := ℝ) (volume prime child))
    have clock := Nat.floor_le (show 0 ≤ C*power*volume prime child by positivity)
    apply Nat.le_floor
    push_cast
    have copied : (k : ℝ) ≤ volume prime child := by exact_mod_cast hk
    have elapsed : (t : ℝ) ≤ (⌊C*power*volume prime child⌋₊ : ℕ) := by exact_mod_cast cost
    change (k : ℝ)+t ≤ (C+1)*power*volume prime child
    linarith only [clock,scale,copied,elapsed]
  · intro j ne
    by_cases hit : ∃ i, place i = j
    · obtain ⟨i,rfl⟩ := hit
      exact ⟨(clean i).1.trans (fresh i).1.symm,(clean i).2.trans (fresh i).2.symm⟩
    have away := fun i eq => hit ⟨i,eq⟩
    exact ⟨(frame j ne away).1.trans (congrFun left j),(frame j ne away).2.trans (keep j away)⟩

/-- One uniform stopped-leaf tariff covers both execution and cleanup at every interval. -/
theorem generatedStoppedIntervalWithCharge [M8.Machine.Net] {Q : ℕ} {U : Type} (capacity : columnCapacity ≤ Q)
    (mergeCap : let q := 7+(CyclicRowCycle.states 142080+5)+4; q+q ≤ Q) :
    ∃ (C : ℝ) (N : ℕ) (body : Unit → Pr Unit (72+N) Q prime U), 0 ≤ C ∧
    let bank := Fin.castAddEmb N (n := 72)
    ∀ lo hi, lo < hi → hi ≤ 64 → ∃ code : Pr Unit (72+N) Q prime U, ∀ a W, 0 < a → 0 < W →
      let M := prime^a
      let lane := phaseIntervalChild lo hi a W 64
      let wide := {lane with afterD := lane.afterD*142080}
      ∀ (child : Descriptor) (position : Fin (volume prime child) ≃ Fin (volume prime wide)),
      InheritedIntervalPositions child wide rfl position → lane.width = child.width →
      ∀ (word : Fin (volume prime wide) → ZMod 2) u S,
      S.R (bank 2) = binSyms M.size M → S.R (bank 28) = binSyms 1 1 →
      S.R (bank 53) = binSyms W.size W → (S.R (bank 71)).length = a →
      (∀ i : Fin 72, 59 ≤ i.val → i.val ≤ 65 → S.R (bank i) = []) →
      RecordPayload (bank 24) (fun _ => blank) 0 word S → S.L (bank 59) = [] →
      (∀ i, S.L (bank (descriptorPorts i)) = [] ∧ S.R (bank (descriptorPorts i)) = []) →
      (∀ j : Fin N, S.L (j.natAdd 72) = [] ∧ S.R (j.natAdd 72) = []) →
      ∃ z F t changed, Exec body code (mk u S) t (mk z F) ∧
        (∀ js : List _, js.Nodup → t+tapeCharge cleanupWeight js F ≤ tapeCharge cleanupWeight js S+
          ⌊C*(child.width : ℝ)^M8.Machine.BudgetBound.tau*volume prime child⌋₊) ∧
        z.user = u.user ∧ RecordPayload (bank 24) (fun _ => blank) 0 changed F ∧
        (∀ j, changed (position j) = Shared50RecursiveNodeRows.transpose (one_dvd child.rows) (word ∘ position) j) ∧
        ∀ j, j ≠ bank 24 → F.L j = S.L j ∧ F.R j = S.R j := by
  classical
  obtain ⟨C,N,body,nonneg,run⟩ := generatedStoppedInterval (U := U) capacity mergeCap
  let Interval := {p : Fin 65 × Fin 65 // p.1 < p.2}
  have worker (i : Interval) := run i.val.1.val i.val.2.val i.property (by omega)
  let bound := Fast.Main.mnProgPush (body ()) + ∑ i : Interval, Fast.Main.mnProgPush (worker i).choose
  let factor := 1+6*bound
  refine ⟨(factor : ℝ)*C,N,body,mul_nonneg (Nat.cast_nonneg factor) nonneg,?_⟩
  intro bank lo hi ordered fits
  let i : Interval := ⟨(⟨lo,by omega⟩,⟨hi,by omega⟩),ordered⟩
  refine ⟨(worker i).choose,?_⟩
  intro a W live positive M lane wide child position coords width word u S base unit tail atom scratch source left slots unused
  obtain ⟨z,F,t,y,exec,paid,user,out,acts,frame⟩ := (worker i).choose_spec a W live positive child position coords width
    word u S base unit tail atom scratch source left slots unused
  refine ⟨z,F,t,y,exec,?_,user,out,acts,frame⟩
  intro js unique
  have small : Fast.Main.mnProgPush (worker i).choose ≤ bound := by
    have le := Finset.single_le_sum (f := fun j : Interval => Fast.Main.mnProgPush (worker j).choose)
      (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
    exact le.trans (Nat.le_add_left _ _)
  have growth := recordCleanup_cost_le js unique exec small (fun f => by cases f; exact Nat.le_add_right _ _)
  change tapeCharge cleanupWeight js F+1 ≤ tapeCharge cleanupWeight js S+1+6*(bound*t) at growth
  have positiveCost := mul_nonneg (mul_nonneg nonneg (Real.rpow_nonneg (Nat.cast_nonneg child.width) M8.Machine.BudgetBound.tau)) (Nat.cast_nonneg (α := ℝ) (volume prime child))
  have elapsed := (Nat.le_floor_iff positiveCost).mp paid
  have scaled := mul_le_mul_of_nonneg_left elapsed (Nat.cast_nonneg (α := ℝ) factor)
  have bill : factor*t ≤ ⌊(factor : ℝ)*C*(child.width : ℝ)^M8.Machine.BudgetBound.tau*volume prime child⌋₊ := by
    apply Nat.le_floor
    simpa only [Nat.cast_mul,mul_assoc] using scaled
  rw [show factor*t = t+6*(bound*t) by simp only [factor,Nat.add_mul,Nat.one_mul,Nat.mul_assoc]] at bill
  omega

end IntegerMultBounds.MathlibTM2.M6.BitNode
