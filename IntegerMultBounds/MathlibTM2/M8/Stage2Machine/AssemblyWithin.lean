module

public import IntegerMultBounds.MathlibTM2.M8.Stage2Machine.Assembly
public import IntegerMultBounds.MathlibTM2.M8.Stage2Machine.FamilyStepWithin
public import IntegerMultBounds.MathlibTM2.M8.Stage2Machine.LeafWithin
public import IntegerMultBounds.MathlibTM2.M8.Stage2Machine.PadWithin
public import IntegerMultBounds.MathlibTM2.M8.Stage2Machine.BankHeads
public import IntegerMultBounds.Machine.RawHeadMargin

/-! The family and residual leaf run on the actual padded core bank with the
same interval. Boundary heads are independent of views and array contents. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Stage2Machine.AssemblyWithin
open IntegerMultBounds.Machine
open Networks.Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume)
open SharedBankStageInput (raw)
open FlatCoordinateSchedule (bits)
open RevMachine
open FamilyRoot (bound)
open Assembly
noncomputable section
variable [M8.Machine.Net] {k : ℕ}
  (capacity : Fintype.card (Graph.PC (RevHalf.pcs rev97m).length) ≤ 2^k)

theorem bank_head_eq (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime)
    (st : Tapes 2 prime) (w : ℕ) (u v : Descriptor) (X Y : ℕ → ZMod 2) :
    (bank capacity f p node scalar (fun _ => st) w u X).head =
      (bank capacity f p node scalar (fun _ => st) w v Y).head :=
  SharedBankStageInput.raw_head_congr (Leaf.leafBank_head_eq f p node scalar (Prepare.rest w 529) st u v X Y) _

theorem fam_phase (cutoff : ℕ)
    (hcut : ∀ n, cutoff ≤ n → 1 ≤ M8.Machine.ArbitraryWidthHighPrepare.highDepth prime n ∧
      M8.Machine.ArbitraryWidthHighPrepare.highDepth prime n < n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℕ, ∀ L : ℝ, 1 ≤ L → ((bits w).length : ℝ) ≤ L →
      ((max 1 w : ℕ) : ℝ) ^ M8.Machine.BudgetBound.tau ≤ L →
      ∀ (u : Descriptor) (n : ℕ), u.Positive → 0 < w → u.width = n * w → 1 ≤ n →
      rev97m.roleCount ^ RevNode.depth rev97m.width (RevHalf.Rk rev97m) n ∣ u.rows →
      ∀ (f : ℤ → Fin (prime+4)) (p : ℤ), (∀ z, p ≤ z → f z = blank) →
      ∀ (node : Tapes 1 prime), Family.NodeFree node → ∀ (scalar : Tapes 1 prime) (st : Tapes 2 prime),
      RecursiveStackAllocation.Available 0 st → RecursiveStackAllocation.Available 1 st →
      ∀ lo upper : ℤ,
      (∀ X j, lo+(FamilyStepWithin.coefficient k cutoff*volume prime u : ℕ) ≤
        (bank capacity f p node scalar (fun _ => st) w u X).head j ∧
        (bank capacity f p node scalar (fun _ => st) w u X).head j+
          (FamilyStepWithin.coefficient k cutoff*volume prime u : ℕ) ≤ upper) →
      Core.PhaseWithin (famP capacity) (bank capacity f p node scalar (fun _ => st) w) u u (RevT prime w n u)
        (k + 1 + ⌊bound C L n * volume prime u⌋₊) (fun z => ∀ j, lo ≤ z.head j ∧ z.head j ≤ upper) := by
  obtain ⟨C,hC,hF⟩ := FamilyStepWithin.family_step capacity cutoff hcut
  refine ⟨C,hC,?_⟩
  intro w L hL hbits hpower u n hp hw hwn hn hrows f p hpay node hfree scalar st hdesc hpc lo upper hm
  have hraw (X : ℕ → ZMod 2) := SharedBankStageInput.raw_margin_of_padding
    (Leaf.leafBank f p node scalar (Prepare.rest w 529) st u X)
    (by have h := switch_le capacity; omega : CommonBank.count (NodeBank.tapes rev97m) < tW capacity) (hm X)
  have hz := hraw (fun _ => 0) (CommonBank.count (NodeBank.tapes rev97m)+1)
    (Fin.last (CommonBank.count (NodeBank.tapes rev97m)))
  simp only [raw,Fin.val_last,lt_self_iff_false,↓reduceDIte] at hz
  have h := hF w L hL hbits hpower u n hp hw hwn hn hrows f p hpay node hfree scalar st hdesc hpc
    lo upper (fun X => hraw X (FamilyStep.tF capacity))
  have h' : Core.PhaseWithin (FamilyStep.program capacity)
      (fun u' X => raw (Leaf.leafBank f p node scalar (Prepare.rest w 529) st u' X) (FamilyStep.tF capacity))
      u u (RevT prime w n u) _ (fun z => ∀ j, lo ≤ z.head j ∧ z.head j ≤ upper) := h
  exact PadWithin.pad_step (tF_le capacity) (count_le capacity) h' (by omega) (by omega)

theorem leaf_phase (cutoff : ℕ)
    (hcut : ∀ n, cutoff ≤ n → 1 ≤ M8.Machine.ArbitraryWidthHighPrepare.highDepth prime n ∧
      M8.Machine.ArbitraryWidthHighPrepare.highDepth prime n < n)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime)
    (st : Tapes 2 prime) (w : ℕ) (u : Descriptor) (hp : u.Positive) (lo upper : ℤ)
    (hm : ∀ X j, lo+(M8.Machine.ArbitraryWidthOriginalTotalRunWithin.coefficient cutoff*volume prime u : ℕ) ≤
      (bank capacity f p node scalar (fun _ => st) w u X).head j ∧
      (bank capacity f p node scalar (fun _ => st) w u X).head j+
        (M8.Machine.ArbitraryWidthOriginalTotalRunWithin.coefficient cutoff*volume prime u : ℕ) ≤ upper) :
    Core.PhaseWithin (leafP capacity) (bank capacity f p node scalar (fun _ => st) w) u u
      (Stage2Wrapper.Moves prime u Prod.swap) (M8.Machine.ArbitraryWidthOriginalTotalRun.cost u (Routines.hdr u))
      (fun z => ∀ j, lo ≤ z.head j ∧ z.head j ≤ upper) := by
  have hraw (X : ℕ → ZMod 2) := SharedBankStageInput.raw_margin_of_padding
    (Leaf.leafBank f p node scalar (Prepare.rest w 529) st u X)
    (by have h := switch_le capacity; omega : CommonBank.count (NodeBank.tapes rev97m) < tW capacity) (hm X)
  have hz := hraw (fun _ => 0) (CommonBank.count (NodeBank.tapes rev97m)+1)
    (Fin.last (CommonBank.count (NodeBank.tapes rev97m)))
  simp only [raw,Fin.val_last,lt_self_iff_false,↓reduceDIte] at hz
  have h := LeafWithin.leaf_phase cutoff hcut f p node scalar (Prepare.rest w 529) st u hp lo upper
    (fun X => hraw X (LeafCore.core (NodeBank.io rev97m)).tapes)
  exact PadWithin.pad_step (core_le capacity) (SharedBankFamily.common_le _) h (by omega) (by omega)

end
end IntegerMultBounds.MathlibTM2.M8.Stage2Machine.AssemblyWithin
