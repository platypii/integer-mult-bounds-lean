module

public import IntegerMultBounds.MathlibTM2.M6.BitInstalledRecordChild
public import IntegerMultBounds.MathlibTM2.M6.BitCutoffRecurrence

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Certificates.PR589 RecursiveInterchangeLayout
open Stack Host M8.RevMachine
open Shared50ModularControl (prime)

private theorem recordEntryBound (c : CutoffNodeInput) (rate : ℕ) :
    rate*c.cells+(142081*(10*c.cells+10)+1)+2 ≤ (rate+21)*volume prime c.node := by
  rw [← c.cells_share,Nat.add_mul]
  have positive : 0 < c.cells := Nat.mul_pos (pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _)
    (Nat.mul_pos c.idlePositive (by decide))
  have h := Nat.mul_le_mul_left rate (show c.cells ≤ c.cells*142080 by omega)
  omega

/-- A fixed entry program fits the tree allowance whenever the core receives
at most the local charge and the allowances of its scheduled children. -/
def SplitRecordTreeFamily [M8.Machine.Net] {Config P U : Type} {N Q : ℕ}
    (input : Config → CutoffNodeInput) (body : P → Pr P N Q prime U) (dst : Fin (142081+2) ↪ Fin N)
    (leafRate : ℝ) (budget : Config → ℕ → ℕ) : Prop :=
    ∃ minimum : ℝ, 0 ≤ minimum ∧ ∀ {T : ℕ}
      (live : Fin (142080+2) ↪ Fin T) (record : Fin 34 ↪ Fin T),
      (∀ i j, 8 ≤ j.val → record j ≠ live i) →
      let H := 142082+T+N
      ∃ (bank : Fin N ↪ Fin H) (host : Empty ⊕ P → Pr (Empty ⊕ P) H Q prime U)
        (program : Pr (Empty ⊕ P) H Q prime U), (∀ f, host (.inr f) = embProg bank Sum.inr (body f)) ∧ ChildBankFrame live bank ∧ ∀ D : ℝ, minimum ≤ D → ∀ x, let c := input x
        c.cutoff < c.node.width →
        let fuel := c.depth-(c.path.length+1)
        (∀ k : Fin nodeChildren5.length, let d := scheduledChild prime c.node k
          c.cutoff < d.width → budget x k.val ≤ cutoffTreeBudget D leafRate c.cutoff fuel d) →
        SplitRecordChildExec c live record dst bank host program (cutoffTreeBudget D leafRate c.cutoff (c.depth-c.path.length) c.node) ∧
        InstalledRecordChildExec c live record dst bank host program (cutoffTreeBudget D leafRate c.cutoff (c.depth-c.path.length) c.node)

/-- Once the layout and its initializer are fixed, choose a single tree
coefficient that covers initialization and all active child allowances. -/
theorem splitRecordTreeBudget [M8.Machine.Net] {Config P U : Type} {N Q : ℕ}
    {input : Config → CutoffNodeInput} {seed : Config → Stacks N prime}
    (loader : LoadsNodeSeedFromRecord input seed) (work : Fin 9 → ℕ → ℕ → ℕ) (assemble : ℕ)
    (C : ℝ) (localBound : ∀ x, let c := input x; (c.localCharge work assemble : ℝ) ≤
      C*((volume prime c.node : ℝ)*(c.node.width : ℝ)^M8.Machine.BudgetBound.tau))
    {body : P → Pr P N Q prime U} {code src dst} (leafRate : ℝ) (budget : Config → ℕ → ℕ)
    (child : ∀ x, let c := input x
      PackedPieceHandoffWithCharge cleanupWeight c.cells (packedChildOutput (c.w+1) c.cells)
        body code src dst (seed x) (c.localCharge work assemble+
          ∑ k : Fin nodeChildren5.length, stageBranchTime c.node c.cutoff leafRate (budget x) k.val)) :
    SplitRecordTreeFamily (P := P) (U := U) (Q := Q) input body dst leafRate budget := by
  obtain ⟨rate,build⟩ := runRecordChild loader
  let minimum := max 0 C+(rate+21 : ℕ)
  refine ⟨minimum,by dsimp [minimum]; positivity,?_⟩
  intro T live record apart H
  obtain ⟨bank,host,program,installed,frame,exec⟩ := build body code src dst live record apart
  refine ⟨bank,host,program,installed,frame,?_⟩
  intro D enough x c active fuel allowance
  have shrink : c.root.width*42^c.depth ≤ c.cutoff*64^c.depth := by
    rw [c.rootWidth]
    simpa only [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using Nat.mul_le_mul_right (64^c.depth) c.stop
  have short := scheduledPath_length_lt prime c.root c.depth c.cutoff shrink c.path active
  have remaining : c.depth-c.path.length = fuel+1 := by dsimp only [fuel]; omega
  rw [remaining]
  have width : 1 ≤ c.node.width := by have := c.width; omega
  have growth := Real.one_le_rpow (show 1 ≤ (c.node.width : ℝ) by exact_mod_cast width)
    M8.Machine.BudgetBound.exponent_range.1.le
  let scale := (volume prime c.node : ℝ)*(c.node.width : ℝ)^M8.Machine.BudgetBound.tau
  have vol : (volume prime c.node : ℝ) ≤ scale := le_mul_of_one_le_right (by positivity) growth
  have reserve := recordEntryBound c rate
  have bound := cutoffNodeCharge_le c work assemble D leafRate fuel active _ (by
    rw [Nat.cast_add]
    apply (add_le_add (localBound x) (Nat.cast_le.mpr reserve : (_ : ℝ) ≤ _)).trans
    rw [Nat.cast_mul]
    change C*scale+_ ≤ D*scale
    apply le_trans _ (mul_le_mul_of_nonneg_right enough (by dsimp [scale]; positivity))
    rw [show minimum*scale = max 0 C*scale+((rate+21 : ℕ) : ℝ)*scale by simp [minimum,add_mul]]
    exact add_le_add (mul_le_mul_of_nonneg_right (le_max_right _ _) (by dsimp [scale]; positivity))
      (mul_le_mul_of_nonneg_left vol (by positivity)))
  let next := fun i => if h : i < nodeChildren5.length then
    cutoffTreeBudget D leafRate c.cutoff fuel (scheduledChild prime c.node ⟨i,h⟩) else 0
  have children := Finset.sum_le_sum (s := Finset.univ) (f := fun k : Fin nodeChildren5.length =>
    stageBranchTime c.node c.cutoff leafRate (budget x) k.val)
    (g := fun k => stageBranchTime c.node c.cutoff leafRate next k.val) (fun k _ => by
      simp only [stageBranchTime,next,dite_eq_left k.isLt]
      split
      · exact allowance k ‹_›
      · rfl)
  have run := exec x _ (child x)
  have fits : rate*c.cells+(142081*(10*c.cells+10)+1+
      (c.localCharge work assemble+∑ k : Fin nodeChildren5.length, stageBranchTime c.node c.cutoff leafRate (budget x) k.val))+2 ≤
      cutoffTreeBudget D leafRate c.cutoff (fuel+1) c.node := by
    dsimp only [next,c] at bound children ⊢
    omega
  refine ⟨?_,run.call fits⟩
  intro data u S fan fields cut length scratch bridge vacant
  obtain ⟨z,F,t,y,ran,user,paid,rest⟩ := run data u S fan fields cut length scratch bridge vacant
  refine ⟨z,F,t,y,ran,user,?_,rest⟩
  intro js unique
  dsimp only [next,c] at bound paid children ⊢
  exact (paid js unique).trans (Nat.add_le_add_left (by omega) _)

end IntegerMultBounds.MathlibTM2.M6.BitNode
