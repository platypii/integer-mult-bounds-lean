module

public import IntegerMultBounds.MathlibTM2.M6.BitPackedMoveTranspose
public import IntegerMultBounds.MathlibTM2.M6.BitCutoffRecurrence

/-! Fit the fixed-bank MOVE wrapper into the active child's local reserve. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback
open RecursiveInterchangeLayout (Descriptor volume)
open Shared50ModularControl (prime)

theorem scheduledCutoffMove [M8.Machine.Net] {P U : Type} {T Q : ℕ} (body : P → Pr P T Q prime U) (entry : P)
    (bank : Fin (intervalSplitTapes+1) ↪ Fin T) (tmp buf : Fin T)
    (tmpOff : ∀ i, bank i ≠ tmp) (bufOff : ∀ i, bank i ≠ buf) (distinct : tmp ≠ buf)
    (capacity : let q := 7+(CyclicRowCycle.states 142080+5)+4; q+q ≤ Q) :
    let fan := (withHelperPort (intervalOwners 142080)).trans bank
    ∀ dst : Fin (142081+2) ↪ Fin T,
    (∀ j i, bank (moveReturnPorts j) ≠ childReturnFan dst i) →
    ∃ code : Pr P T Q prime U, ∀ (c : CutoffNodeInput) seed (D rate entryRate : ℝ),
      let child := c.node
      let atom := c.w+1
      let width : child.width = 64*atom := c.width
      let groups : 142080 ∣ child.rows := ⟨_,c.rows⟩
      let W := CopyChildLayout.spectators child / 142080
      let lane := packedDescriptor (64*atom) W
      let m := volume prime lane
      let wide := packedDescriptor (64*atom) (W*142080)
      let size : m*142080 = volume prime wide := by simp [m,lane,wide,volume,packedDescriptor,Nat.mul_assoc]
      let layout := CopyChildLayout.changeLayout wide child width.symm (scheduledMoveSpectators child atom groups)
      let position := (CopyChildLayout.flatAddress wide).symm.trans (layout.trans (CopyChildLayout.flatAddress child))
      let budget := cutoffTreeBudget D rate c.cutoff (c.depth-c.path.length) child
      let scale := (volume prime child : ℝ)*(child.width : ℝ)^M8.Machine.BudgetBound.tau
      c.path.length < c.depth → c.cutoff < child.width → 214000000 ≤ entryRate → entryRate ≤ D →
      PackedPieceHandoffWithCharge cleanupWeight c.cells (packedChildOutput atom c.cells) body (body entry) fan dst seed (budget-⌊entryRate*scale⌋₊) →
      ∀ (x : Fin (volume prime child) → ZMod 2) u (S : Stacks T prime),
      S.R (bank (Fin.succ 0)) = List.ofFn (fun i => SparseRoleCircuit.encode (x (position (i.cast size)))) →
      (∀ i, S.L (bank i) = []) → (∀ i, i ≠ Fin.succ 0 → S.R (bank i) = []) →
      S.L tmp = [] → S.R tmp = [] → S.R buf = [] →
      (∀ j, (∀ i, fan i ≠ bank j) → seed.L (bank j) = [] ∧ seed.R (bank j) = []) →
      (∀ j, (∀ i, bank i ≠ j) → S.L j = seed.L j ∧ S.R j = seed.R j) →
      ∃ z F t, Exec body code (mk u S) t (mk z F) ∧ z.user = u.user ∧
        RecordPayload (bank (Fin.succ 0)) (fun _ => blank) 0
          ((Shared50RecursiveNodeRows.transpose (one_dvd child.rows) x) ∘ position) F ∧
        t ≤ budget := by
  intro fan dst disjoint
  obtain ⟨code,run⟩ := scheduledPackedMove body entry bank tmp buf tmpOff bufOff distinct capacity dst disjoint
  refine ⟨code,?_⟩
  intro c seed D rate entryRate child atom width groups W lane m wide size layout position budget scale short active enough localRate worker x u S source left empty tl tr br localSeed outerSeed
  have volumeEq := Fintype.card_congr position
  simp only [Fintype.card_fin] at volumeEq
  have cells : c.cells = m := Nat.eq_of_mul_eq_mul_right (by decide : 0 < 142080)
    (c.cells_share.trans (size.trans volumeEq).symm)
  have pos : 0 < c.cells := Nat.mul_pos (pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _)
    (Nat.mul_pos c.idlePositive (by decide))
  rw [cells] at worker pos
  obtain ⟨z,F,t,exec,user,out,bill⟩ := run child atom _ seed width groups worker pos x u S source left empty tl tr br localSeed outerSeed
  refine ⟨z,F,t,exec,user,out,?_⟩
  have power : 1 ≤ (child.width : ℝ)^M8.Machine.BudgetBound.tau :=
    Real.one_le_rpow (by exact_mod_cast (show 1 ≤ child.width by omega)) M8.Machine.BudgetBound.exponent_range.1.le
  have mass : (volume prime child : ℝ) ≤ scale := le_mul_of_one_le_right (by positivity) power
  have wrapper : 214000000*volume prime child ≤ ⌊entryRate*scale⌋₊ := by
    apply Nat.le_floor
    push_cast
    exact mul_le_mul enough mass (by positivity) (by linarith)
  have fits : ⌊entryRate*scale⌋₊ ≤ budget := by
    dsimp only [budget]
    rw [show c.depth-c.path.length = (c.depth-c.path.length-1)+1 by omega,cutoffTreeBudget,ite_eq_left active]
    exact (Nat.floor_mono (mul_le_mul_of_nonneg_right localRate ((by positivity : (0 : ℝ) ≤ volume prime child).trans mass))).trans (Nat.le_add_right ..)
  omega

end IntegerMultBounds.MathlibTM2.M6.BitNode
