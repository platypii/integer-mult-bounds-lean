module

public import IntegerMultBounds.MathlibTM2.M6.BitBorrowedSweep
public import IntegerMultBounds.MathlibTM2.M6.BitFlatIdleLeaf

/-! A PR589 stage whose scheduled MOVE and COPY children all stop. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback M8.RevMachine
open Certificates.PR589 RecursiveInterchangeLayout
open Shared50ModularControl (prime)

/-- Install one fixed leaf per occurrence. The stage supplies each MOVE's
spectator word and charges its scheduled child at the common leaf rate. -/
theorem stoppedPackedSweep [M8.Machine.Net] (n : Fin 9) :
    ∃ (states : ℕ) (leafRate : ℝ), ∀ {Q : ℕ} {U : Type}, states ≤ Q →
      ∃ coeff : StageRun → ℝ, ∀ (node : Descriptor) (w B rows : ℕ),
      node.width = 64*(w+1) → node.rows = 142080*rows → node.beforeH = B*prime^(64*((w+1)*64)) →
      let K := node.beforeRows*rows*node.between*node.afterD
      let W := ((prime^(w+1))^112*B)*prime^(64*((w+1)*64))*K
      0 < W → ∀ rate : ℝ, leafRate ≤ rate →
      let price := fun (i : Fin nodeChildren5.length) => let child := scheduledChild prime node i
        ⌊(rate*(child.width : ℝ)^M8.Machine.BudgetBound.tau)*volume prime child⌋₊
      ∃ (P : Type) (tapes : StageRun → ℕ) (body : ∀ p, P → Pr P (tapes p) Q prime U),
        PackedStageExecution (w := w+1) (B := B) (K := K) n tapes body coeff
          (fun time => ∀ i : Fin nodeChildren5.length, time i.val = price i) := by
  classical
  obtain ⟨mt,ct,mr,cr,mT,cT,mBank,cBank,states,build⟩ := scheduledInvocationFamily n
  obtain ⟨copyRate,copy⟩ := stoppedCopyChild_budget
  let core : ℝ := (LeafCore.small+5 : ℕ)*|LeafCore.C|+8+LeafCore.small*(16+8*|LeafCore.C|)
  refine ⟨max states (max columnCapacity stoppedCopyMachine.1),max (163+core) copyRate,?_⟩
  intro Q U room
  have caps := (le_max_right _ _).trans room
  let mi := fun (p : StageRun) (i : MoveIndex) => phaseChildPositions.choose (n,p,i)
  let ci := fun (p : StageRun) (j : CopyIndex) => copyChildPosition (n,p,j)
  choose move runMove using fun (p : StageRun) (i : MoveIndex) =>
    stoppedMoveProgram (P := Unit) (U := U) (mr p i) ((le_max_left _ _).trans caps)
      (nodeChildren5[(mi p i).val]) (nodeChildren5_bounds (mi p i)).1
  let mb := fun p i (_ : Unit) => move p i
  let cb := fun (p : StageRun) (j : CopyIndex) (_ : Unit) =>
    stoppedCopyProgram (P := Unit) (U := U) (cr p j) ((le_max_right _ _).trans caps)
  obtain ⟨coeff,stage⟩ := build ((le_max_left _ _).trans room) mb (fun _ _ => ()) cb (fun _ _ => ())
  refine ⟨coeff,?_⟩
  intro node w B rows width split label K W pos rate large price
  let md := fun p i => scheduledChild prime node (mi p i)
  let record := fun p i => let s := CopyChildLayout.spectators (md p i); binSyms (A := prime) s.size s
  obtain ⟨mp,cp,banks,mcoords,ccoords,T,fan,bank,run⟩ :=
    stage node w B rows width split label pos record (fun _ _ => [])
  refine ⟨_,fun p => (banks p).tapes,fun p => (banks p).body (mBank p) (cBank p) (mb p) (cb p),T,fan,bank,?_⟩
  intro scratch owner worker host blocks V time priced
  apply run time
  constructor
  · intro p i
    rw [priced (mi p i)]
    have shape : (md p i).width = (w+1)*nodeChildren5[(mi p i).val] := by
      change nodeChildren5[(mi p i).val]*(node.width/64) = _
      rw [width,Nat.mul_div_cancel_left _ (by decide),Nat.mul_comm]
    exact runMove p i (mb p i) () rfl node (md p i) w W shape (mp p i) (mcoords p i) pos rate
      ((le_max_left _ _).trans large)
  · intro p j
    rw [priced (ci p j)]
    exact copy (cr p j) _ (cb p j) () rfl node n p j w W rows width split [] (cp p j) (ccoords p j) pos rate
      ((le_max_right _ _).trans large)

end IntegerMultBounds.MathlibTM2.M6.BitNode
