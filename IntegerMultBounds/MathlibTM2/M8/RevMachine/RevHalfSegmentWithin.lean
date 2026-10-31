module

public import IntegerMultBounds.MathlibTM2.M8.RevMachine.RevHalf
public import IntegerMultBounds.MathlibTM2.M8.RevMachine.NodeSegmentBounds
public import IntegerMultBounds.MathlibTM2.M8.RevMachine.GraphRunWithin

/-! A concrete nonrecursive node piece and its controller edge, with one
fixed head interval throughout the actual graph execution. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.RevMachine.RevHalf
open IntegerMultBounds.Machine Networks
open Networks.Shared50ModularControl (prime)
open RecursiveInterchangeLayout (volume)
open Family (Frame)
open NodeBank (tapes)
open NodeSplit (roleView midView)
open Routines (hdr)
open SharedBankStageInput (raw)
noncomputable section
variable (N : RevNetwork) {k : ℕ}
  {capacity : Fintype.card (Graph.PC (pcs N).length) ≤ 2^k}

theorem seg_within (hR : RevRuns N) {b₀ : ℕ} (σ : Frame (pcs N) capacity)
    (y : Tapes (CommonBank.count (tapes N)) prime) (hok : Ok N b₀ σ) (hm : N.width ≤ σ.n)
    (i : Graph.Site (pcs N)) (s : Schedule.Seg (N.World ⊕ N.Temp) N.width)
    (hi : (pcs N)[i] = .seg s) (hy : NodeS N σ i.val y)
    (core : Graph.Block (CommonBank.count (tapes N)) prime)
    (lo upper : ℤ) (hlo : lo ≤ 0) (hupper : 0 ≤ upper)
    (hbank : ∀ j,
      lo+(RevNode.segSpaceConstant N s*volume prime (roleView N σ.b σ.n σ.v) : ℕ) ≤
        (raw y (RevNode.segB N s).tapes).head j ∧
      (raw y (RevNode.segB N s).tapes).head j+
        (RevNode.segSpaceConstant N s*volume prime (roleView N σ.b σ.n σ.v) : ℕ) ≤ upper) :
    let impl := Family.impl core (RevNode.blocks N k)
    ∃ y', NodeS N σ (i.val+1) y' ∧ ∃ n ≤ segCost N σ s+1,
      RunWithin (Graph.program (pcs N) capacity Family.pcSlot Family.pcSlot_pos impl)
        (fun v => ∀ j, lo ≤ v.head j ∧ v.head j ≤ upper) n
        (Graph.entryConfig (pcs N) capacity Family.pcSlot Family.pcSlot_pos impl (.piece i) y)
        (Graph.entryConfig (pcs N) capacity Family.pcSlot Family.pcSlot_pos impl (Graph.successor (pcs N) i) y') := by
  intro impl
  obtain ⟨y',hy',hr⟩ := half_seg hR σ y hok hm i s hi hy
  have hblock : Graph.block (pcs N) capacity Family.pcSlot Family.pcSlot_pos impl (.piece i) = RevNode.segB N s := by
    simp only [Graph.block,hi,impl,Family.impl,RevNode.blocks]
  have hheads : ∀ z, RunInvariant (RevNode.segB N s).program (· = raw y (RevNode.segB N s).tapes) z →
      ∀ j, lo ≤ z.head j ∧ z.head j ≤ upper := by
    intro z hz j
    obtain ⟨data,_,rfl⟩ := hy
    have hc := RevNode.nodeC_segCounters N σ.b (σ.n/N.width)
    have hp := NodeSplit.roleView_positive N (b := σ.b) (n := σ.n) σ.hpos (rows_dvd hok hm)
    have hf : 0 < σ.n/N.width := Nat.div_pos hm (by have := N.two_le_width; omega)
    have h := RevNode.seg_heads N s σ.hb hf _ rfl hp _ (Routines.hdr_headers _) σ.f σ.p
      (RecursiveViewFrame.savedStack (hdr (midView N σ.b σ.n σ.v)) (RecursiveViewFrame.savedStack (hdr σ.v) σ.node))
      σ.scalar _ σ.st hc data z hz j
    have hb := hbank j
    omega
  refine ⟨y',hy',?_⟩
  apply GraphRun.block_jump_within_heads (pcs N) capacity Family.pcSlot Family.pcSlot_pos impl
    (.piece i) (Graph.successor (pcs N) i) y y' (segCost N σ s)
  · rw [hblock]; exact hr
  · exact Graph.seg_edge (pcs N) capacity Family.pcSlot Family.pcSlot_pos impl i s hi
  · exact hlo
  · exact hupper
  · rw [hblock]; exact hheads

end
end IntegerMultBounds.MathlibTM2.M8.RevMachine.RevHalf
