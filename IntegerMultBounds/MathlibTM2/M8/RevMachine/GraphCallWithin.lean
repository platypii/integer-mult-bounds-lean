module

public import IntegerMultBounds.MathlibTM2.M8.RevMachine.GraphRunWithin

/-! A recursive call reuses the same workspace interval through entry, the
child's actual execution, and recovery. Both controller joins are included. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.RevMachine.GraphRun
open IntegerMultBounds.Machine Graph
open SharedBankStageInput (raw)
noncomputable section
variable {Seg Call : Type} {t a k : ℕ} (pieces : List (Piece Seg Call))
  (capacity : Fintype.card (PC pieces.length) ≤ 2^k) (stack : Fin t) (ht : 0 < t)
  (impl : Implementation t a k Seg Call)

theorem call_jump_within_heads (i : Site pieces) (c : Call) (hi : pieces[i] = .call c)
    (before entered returned after : Tapes t a) (E R nc : ℕ)
    (he : HoareTime (impl.enter c (returnCode pieces capacity i)).program
      (· = raw before (impl.enter c (returnCode pieces capacity i)).tapes)
      (· = raw entered (impl.enter c (returnCode pieces capacity i)).tapes) E)
    (hr : HoareTime (impl.recover c).program (· = raw returned (impl.recover c).tapes)
      (· = raw after (impl.recover c).tapes) R)
    (lo upper : ℤ) (hlo : lo ≤ 0) (hupper : 0 ≤ upper)
    (hc : RunWithin (program pieces capacity stack ht impl)
      (fun v => ∀ j, lo ≤ v.head j ∧ v.head j ≤ upper) nc
      (entryConfig pieces capacity stack ht impl .prepare entered)
      (entryConfig pieces capacity stack ht impl (.recover i) returned))
    (henter : ∀ z, RunInvariant (impl.enter c (returnCode pieces capacity i)).program
      (· = raw before (impl.enter c (returnCode pieces capacity i)).tapes) z →
      ∀ j, lo ≤ z.head j ∧ z.head j ≤ upper)
    (hrecover : ∀ z, RunInvariant (impl.recover c).program
      (· = raw returned (impl.recover c).tapes) z → ∀ j, lo ≤ z.head j ∧ z.head j ≤ upper) :
    ∃ n ≤ E+1+nc+(R+1), RunWithin (program pieces capacity stack ht impl)
      (fun v => ∀ j, lo ≤ v.head j ∧ v.head j ≤ upper) n
      (entryConfig pieces capacity stack ht impl (.piece i) before)
      (entryConfig pieces capacity stack ht impl (successor pieces i) after) := by
  have hbe : block pieces capacity stack ht impl (.piece i) = impl.enter c (returnCode pieces capacity i) := by
    simp only [block,hi]
  have hbr : block pieces capacity stack ht impl (.recover i) = impl.recover c := by
    simp only [block,hi]
  obtain ⟨ne,hne,hwe⟩ := block_jump_within_heads pieces capacity stack ht impl (.piece i) .prepare
    before entered E (by rw [hbe]; exact he) (call_edge pieces capacity stack ht impl i c hi)
    lo upper hlo hupper (by rw [hbe]; exact henter)
  obtain ⟨nr,hnr,hwr⟩ := block_jump_within_heads pieces capacity stack ht impl (.recover i) (successor pieces i)
    returned after R (by rw [hbr]; exact hr) (recover_edge pieces capacity stack ht impl i)
    lo upper hlo hupper (by rw [hbr]; exact hrecover)
  exact ⟨ne+nc+nr,by omega,(hwe.trans hc).trans hwr⟩

end
end IntegerMultBounds.MathlibTM2.M8.RevMachine.GraphRun
