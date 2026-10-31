module

public import IntegerMultBounds.MathlibTM2.M8.RevMachine.GraphExistsCallWithin

/-! A frame uses one workspace interval through all its local blocks and child
calls. The only recursive premise is the corresponding certificate for children. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.RevMachine.GraphExists
open IntegerMultBounds.Machine Graph GraphRun
open SharedBankStageInput (raw)
noncomputable section
variable {Seg Call : Type} {t a k : ℕ} {pieces : List (Piece Seg Call)}
  {capacity : Fintype.card (PC pieces.length) ≤ 2^k} {stack : Fin t} {ht : 0 < t}
  {impl : Implementation t a k Seg Call} {m W : ℕ} {rank : Call → ℕ}
  (S : Inv pieces capacity stack impl m W rank)

/-- Local block bounds on the existing frame shapes. No child execution is part
of these bounds; child certificates enter only in `frame_run_within`. -/
structure FrameBounds (σ : S.Shape) (x₀ : Tapes t a) (lo hi : ℤ) : Prop where
  lower_nonpos : lo ≤ 0
  upper_nonneg : 0 ≤ hi
  prepare : ∀ c, RunInvariant impl.prepare.program (· = raw x₀ impl.prepare.tapes) c →
    ∀ j, lo ≤ c.head j ∧ c.head j ≤ hi
  leaf : ∀ i < S.leaves σ, ∀ y, S.Leaf σ x₀ i y →
    ∀ c, RunInvariant impl.leaf.program (· = raw y impl.leaf.tapes) c →
      ∀ j, lo ≤ c.head j ∧ c.head j ≤ hi
  test : ∀ i ≤ S.leaves σ, ∀ y, S.Leaf σ x₀ i y →
    ∀ j, lo+S.cTest σ ≤ (raw y (tapeCount pieces capacity stack ht impl)).head j ∧
      (raw y (tapeCount pieces capacity stack ht impl)).head j+S.cTest σ ≤ hi
  split : ∀ y, S.Leaf σ x₀ (S.leaves σ) y →
    ∀ c, RunInvariant impl.split.program (· = raw y impl.split.tapes) c →
      ∀ j, lo ≤ c.head j ∧ c.head j ≤ hi
  segment : ∀ (i : Site pieces) (s : Seg), pieces[i] = .seg s → ∀ y, S.Node σ x₀ i.val y →
    ∀ c, RunInvariant (impl.segment s).program (· = raw y (impl.segment s).tapes) c →
      ∀ j, lo ≤ c.head j ∧ c.head j ≤ hi
  enter : ∀ (i : Site pieces) (c : Call), pieces[i] = .call c → ∀ y, S.Node σ x₀ i.val y →
    ∀ z, RunInvariant (impl.enter c (returnCode pieces capacity i)).program
      (· = raw y (impl.enter c (returnCode pieces capacity i)).tapes) z →
      ∀ j, lo ≤ z.head j ∧ z.head j ≤ hi
  recover : ∀ (i : Site pieces) (c : Call), pieces[i] = .call c → ∀ y, S.Node σ x₀ i.val y →
    ∀ C : ChildStep S σ x₀ y i c, ∀ z, S.Exit C.child C.entered z →
      ∀ d, RunInvariant (impl.recover c).program (· = raw z (impl.recover c).tapes) d →
        ∀ j, lo ≤ d.head j ∧ d.head j ≤ hi
  merge : ∀ y, S.Node σ x₀ pieces.length y →
    ∀ c, RunInvariant impl.merge.program (· = raw y impl.merge.tapes) c →
      ∀ j, lo ≤ c.head j ∧ c.head j ≤ hi
  finish : ∀ y, S.Done σ x₀ y →
    ∀ c, RunInvariant impl.finish.program (· = raw y impl.finish.tapes) c →
      ∀ j, lo ≤ c.head j ∧ c.head j ≤ hi
  pop : ∀ y, S.Finished σ x₀ y → ∀ j,
    lo+(k+1 : ℕ) ≤ (raw y (tapeCount pieces capacity stack ht impl)).head j ∧
      (raw y (tapeCount pieces capacity stack ht impl)).head j+(k+1 : ℕ) ≤ hi

theorem frame_run_within (σ : S.Shape) (x₀ : Tapes t a) (hx : S.Entry σ x₀)
    (lo hi : ℤ) (F : FrameBounds (ht := ht) S σ x₀ lo hi)
    (hchild : m ≤ S.size σ → ChildrenWithin (ht := ht) S
      (fun v => ∀ j, lo ≤ v.head j ∧ v.head j ≤ hi) σ x₀) :
    ContractWithin (ht := ht) S (fun v => ∀ j, lo ≤ v.head j ∧ v.head j ≤ hi) σ x₀ := by
  obtain ⟨yl,hyl,nl,hrl⟩ := leaves_run_within S σ x₀ hx lo hi F.lower_nonpos F.upper_nonneg
    F.prepare F.leaf F.test
  by_cases hm : m ≤ S.size σ
  · simp only [hm,ite_true] at hrl
    obtain ⟨yn,hyn,hsp⟩ := S.split σ x₀ yl hx hm hyl
    obtain ⟨ns,_,hrs⟩ := block_jump_within_heads pieces capacity stack ht impl .split (first pieces)
      yl yn (S.cSplit σ) hsp (fun _ => rfl) lo hi F.lower_nonpos F.upper_nonneg (F.split yl hyl)
    have hp := piece_run_within S σ x₀ hx hm lo hi F.lower_nonpos F.upper_nonneg
      F.segment F.enter (hchild hm) F.recover
    obtain ⟨ym,hym,nsc,hrsc⟩ := schedule_run_within S σ x₀ lo hi yn hyn hrs.finish hp
    obtain ⟨yd,hyd,hmg⟩ := S.merge σ x₀ ym hx hm hym
    obtain ⟨nm,_,hrm⟩ := block_jump_within_heads pieces capacity stack ht impl .merge .finish
      ym yd (S.cMerge σ) hmg (fun _ => rfl) lo hi F.lower_nonpos F.upper_nonneg (F.merge ym hym)
    obtain ⟨z,hz,nt,hrt⟩ := tail_run_within S σ x₀ hx lo hi F.lower_nonpos F.upper_nonneg
      yd hyd (F.finish yd hyd) F.pop
    exact ⟨z,hz,nl+ns+nsc+nm+nt,(((hrl.trans hrs).trans hrsc).trans hrm).trans hrt⟩
  · simp only [hm,ite_false] at hrl
    have hyd := S.done_leaf σ x₀ yl hx hm hyl
    obtain ⟨z,hz,nt,hrt⟩ := tail_run_within S σ x₀ hx lo hi F.lower_nonpos F.upper_nonneg
      yl hyd (F.finish yl hyd) F.pop
    exact ⟨z,hz,nl+nt,hrl.trans hrt⟩

/-- Strong induction closes the recursion once local block bounds and the
ordinary child-entry invariant are established. No child execution oracle remains. -/
theorem contract_within (Safe : S.Shape → Tapes t a → Prop) (lo hi : ℤ)
    (hm : 0 < m) (hrank : ∀ r ∈ GraphContract.ranks rank pieces, r < m)
    (hlocal : ∀ σ x₀, S.Entry σ x₀ → Safe σ x₀ → FrameBounds (ht := ht) S σ x₀ lo hi)
    (hchild : ∀ σ x₀, S.Entry σ x₀ → Safe σ x₀ → m ≤ S.size σ →
      ∀ (i : Site pieces) (c : Call), pieces[i] = .call c → ∀ y, S.Node σ x₀ i.val y →
        ∀ C : ChildStep S σ x₀ y i c, Safe C.child C.entered) :
    ∀ σ x₀, S.Entry σ x₀ → Safe σ x₀ →
      ContractWithin (ht := ht) S (fun v => ∀ j, lo ≤ v.head j ∧ v.head j ≤ hi) σ x₀ := by
  have hmain : ∀ n, ∀ σ x₀, S.size σ = n → S.Entry σ x₀ → Safe σ x₀ →
      ContractWithin (ht := ht) S (fun v => ∀ j, lo ≤ v.head j ∧ v.head j ≤ hi) σ x₀ := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro σ x₀ hn hx hs
      apply frame_run_within S σ x₀ hx lo hi (hlocal σ x₀ hx hs)
      intro hnode i c hic y hy C
      have hr := hrank (rank c) (GraphContract.rank_mem rank pieces i.val i.isLt c hic)
      have hf : 0 < S.size σ/m := Nat.div_pos hnode hm
      have hlt : S.size C.child < S.size σ := by
        rw [C.size]
        exact (Nat.mul_lt_mul_of_pos_right hr hf).trans_le (Nat.mul_div_le _ _)
      exact ih (S.size C.child) (by omega) C.child C.entered rfl C.entry
        (hchild σ x₀ hx hs hnode i c hic y hy C)
  intro σ x₀ hx hs
  exact hmain (S.size σ) σ x₀ rfl hx hs

/-- At the root, the bounded halting certificate covers every actual reachable
configuration, independently of the separately proved runtime estimate. -/
theorem ContractWithin.prefix {H : TapePred (tapeCount pieces capacity stack ht impl) a}
    {σ : S.Shape} {x₀ : Tapes t a} (h : ContractWithin (ht := ht) S H σ x₀)
    (hret : S.ret σ = .halt) {n : ℕ} {z}
    (hr : run (program pieces capacity stack ht impl) n
      (entryConfig pieces capacity stack ht impl .prepare x₀) = some z) : H z.tapes := by
  obtain ⟨y,_,m,hm⟩ := h
  rw [hret] at hm
  exact hm.prefix_of_halt (entry_halt pieces capacity stack ht impl y) hr

end
end IntegerMultBounds.MathlibTM2.M8.RevMachine.GraphExists
