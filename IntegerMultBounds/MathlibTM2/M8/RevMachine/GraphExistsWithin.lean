module

public import IntegerMultBounds.MathlibTM2.M8.RevMachine.GraphExists
public import IntegerMultBounds.MathlibTM2.M8.RevMachine.GraphControlWithin

/-! Prefix bounds follow the same frame decomposition as the execution proof.
All phases share one head interval; repeated leaves do not add allowances. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.RevMachine.GraphExists
open IntegerMultBounds.Machine Graph GraphRun
open SharedBankStageInput (raw)
noncomputable section

/-- A structural chain of bounded runs, with a shape predicate at its boundaries. -/
theorem chain_within {β : Type} {t q a : ℕ} {M : Program t q a}
    (cfg : ℕ → β → Config t q a) (P : ℕ → β → Prop) (H : TapePred t a)
    (y₀ : β) (h₀ : P 0 y₀) (hsafe : H (cfg 0 y₀).tapes) :
    ∀ N, (∀ i < N, ∀ y, P i y → ∃ y', P (i+1) y' ∧
      ∃ n, RunWithin M H n (cfg i y) (cfg (i+1) y')) →
      ∃ y, P N y ∧ ∃ n, RunWithin M H n (cfg 0 y₀) (cfg N y)
  | 0, _ => ⟨y₀,h₀,0,RunWithin.refl hsafe⟩
  | N+1, h => by
    obtain ⟨y,hy,n,hr⟩ := chain_within cfg P H y₀ h₀ hsafe N (fun i hi => h i (by omega))
    obtain ⟨y',hy',m,hs⟩ := h N (by omega) y hy
    exact ⟨y',hy',n+m,hr.trans hs⟩

variable {Seg Call : Type} {t a k : ℕ} {pieces : List (Piece Seg Call)}
  {capacity : Fintype.card (PC pieces.length) ≤ 2^k} {stack : Fin t} {ht : 0 < t}
  {impl : Implementation t a k Seg Call} {m W : ℕ} {rank : Call → ℕ}
  (S : Inv pieces capacity stack impl m W rank)
  (σ : S.Shape) (x₀ : Tapes t a) (hx : S.Entry σ x₀)
  (lo hi : ℤ) (hlo : lo ≤ 0) (hhi : 0 ≤ hi)

include hx hlo hhi

theorem leaves_run_within
    (hprepare : ∀ c, RunInvariant impl.prepare.program (· = raw x₀ impl.prepare.tapes) c →
      ∀ j, lo ≤ c.head j ∧ c.head j ≤ hi)
    (hleaf : ∀ i < S.leaves σ, ∀ y, S.Leaf σ x₀ i y →
      ∀ c, RunInvariant impl.leaf.program (· = raw y impl.leaf.tapes) c →
        ∀ j, lo ≤ c.head j ∧ c.head j ≤ hi)
    (htest : ∀ i ≤ S.leaves σ, ∀ y, S.Leaf σ x₀ i y →
      ∀ j, lo+S.cTest σ ≤ (raw y (tapeCount pieces capacity stack ht impl)).head j ∧
        (raw y (tapeCount pieces capacity stack ht impl)).head j+S.cTest σ ≤ hi) :
    ∃ yl, S.Leaf σ x₀ (S.leaves σ) yl ∧ ∃ n,
      RunWithin (program pieces capacity stack ht impl)
        (fun v => ∀ j, lo ≤ v.head j ∧ v.head j ≤ hi) n
        (entryConfig pieces capacity stack ht impl .prepare x₀)
        (entryConfig pieces capacity stack ht impl
          (exitPC pieces (if m ≤ S.size σ then .node else .done)) yl) := by
  let H : TapePred (tapeCount pieces capacity stack ht impl) a :=
    fun v => ∀ j, lo ≤ v.head j ∧ v.head j ≤ hi
  let E := entryConfig pieces capacity stack ht impl
  obtain ⟨y₀,hy₀,hp⟩ := S.prepare σ x₀ hx
  obtain ⟨np,_,hrp⟩ := block_jump_within_heads pieces capacity stack ht impl .prepare .test
    x₀ y₀ (S.cPrepare σ) hp (fun _ => rfl) lo hi hlo hhi hprepare
  obtain ⟨yl,hyl,nl,hrl⟩ := chain_within (M := program pieces capacity stack ht impl)
    (fun _ y => E .test y) (S.Leaf σ x₀) H y₀ hy₀ hrp.finish (S.leaves σ)
    (fun i hiLeaf y hy => by
      obtain ⟨nt,_,hrt⟩ := test_run_within_heads pieces capacity stack ht impl y .leaf (S.cTest σ)
        (S.test_leaf σ x₀ i y hx hiLeaf hy) lo hi (htest i (by omega) y hy)
      obtain ⟨y',hy',hl⟩ := S.leaf σ x₀ i y hx hiLeaf hy
      obtain ⟨nb,_,hrb⟩ := block_jump_within_heads pieces capacity stack ht impl .leaf .test
        y y' (S.cLeaf σ) hl (fun _ => rfl) lo hi hlo hhi (hleaf i hiLeaf y hy)
      exact ⟨y',hy',nt+nb,hrt.trans hrb⟩)
  obtain ⟨nt,_,hrt⟩ := test_run_within_heads pieces capacity stack ht impl yl _ (S.cTest σ)
    (S.test_end σ x₀ yl hx hyl) lo hi (htest _ le_rfl yl hyl)
  exact ⟨yl,hyl,np+nl+nt,(hrp.trans hrl).trans hrt⟩

theorem tail_run_within (yd : Tapes t a) (hyd : S.Done σ x₀ yd)
    (hfinish : ∀ c, RunInvariant impl.finish.program (· = raw yd impl.finish.tapes) c →
      ∀ j, lo ≤ c.head j ∧ c.head j ≤ hi)
    (hpop : ∀ yf, S.Finished σ x₀ yf → ∀ j,
      lo+(k+1 : ℕ) ≤ (raw yf (tapeCount pieces capacity stack ht impl)).head j ∧
        (raw yf (tapeCount pieces capacity stack ht impl)).head j+(k+1 : ℕ) ≤ hi) :
    ∃ z, S.Exit σ x₀ z ∧ ∃ n,
      RunWithin (program pieces capacity stack ht impl)
        (fun v => ∀ j, lo ≤ v.head j ∧ v.head j ≤ hi) n
        (entryConfig pieces capacity stack ht impl .finish yd)
        (entryConfig pieces capacity stack ht impl (S.ret σ) z) := by
  obtain ⟨yf,hyf,hfin⟩ := S.finish σ x₀ yd hx hyd
  obtain ⟨nf,_,hrf⟩ := block_jump_within_heads pieces capacity stack ht impl .finish .pop
    yd yf (S.cFinish σ) hfin (fun _ => rfl) lo hi hlo hhi hfinish
  obtain ⟨z,hz,hp⟩ := S.pop σ x₀ yf hx hyf
  have hrp := pop_run_within_heads pieces capacity stack ht impl (S.ret σ) yf z hp lo hi (hpop yf hyf)
  exact ⟨z,hz,nf+(k+2),hrf.trans hrp⟩

end
end IntegerMultBounds.MathlibTM2.M8.RevMachine.GraphExists
