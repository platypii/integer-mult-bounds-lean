module

public import IntegerMultBounds.MathlibTM2.M8.RevMachine.GraphExistsWithin
public import IntegerMultBounds.MathlibTM2.M8.RevMachine.GraphCallWithin

/-! A child-call witness retains the existing geometry, entry execution and
recovery contract. Prefix bounds compose through that witness and the schedule. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.RevMachine.GraphExists
open IntegerMultBounds.Machine Graph GraphRun
open SharedBankStageInput (raw)
noncomputable section
variable {Seg Call : Type} {t a k : ℕ} {pieces : List (Piece Seg Call)}
  {capacity : Fintype.card (PC pieces.length) ≤ 2^k} {stack : Fin t} {ht : 0 < t}
  {impl : Implementation t a k Seg Call} {m W : ℕ} {rank : Call → ℕ}
  (S : Inv pieces capacity stack impl m W rank)

/-- The resource proof uses the same child selected by the execution contract. -/
structure ChildStep (σ : S.Shape) (x₀ y : Tapes t a) (i : Site pieces) (c : Call) where
  child : S.Shape
  entered : Tapes t a
  size : S.size child = rank c*(S.size σ/m)
  volume : (S.vol child : ℝ) = S.vol σ/W
  return_pc : S.ret child = .recover i
  entry : S.Entry child entered
  enterCost : ℕ
  recoverCost : ℕ
  cost : enterCost+recoverCost ≤ S.cCall σ c
  enter : GraphContract.Runs (impl.enter c (returnCode pieces capacity i)) y entered enterCost
  recover : ∀ z, S.Exit child entered z → ∃ y', S.Node σ x₀ (i.val+1) y' ∧
    GraphContract.Runs (impl.recover c) z y' recoverCost

theorem child_step (σ : S.Shape) (x₀ y : Tapes t a) (hx : S.Entry σ x₀) (hm : m ≤ S.size σ)
    (i : Site pieces) (c : Call) (hi : pieces[i] = .call c) (hy : S.Node σ x₀ i.val y) :
    Nonempty (ChildStep S σ x₀ y i c) := by
  obtain ⟨τ,y₁,hn,hv,hr,he,E,R,hER,henter,hrecover⟩ := S.call σ x₀ y hx hm i c hi hy
  exact ⟨⟨τ,y₁,hn,hv,hr,he,E,R,hER,henter,hrecover⟩⟩

/-- A frame certificate records all prefixes, with its original exit shape. -/
def ContractWithin (H : TapePred (tapeCount pieces capacity stack ht impl) a)
    (σ : S.Shape) (x₀ : Tapes t a) : Prop :=
  ∃ z, S.Exit σ x₀ z ∧ ∃ n, RunWithin (program pieces capacity stack ht impl) H n
    (entryConfig pieces capacity stack ht impl .prepare x₀)
    (entryConfig pieces capacity stack ht impl (S.ret σ) z)

/-- The recursive obligation applies to the execution contract's actual child witnesses. -/
def ChildrenWithin (H : TapePred (tapeCount pieces capacity stack ht impl) a)
    (σ : S.Shape) (x₀ : Tapes t a) : Prop :=
  ∀ (i : Site pieces) (c : Call), pieces[i] = .call c → ∀ y, S.Node σ x₀ i.val y →
    ∀ C : ChildStep S σ x₀ y i c, ContractWithin (ht := ht) S H C.child C.entered

variable (σ : S.Shape) (x₀ : Tapes t a) (hx : S.Entry σ x₀) (hm : m ≤ S.size σ)
  (lo upper : ℤ) (hlo : lo ≤ 0) (hupper : 0 ≤ upper)

include hx hm hlo hupper

theorem piece_run_within
    (hseg : ∀ (i : Site pieces) (s : Seg), pieces[i] = .seg s → ∀ y, S.Node σ x₀ i.val y →
      ∀ z, RunInvariant (impl.segment s).program (· = raw y (impl.segment s).tapes) z →
        ∀ j, lo ≤ z.head j ∧ z.head j ≤ upper)
    (henter : ∀ (i : Site pieces) (c : Call), pieces[i] = .call c → ∀ y, S.Node σ x₀ i.val y →
      ∀ z, RunInvariant (impl.enter c (returnCode pieces capacity i)).program
        (· = raw y (impl.enter c (returnCode pieces capacity i)).tapes) z →
        ∀ j, lo ≤ z.head j ∧ z.head j ≤ upper)
    (hchild : ChildrenWithin (ht := ht) S (fun v => ∀ j, lo ≤ v.head j ∧ v.head j ≤ upper) σ x₀)
    (hrecover : ∀ (i : Site pieces) (c : Call), pieces[i] = .call c → ∀ y, S.Node σ x₀ i.val y →
      ∀ C : ChildStep S σ x₀ y i c, ∀ z, S.Exit C.child C.entered z →
        ∀ d, RunInvariant (impl.recover c).program (· = raw z (impl.recover c).tapes) d →
          ∀ j, lo ≤ d.head j ∧ d.head j ≤ upper)
    (i : Site pieces) (y : Tapes t a) (hy : S.Node σ x₀ i.val y) :
    ∃ y', S.Node σ x₀ (i.val+1) y' ∧ ∃ n, RunWithin (program pieces capacity stack ht impl)
      (fun v => ∀ j, lo ≤ v.head j ∧ v.head j ≤ upper) n
      (entryConfig pieces capacity stack ht impl (.piece i) y)
      (entryConfig pieces capacity stack ht impl (successor pieces i) y') := by
  generalize hpc : pieces[i] = piece
  cases piece with
  | seg s =>
    obtain ⟨y',hy',hr⟩ := S.seg σ x₀ y hx hm i s hpc hy
    have hb : block pieces capacity stack ht impl (.piece i) = impl.segment s := by simp only [block,hpc]
    obtain ⟨n,_,hw⟩ := block_jump_within_heads pieces capacity stack ht impl (.piece i) (successor pieces i)
      y y' (S.cSeg σ s) (by rw [hb]; exact hr) (seg_edge pieces capacity stack ht impl i s hpc)
      lo upper hlo hupper (by rw [hb]; exact hseg i s hpc y hy)
    exact ⟨y',hy',n,hw⟩
  | call c =>
    obtain ⟨C⟩ := child_step S σ x₀ y hx hm i c hpc hy
    obtain ⟨z,hz,nc,hwc⟩ := hchild i c hpc y hy C
    rw [C.return_pc] at hwc
    obtain ⟨y',hy',hr⟩ := C.recover z hz
    obtain ⟨n,_,hw⟩ := call_jump_within_heads pieces capacity stack ht impl i c hpc y C.entered z y'
      C.enterCost C.recoverCost nc C.enter hr lo upper hlo hupper hwc
      (henter i c hpc y hy) (hrecover i c hpc y hy C z hz)
    exact ⟨y',hy',n,hw⟩

omit hx hm hlo hupper in
/-- The schedule induction is independent of the number and arrangement of calls. -/
theorem schedule_run_within (yn : Tapes t a) (hyn : S.Node σ x₀ 0 yn)
    (hsafe : ∀ j, lo ≤ (raw yn (tapeCount pieces capacity stack ht impl)).head j ∧
      (raw yn (tapeCount pieces capacity stack ht impl)).head j ≤ upper)
    (hpiece : ∀ (i : Site pieces) y, S.Node σ x₀ i.val y → ∃ y', S.Node σ x₀ (i.val+1) y' ∧
      ∃ n, RunWithin (program pieces capacity stack ht impl)
        (fun v => ∀ j, lo ≤ v.head j ∧ v.head j ≤ upper) n
        (entryConfig pieces capacity stack ht impl (.piece i) y)
        (entryConfig pieces capacity stack ht impl (successor pieces i) y')) :
    ∃ ym, S.Node σ x₀ pieces.length ym ∧ ∃ n, RunWithin (program pieces capacity stack ht impl)
      (fun v => ∀ j, lo ≤ v.head j ∧ v.head j ≤ upper) n
      (entryConfig pieces capacity stack ht impl (first pieces) yn)
      (entryConfig pieces capacity stack ht impl .merge ym) := by
  let E := entryConfig pieces capacity stack ht impl
  obtain ⟨ym,hym,n,hr⟩ := chain_within (M := program pieces capacity stack ht impl)
    (fun i y => E (position pieces i) y) (S.Node σ x₀)
    (fun v => ∀ j, lo ≤ v.head j ∧ v.head j ≤ upper) yn hyn hsafe pieces.length
    (fun i hi y hy => by
      have hp : position pieces i = .piece ⟨i,hi⟩ := by simp [position,hi]
      have hs : successor pieces ⟨i,hi⟩ = position pieces (i+1) := rfl
      obtain ⟨y',hy',n,hr⟩ := hpiece ⟨i,hi⟩ y hy
      exact ⟨y',hy',n,by rw [hp,←hs]; exact hr⟩)
  have hfirst : position pieces 0 = first pieces := by unfold position first; split_ifs <;> rfl
  have hlast : position pieces pieces.length = .merge := by simp [position]
  rw [hfirst,hlast] at hr
  exact ⟨ym,hym,n,hr⟩

end
end IntegerMultBounds.MathlibTM2.M8.RevMachine.GraphExists
