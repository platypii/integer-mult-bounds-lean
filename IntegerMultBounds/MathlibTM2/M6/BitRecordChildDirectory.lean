module

public import IntegerMultBounds.MathlibTM2.M6.BitRecordChildBudget

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host
open RecursiveInterchangeLayout Certificates.PR589
open Shared50ModularControl (prime)

/-- Install a finite family of node entries in a single table. All entries
share the maximum tape capacity and one recurrence coefficient. -/
theorem splitRecordTreeDirectory [M8.Machine.Net] {I U : Type} [Fintype I]
    {P Config : I → Type} {N T : I → ℕ} {Q : ℕ}
    (input : ∀ i, Config i → CutoffNodeInput) (body : ∀ i, P i → Pr (P i) (N i) Q prime U)
    (dst : ∀ i, Fin (142081+2) ↪ Fin (N i)) (leafRate : ℝ) (budget : ∀ i, Config i → ℕ → ℕ)
    (family : ∀ i, SplitRecordTreeFamily (input i) (body i) (dst i) leafRate (budget i))
    (live : ∀ i, Fin (142080+2) ↪ Fin (T i)) (record : ∀ i, Fin 34 ↪ Fin (T i))
    (apart : ∀ i r j, 8 ≤ j.val → record i j ≠ live i r) :
    let size := fun i => 142082+T i+N i
    let H := Finset.univ.sup size
    let place := fun i => Fin.castLEEmb (Finset.le_sup (f := size) (Finset.mem_univ i))
    let Label := I ⊕ (Σ i, Empty ⊕ P i)
    ∃ (D : ℝ) (bank : ∀ i, Fin (N i) ↪ Fin (size i)) (table : Label → Pr Label H Q prime U),
      0 ≤ D ∧ (∀ i, ChildBankFrame (live i) (bank i)) ∧
      (∀ i f, table (.inr ⟨i,.inr f⟩) = embProg (place i) (fun g => Sum.inr ⟨i,g⟩)
        (embProg (bank i) Sum.inr (body i f))) ∧
      ∀ i x, let c := input i x
        c.cutoff < c.node.width →
        (∀ k : Fin nodeChildren5.length, let d := scheduledChild prime c.node k
          c.cutoff < d.width → budget i x k.val ≤ cutoffTreeBudget D leafRate c.cutoff
            (c.depth-(c.path.length+1)) d) →
        RecordChildCall c (live i) (record i) (dst i) (bank i) (place i) table (.inl i)
          (cutoffTreeBudget D leafRate c.cutoff (c.depth-c.path.length) c.node) := by
  classical
  intro size H place Label
  choose minimum nonneg build using family
  let D := ∑ i, minimum i
  have enough i : minimum i ≤ D := Finset.single_le_sum (fun j _ => nonneg j) (Finset.mem_univ i)
  choose bank host program installed frame exec using fun i => build i D (enough i) (live i) (record i) (apart i)
  refine ⟨D,bank,recordChildDirectory place host program,Finset.sum_nonneg (fun i _ => nonneg i),frame,?_,?_⟩
  · intro i f
    change embProg (place i) _ (host i (.inr f)) = _
    rw [installed i f]
  · intro i x c active children
    exact InstalledRecordChildExec.inDirectory place host program i (exec i x active children).2

end IntegerMultBounds.MathlibTM2.M6.BitNode
