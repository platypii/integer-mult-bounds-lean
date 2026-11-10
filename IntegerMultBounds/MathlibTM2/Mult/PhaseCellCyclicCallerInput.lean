module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFittingCyclicComplexCaller

/-! Ordinary caller context and the three owned input ports. These separate
preserved seed/control data from the payload produced by tensor selection. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.CyclicComplexCallerLayout
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {T A s : ℕ} [NeZero s]

structure InputContext (ports : CyclicComplexCallerLayout T) (H K : ReplicaHaloProblem s)
    (W N radius rows : ℕ) (S : Stacks T A) : Prop where
  bank : ∀ i, S.L (ports.bank i) = [] ∧ S.R (ports.bank i) = []
  seedL : ∀ i ∈ recoverySeedHeaderPorts, (S.R (ports.seedL i)).length = recoverySeedHeader H W N i
  seedR : ∀ i ∈ recoverySeedHeaderPorts, (S.R (ports.seedR i)).length = recoverySeedHeader K W N i
  controls : ∀ i, (S.R (ports.controls i)).length = ![W,radius,rows] i
  saved : S.R ports.saved = []
  tmp : S.R ports.tmp = []

structure PackedInput (ports : CyclicComplexCallerLayout T) (H K : ReplicaHaloProblem s)
    (Fs : List (ZMod s → GaussianInt)) (a n W radius rows : ℕ) (S : Stacks T A) : Prop
    extends InputContext ports H K W Fs.length radius rows S where
  archive : S.R ports.archive = cstream A W (Fs.map (packedInterval a n)).flatten
  count : (S.R ports.count).length = Fs.length*n*W
  span : (S.R ports.span).length = n

/-- Exactly the right stacks observed by ordinary context readiness. -/
def contextSupport (ports : CyclicComplexCallerLayout T) (r : Fin T) : Prop :=
  (∃ i, ports.bank i = r) ∨
  (∃ i ∈ recoverySeedHeaderPorts, ports.seedL i = r ∨ ports.seedR i = r) ∨
  (∃ i, ports.controls i = r) ∨ r ∈ [ports.saved,ports.tmp]

theorem InputContext.frame {ports : CyclicComplexCallerLayout T} {H K : ReplicaHaloProblem s}
    {W N radius rows : ℕ} {S F : Stacks T A}
    (h : InputContext ports H K W N radius rows S)
    (hleft : ∀ i, F.L (ports.bank i) = S.L (ports.bank i))
    (hframe : ∀ r, contextSupport ports r → F.R r = S.R r) :
    InputContext ports H K W N radius rows F := by
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · intro i
    rw [hleft i,hframe _ (Or.inl ⟨i,rfl⟩)]
    exact h.bank i
  · intro i hi
    rw [hframe _ (Or.inr (Or.inl ⟨i,hi,Or.inl rfl⟩))]
    exact h.seedL i hi
  · intro i hi
    rw [hframe _ (Or.inr (Or.inl ⟨i,hi,Or.inr rfl⟩))]
    exact h.seedR i hi
  · intro i
    rw [hframe _ (Or.inr (Or.inr (Or.inl ⟨i,rfl⟩)))]
    exact h.controls i
  · rw [hframe _ (Or.inr (Or.inr (Or.inr (by simp))))]
    exact h.saved
  · rw [hframe _ (Or.inr (Or.inr (Or.inr (by simp))))]
    exact h.tmp

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.CyclicComplexCallerLayout
