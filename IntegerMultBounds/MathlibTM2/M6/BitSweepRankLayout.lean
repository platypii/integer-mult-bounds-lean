module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackFormulaLayout
public import IntegerMultBounds.MathlibTM2.M6.BitSweepBinaryRank

/-! Allocate the rank evaluator while preserving the coordinate evaluator's tape bank. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine Cover.Fallback RingFormula Host Stack Node

/-- The two modular evaluators use disjoint frames. A rank operand may
be live while the coordinate evaluator borrows the other operand as output. -/
theorem sweepRankLayout_prepared {T D E A M : ℕ} [NeZero M]
    (rankPool : Fin ((D+1)*13) ↪ Fin T) (coordPool : Fin ((E+1)*13) ↪ Fin T)
    (source : Leaf (Entry Bool 64) → Fin 7 ↪ Fin T)
    (constant : Leaf (Option (Fin 128)) → Fin 4 ↪ Fin T)
    (disjoint : ∀ i j, coordPool i ≠ rankPool j) (sources : ∀ a i j, source a i ≠ rankPool j)
    (localSources : ∀ a i j, source a i ≠ coordPool j) (constants : ∀ a i j, constant a i ≠ rankPool j)
    (H : ℕ) (mat : Bool → Matrix (Fin 64) (Fin 64) (ZMod M))
    (f : Fin 128 → RingFormula (Entry Bool 64)) (rankDepth : sweepBinaryRankCode.depth ≤ D)
    (coordDepth : ∀ i, (f i).depth ≤ E) (out : Fin T) (R : Regs T A)
    (empty : R out = []) (outside : ∀ i, rankPool i ≠ out) (coordOut : ∀ i, coordPool i ≠ out)
    (sourceOut : ∀ a i, source a i ≠ out) (constantOut : ∀ a i, constant a i ≠ out)
    (rankMod : ∀ k ≤ D, R (frame rankPool k 2) = binSyms H (M^128))
    (coordMod : ∀ k ≤ E, R (frame coordPool k 2) = binSyms H M)
    (rankFree : ∀ k ≤ D, ∀ i : Fin 13, i ≠ 2 → R (frame rankPool k i) = [])
    (coordFree : ∀ k ≤ E, ∀ i : Fin 13, i ≠ 2 → R (frame coordPool k i) = [])
    (inputs : ∀ a, leafReady (fun b _ => source b) mat H a (source a 3) R) :
    let x := fun i => eval (entryValue mat) (f i)
    let regs := fun a dst => (constant a).trans (Equiv.swap (constant a 1) dst).toEmbedding
    let leaf := fun i => prepared (registerBank coordPool) (entryValue mat) H
      (leafReady (leafBank source) mat H) (f i) 0
    (∀ a, (∀ i, a ≠ Leaf.input (some i)) →
      R (constant a 0) = binSyms H (a.value (rankInput x)).val ∧
      R (constant a 2) = [] ∧ R (constant a 3) = []) →
    prepared (registerBank rankPool) (rankInput x) H (rankLeafReady H x leaf regs)
      sweepBinaryRankCode 0 out R := by
  intro x regs leaf words
  let allowed := fun dst => (∀ i, coordPool i ≠ dst) ∧ (∀ a i, source a i ≠ dst) ∧ (∀ a i, constant a i ≠ dst)
  let ok := fun (S : Regs T A) => ∀ t, (∀ j, t ≠ rankPool j) → S t = R t
  apply layout_prepared_of_invariant rankPool _ H _ R _ 0 out (by simpa using rankDepth) empty
    (fun _ _ _ _ => outside _) (fun k _ => rankMod k) (fun k _ => rankFree k) allowed
    ⟨coordOut,sourceOut,constantOut⟩ (fun _ _ _ _ => ⟨fun i => disjoint i _,fun a i => sources a i _,fun a i => constants a i _⟩)
    ok (fun _ _ => rfl)
  · intro S agree a dst hd blank
    have copy (h : ∀ i, a ≠ Leaf.input (some i)) :
        regs a dst 1 = dst ∧ S (regs a dst 0) = binSyms H (a.value (rankInput x)).val ∧
        S (regs a dst 2) = [] ∧ S (regs a dst 3) = [] := by
      have slot (i : Fin 4) (hi : i ≠ 1) : regs a dst i = constant a i :=
        Equiv.swap_apply_of_ne_of_ne ((constant a).injective.ne hi) (hd.2.2 a i)
      refine ⟨Equiv.swap_apply_left ..,?_⟩
      simpa only [slot 0 (by decide),slot 2 (by decide),slot 3 (by decide),agree _ (constants a _)] using
        (words a h)
    cases a with
    | zero | one => exact copy (by simp)
    | input i =>
      cases i with
      | none => exact copy (by simp)
      | some i =>
        apply allocated_prepared coordPool source localSources mat H _ (coordDepth i) dst hd.1 hd.2.1 S blank
        · intro k hk; exact (agree _ (disjoint _)).trans (coordMod k hk)
        · intro k hk j hj; exact (agree _ (disjoint _)).trans (coordFree k hk j hj)
        · intro a
          have same (j) := agree _ (sources a j)
          have h := inputs a
          cases a with
          | zero | one => simpa only [leafReady,same] using h
          | input a => obtain ⟨b,i,j⟩ := a; simpa only [leafReady,same] using h
  · intro S agree k xs t ht
    exact (Function.update_of_ne (ht _) _ _).trans (agree t ht)

end IntegerMultBounds.MathlibTM2.M6.BitNode
