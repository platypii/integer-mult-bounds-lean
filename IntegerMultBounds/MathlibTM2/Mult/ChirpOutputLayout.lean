module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpOutputComplete
public import IntegerMultBounds.MathlibTM2.Mult.ChirpOutputDimensionSetup

/-! # One register interface for the complete output caller

Nine counters and thirteen scratch words share an injective metadata bank. The
normalization input is the E-product output; all metadata is separate from data
and the shared multiplier bank.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Layer
  IntegerMultBounds.MathlibTM2.Node

structure ChirpOutputLayout (T : ℕ) where
  cr : CR → Fin T
  nr : CR → Fin T
  mul : Fin 64 → Fin T
  bank : Fin 22 → Fin T
  cr_inj : Function.Injective cr
  nr_inj : Function.Injective nr
  mul_inj : Function.Injective mul
  bank_inj : Function.Injective bank
  cr_mul : ∀ r i, cr r ≠ mul i
  nr_mul : ∀ r i, nr r ≠ mul i
  bank_cr : ∀ i r, bank i ≠ cr r
  bank_nr : ∀ i r, bank i ≠ nr r
  bank_mul : ∀ i j, bank i ≠ mul j
  link : nr .xs = cr .out
  input_frame : ∀ r, nr r ≠ cr .xs

def ChirpOutputLayout.dim {T : ℕ} (O : ChirpOutputLayout T) (i : Fin 9) : Fin T :=
  O.bank (Fin.castLE (by decide) i)

theorem ChirpOutputLayout.dim_inj {T : ℕ} (O : ChirpOutputLayout T) : Function.Injective O.dim :=
  O.bank_inj.comp (Fin.castLE_injective _)

/-- The program text depends only on register placement and finite multiplier sizes. -/
noncomputable def chirpOutputRun {T Q A : ℕ} {P U : Type} (O : ChirpOutputLayout T)
    (hT : 64 ≤ T) (hQ : SS.states ≤ Q) : Pr P T Q A U :=
  .seq (.seq
    (.seq (shiftInto (O.cr .xs) (O.bank 9) (O.cr .xs) (O.dim 0) (O.dim 1)
      (O.bank 10) (O.bank 11) (pairSym A false false))
      (cmulTable O.cr (rmulOne O.mul O.mul_inj hT hQ O.cr)))
    (.seq (shiftInto (O.nr .xs) (O.bank 12) (O.nr .xs) (O.dim 2) (O.dim 3)
      (O.bank 13) (O.bank 14) (pairSym A false false))
      (cmulTable O.nr (rmulOne O.mul O.mul_inj hT hQ O.nr))))
    (.seq (.seq (topPass (O.nr .out) (O.bank 15)
      (topShiftWord (O.nr .out) (O.bank 15) (O.bank 16) (O.dim 4) (O.dim 5) (O.dim 6) (O.dim 7)
        (O.bank 17) (O.bank 18) (O.bank 19)))
      (chirpCrop (O.dim 8) (O.nr .out) (O.bank 20) (O.bank 21)))
      (clearWords [O.cr .xs, O.nr .xs]))

/-- The data-facing preconditions before generating the nine output counters. -/
structure ChirpOutputState {T A : ℕ} (O : ChirpOutputLayout T) (S : Stacks T A)
    (q w : ℕ) (blocks : List (List GaussianInt)) (es : List ℤ) (a : ℤ) : Prop where
  cr_ready : Ready (fun r => S.R (O.cr r)) w q
  nr_ready : Ready (fun r => S.R (O.nr r)) w q
  mul_clean : CClean O.mul S
  input : S.R (O.cr .xs) = cstream A w blocks.flatten
  factors : S.R (O.cr .ys) = cstream A w (es.map fun e => (⟨e, 0⟩ : GaussianInt))
  normalization : S.R (O.nr .ys) = csyms A w (⟨a, 0⟩ : GaussianInt)
  cr_empty : ∀ r ∈ [CR.xsv, .ysv, .acc, .out], S.R (O.cr r) = []
  nr_empty : ∀ r ∈ [CR.xsv, .ysv, .acc, .out], S.R (O.nr r) = []

/-- Installing disjoint counters preserves the entire data/multiplier interface. -/
theorem ChirpOutputState.install {T A : ℕ} {O : ChirpOutputLayout T} {S : Stacks T A}
    {q w : ℕ} {blocks : List (List GaussianInt)} {es : List ℤ} {a : ℤ}
    (h : ChirpOutputState O S q w blocks es a) (p l Γ t : ℕ) :
    ChirpOutputState O
      { S with R := (unaryCopiesR (chirpOutputDimensionValues p q l Γ w t) S.R
        (chirpOutputAssignments O.dim)) } q w blocks es a := by
  let R := unaryCopiesR (chirpOutputDimensionValues p q l Γ w t) S.R (chirpOutputAssignments O.dim)
  have off (k : Fin T) (hk : ∀ i, k ≠ O.dim i) : R k = S.R k :=
    chirpOutputDimensions_off O.dim p q l Γ w t S.R k hk
  have hcr : (fun r => R (O.cr r)) = (fun r => S.R (O.cr r)) := by
    funext r
    exact off _ (fun i => (O.bank_cr _ r).symm)
  have hnr : (fun r => R (O.nr r)) = (fun r => S.R (O.nr r)) := by
    funext r
    exact off _ (fun i => (O.bank_nr _ r).symm)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change Ready (fun r => R (O.cr r)) w q
    rw [hcr]
    exact h.cr_ready
  · change Ready (fun r => R (O.nr r)) w q
    rw [hnr]
    exact h.nr_ready
  · exact fun j => ⟨(h.mul_clean j).1,
      (off _ (fun i => (O.bank_mul _ j).symm)).trans (h.mul_clean j).2⟩
  · exact (congrFun hcr .xs).trans h.input
  · exact (congrFun hcr .ys).trans h.factors
  · exact (congrFun hnr .ys).trans h.normalization
  · exact fun r hr => (congrFun hcr r).trans (h.cr_empty r hr)
  · exact fun r hr => (congrFun hnr r).trans (h.nr_empty r hr)

/-- Supplying correlation rows changes only the input tape and preserves output setup. -/
theorem ChirpOutputState.supplyInput {T A : ℕ} {O : ChirpOutputLayout T} {S : Stacks T A}
    {q w : ℕ} {es : List ℤ} {a : ℤ} (h : ChirpOutputState O S q w [] es a)
    (blocks : List (List GaussianInt)) :
    ChirpOutputState O { S with R := Function.update S.R (O.cr .xs) (cstream A w blocks.flatten) }
      q w blocks es a := by
  let xs := cstream A w blocks.flatten
  let R := Function.update S.R (O.cr .xs) xs
  have hcr : (fun r => R (O.cr r)) = Function.update (fun r => S.R (O.cr r)) CR.xs xs := by
    funext r
    by_cases hr : r = .xs
    · subst r; simp [R]
    · simp [R, hr, O.cr_inj.ne hr]
  have hnr : (fun r => R (O.nr r)) = (fun r => S.R (O.nr r)) := by
    funext r
    exact Function.update_of_ne (O.input_frame r) _ _
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change Ready (fun r => R (O.cr r)) w q
    rw [hcr]
    exact h.cr_ready.update .xs (by simp) xs
  · change Ready (fun r => R (O.nr r)) w q
    rw [hnr]
    exact h.nr_ready
  · exact fun i => ⟨(h.mul_clean i).1,
      (Function.update_of_ne (O.cr_mul .xs i).symm _ _).trans (h.mul_clean i).2⟩
  · exact Function.update_self _ _ _
  · exact (Function.update_of_ne (O.cr_inj.ne (show CR.ys ≠ .xs from by intro he; cases he)) _ _).trans h.factors
  · exact (congrFun hnr .ys).trans h.normalization
  · intro r hr
    have hne : r ≠ .xs := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide
    exact (Function.update_of_ne (O.cr_inj.ne hne) _ _).trans (h.cr_empty r hr)
  · exact fun r hr => (congrFun hnr r).trans (h.nr_empty r hr)

/-- Consuming the supplied correlation tape restores its original empty source. -/
theorem ChirpOutputLayout.consumeInput {T A : ℕ} (O : ChirpOutputLayout T)
    (R : Regs T A) (hblank : R (O.cr .xs) = []) (input output : List (Fin (A + 4))) :
    Function.update (Function.update (Function.update R (O.cr .xs) input) (O.cr .xs) [])
      (O.nr .out) output = Function.update R (O.nr .out) output := by
  funext k
  by_cases ho : k = O.nr .out
  · subst k; simp
  · by_cases hi : k = O.cr .xs
    · subst k; simp [ho, hblank]
    · simp [ho, hi]

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
