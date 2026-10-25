module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpOutputLayout
public import IntegerMultBounds.MathlibTM2.Mult.ChirpOutputFactorSetup

/-! # Generated factor tapes establish the complete output caller's data interface -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host

/-- The output data bank before installing the two computed factor tapes. -/
structure ChirpOutputBase {T A : ℕ} (O : ChirpOutputLayout T) (S : Stacks T A)
    (q w : ℕ) (blocks : List (List GaussianInt)) : Prop where
  cr_ready : Ready (fun r => S.R (O.cr r)) w q
  nr_ready : Ready (fun r => S.R (O.nr r)) w q
  mul_clean : CClean O.mul S
  input : S.R (O.cr .xs) = cstream A w blocks.flatten
  cr_empty : ∀ r ∈ [CR.ys, .xsv, .ysv, .acc, .out], S.R (O.cr r) = []
  nr_empty : ∀ r ∈ [CR.ys, .xsv, .ysv, .acc, .out], S.R (O.nr r) = []

/-- Only the intermediate E-product tape is shared between the two data banks. -/
def ChirpOutputLayout.Cross {T : ℕ} (O : ChirpOutputLayout T) : Prop :=
  ∀ r s, r ≠ .xs → O.nr r ≠ O.cr s

/-- The first factor tape is outside the entire normalization bank. -/
theorem ChirpOutputLayout.factor_nr {T : ℕ} (O : ChirpOutputLayout T) (hc : O.Cross) (r : CR) :
    O.cr .ys ≠ O.nr r := by
  by_cases hr : r = .xs
  · subst r
    rw [O.link]
    exact O.cr_inj.ne (by decide)
  · exact (hc r .ys hr).symm

/-- Installing generated factors preserves all working state and establishes the arithmetic interface. -/
theorem ChirpOutputBase.installFactors {T A : ℕ} {O : ChirpOutputLayout T} {S : Stacks T A}
    {q w : ℕ} {blocks : List (List GaussianInt)} (h : ChirpOutputBase O S q w blocks)
    (hc : O.Cross) (es : List ℤ) (a : ℤ) :
    ChirpOutputState O
      { S with R := (Function.update
        (Function.update S.R (O.cr .ys) (cstream A w (es.map fun e => (⟨e, 0⟩ : GaussianInt))))
        (O.nr .ys) (csyms A w (⟨a, 0⟩ : GaussianInt))) } q w blocks es a := by
  let E := cstream A w (es.map fun e => (⟨e, 0⟩ : GaussianInt))
  let N := csyms A w (⟨a, 0⟩ : GaussianInt)
  let S₁ : Stacks T A := { S with R := Function.update S.R (O.cr .ys) E }
  let S₂ : Stacks T A := { S₁ with R := Function.update S₁.R (O.nr .ys) N }
  let ρ := fun r => S.R (O.cr r)
  let ν := fun r => S.R (O.nr r)
  have hcr₁ : CHolds O.cr S₁ (Function.update ρ CR.ys E) := holds_upd O.cr_inj (fun _ => rfl) .ys E
  have hcr₂ : CHolds O.cr S₂ (Function.update ρ CR.ys E) := by
    intro r
    simpa only [S₂, Function.update_of_ne (hc .ys r (by decide)).symm] using hcr₁ r
  have hnr₁ : CHolds O.nr S₁ ν := by
    intro r
    change Function.update S.R (O.cr .ys) E (O.nr r) = ν r
    rw [Function.update_of_ne (O.factor_nr hc r).symm]
  have hnr₂ : CHolds O.nr S₂ (Function.update ν CR.ys N) := holds_upd O.nr_inj hnr₁ .ys N
  have cr_eq : (fun r => S₂.R (O.cr r)) = Function.update ρ CR.ys E := funext hcr₂
  have nr_eq : (fun r => S₂.R (O.nr r)) = Function.update ν CR.ys N := funext hnr₂
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change Ready (fun r => S₂.R (O.cr r)) w q
    rw [cr_eq]
    exact h.cr_ready.update .ys (by simp) E
  · change Ready (fun r => S₂.R (O.nr r)) w q
    rw [nr_eq]
    exact h.nr_ready.update .ys (by simp) N
  · intro j
    exact ⟨(h.mul_clean j).1, by
      change Function.update (Function.update S.R (O.cr .ys) E) (O.nr .ys) N (O.mul j) = []
      rw [Function.update_of_ne (O.nr_mul .ys j).symm,
        Function.update_of_ne (O.cr_mul .ys j).symm]
      exact (h.mul_clean j).2⟩
  · exact (hcr₂ .xs).trans (by simpa only [ρ, Function.update_of_ne (by decide : CR.xs ≠ .ys)] using h.input)
  · exact (hcr₂ .ys).trans (Function.update_self ..)
  · exact (hnr₂ .ys).trans (Function.update_self ..)
  · intro r hr
    have hrys : r ≠ .ys := by intro he; subst r; simp at hr
    exact (hcr₂ r).trans (by
      rw [Function.update_of_ne hrys]
      exact h.cr_empty r (List.mem_cons_of_mem _ hr))
  · intro r hr
    have hrys : r ≠ .ys := by intro he; subst r; simp at hr
    exact (hnr₂ r).trans (by
      rw [Function.update_of_ne hrys]
      exact h.nr_empty r (List.mem_cons_of_mem _ hr))

/-- Clearing owned factor tapes after the output call restores their original empty registers.
The proof is independent of all stream contents and coefficient arithmetic. -/
theorem ChirpOutputLayout.clearFactors {T A : ℕ} (O : ChirpOutputLayout T) (hc : O.Cross)
    (R : Fin T → List (Fin (A + 4))) (E N output : List (Fin (A + 4)))
    (hE : R (O.cr .ys) = []) (hN : R (O.nr .ys) = []) :
    (fun k => if k ∈ [O.cr .ys, O.nr .ys] then [] else
      Function.update (Function.update
        (Function.update (Function.update R (O.cr .ys) E) (O.nr .ys) N)
        (O.cr .xs) []) (O.nr .out) output k) =
      Function.update (Function.update R (O.cr .xs) []) (O.nr .out) output := by
  funext k
  by_cases he : k = O.cr .ys
  · subst k
    simp only [List.mem_cons, true_or, ite_true,
      Function.update_of_ne (O.factor_nr hc .out),
      Function.update_of_ne (O.cr_inj.ne (by decide : CR.ys ≠ .xs)), hE]
  by_cases hn : k = O.nr .ys
  · subst k
    simp only [List.mem_cons, true_or, or_true, ite_true,
      Function.update_of_ne (O.nr_inj.ne (by decide : CR.ys ≠ .out)),
      Function.update_of_ne (O.input_frame .ys), hN]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, he, hn, ite_false]
    by_cases hx : k = O.cr .xs
    · subst k
      simp only [Function.update_of_ne (O.input_frame .out).symm, Function.update_self]
    by_cases ho : k = O.nr .out
    · subst k
      simp only [Function.update_self]
    · simp only [Function.update_of_ne hx, Function.update_of_ne ho,
        Function.update_of_ne he, Function.update_of_ne hn]

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
