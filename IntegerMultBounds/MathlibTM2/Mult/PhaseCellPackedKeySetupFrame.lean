module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedHaloSourceFrame
public import IntegerMultBounds.MathlibTM2.Host.EmbedUpdate

/-! The actual input stage preserves the packed factory's entire setup contract. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  ScalarPlacement

def packedKeySetupReg : Fin 242 → Fin 276 := Fin.castLE (by decide)

theorem packedKeySetupReg_injective : Function.Injective packedKeySetupReg := by
  intro i j he
  apply Fin.ext
  exact congrArg (fun k : Fin 276 => k.val) he

theorem packedKeySetupReg_off (j : Fin 276) (hj : 242 ≤ j.val) : ∀ i, packedKeySetupReg i ≠ j := by
  intro i he
  have hv := congrArg Fin.val he
  have hi := i.isLt
  change i.val = j.val at hv
  omega

/-- Queue and publication-count writes are outside the factory bank. -/
theorem packedKeyInput_setup_view {A : ℕ} (S : Stacks 276 A)
    (tail rhs count : List (Fin (A+4))) :
    embStk packedKeySetupReg {S with R := (Function.update
      (Function.update (Function.update S.R 263 tail) 110 rhs) 251 count)} =
      {embStk packedKeySetupReg S with R := Function.update (embStk packedKeySetupReg S).R 110 rhs} := by
  let M : Stacks 276 A := {S with R := Function.update S.R 263 tail}
  let F : Stacks 276 A := {M with R := Function.update M.R (packedKeySetupReg 110) rhs}
  change embStk packedKeySetupReg {F with R := Function.update F.R 251 count} = _
  rw [embStk_updateR_off F 251 count (packedKeySetupReg_off 251 (by decide))]
  dsimp only [F]
  rw [embStk_updateR packedKeySetupReg_injective]
  dsimp only [M]
  rw [embStk_updateR_off S 263 tail (packedKeySetupReg_off 263 (by decide))]

/-- Every existing packed setup field transports through the executed input
state. Source readiness is updated once by the supplier's own structural lemma. -/
theorem PackedHaloSetup.packed_key_input {freshGeometry : Bool}
    {A p l s t u target rhsExp a b V : ℕ} [NeZero s] {α d : ℝ}
    {C : ZMod s → GaussianInt} {S : Stacks 276 A}
    (h : PackedHaloSetup (freshGeometry := freshGeometry) (p := p) (l := l) (t := t) (u := u)
      (target := target) (rhsExp := rhsExp) (a := a) (b := b) (V := V) α d C (embStk packedKeySetupReg S))
    (tail rhs count : List (Fin (A+4))) :
    PackedHaloSetup (freshGeometry := freshGeometry) (p := p) (l := l) (t := t) (u := u)
      (target := target) (rhsExp := rhsExp) (a := a) (b := b) (V := V) α d C
      (embStk packedKeySetupReg {S with R := (Function.update
        (Function.update (Function.update S.R 263 tail) 110 rhs) 251 count)}) := by
  rw [packedKeyInput_setup_view]
  exact h.update_source rhs

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
