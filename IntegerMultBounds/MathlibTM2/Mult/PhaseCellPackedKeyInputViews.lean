module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedKeyPlacement
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedHaloPublishExec
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedHaloBatchProgram
public import IntegerMultBounds.MathlibTM2.Host.ExtendStacks

/-! Transport existing batch/factory views through the concrete input updates. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  ScalarPlacement

/-- Source and owned publication-count updates preserve the protected/native
view relation; the queue update is invisible to every native register. -/
theorem packedKeyInput_protected_view {A : ℕ} (S : Stacks 276 A) (B : Stacks 263 A)
    (hview : embStk packedKeySolverReg S = B)
    (tail rhs count : List (Fin (A+4))) :
    embStk packedKeySolverReg {S with R := (Function.update
      (Function.update (Function.update S.R 263 tail) 110 rhs) 251 count)} =
      {B with R := (Function.update (Function.update B.R 110 rhs) 251 count)} := by
  let M : Stacks 276 A := {S with R := (Function.update (Function.update S.R 263 tail) 110 rhs)}
  change embStk packedKeySolverReg {M with R := Function.update M.R (packedKeySolverReg 251) count} = _
  rw [embStk_updateR packedKeySolverReg_injective]
  rw [show embStk packedKeySolverReg M = {B with R := Function.update B.R 110 rhs} by
    rw [packedKeyInput_native_view,hview]]

/-- The publication bank's owned replica count is outside the lower batch view. -/
theorem packedKeyInput_publication_view {A : ℕ} (B : Stacks 263 A) (S₀ : Stacks 249 A)
    (hview : embStk packedHaloPublishedReg B = S₀)
    (rhs count : List (Fin (A+4))) :
    embStk packedHaloPublishedReg {B with R := (Function.update (Function.update B.R 110 rhs) 251 count)} =
      {S₀ with R := Function.update S₀.R 110 rhs} := by
  let M : Stacks 263 A := {B with R := Function.update B.R 110 rhs}
  have hoff : ∀ i, packedHaloPublishedReg i ≠ (251 : Fin 263) := by
    intro i he
    have hv := congrArg Fin.val he
    have hi := i.isLt
    change i.val = 251 at hv
    omega
  change embStk packedHaloPublishedReg {M with R := Function.update M.R 251 count} = _
  rw [embStk_updateR_off M 251 count hoff]
  dsimp only [M]
  have hinj : Function.Injective packedHaloPublishedReg := by
    intro i j h
    apply Fin.ext
    exact congrArg (fun k : Fin 263 => k.val) h
  have he := embStk_updateR hinj B 110 rhs
  simpa only [show packedHaloPublishedReg 110 = 110 by decide,hview] using he

/-- Updating the actual RHS preserves the extended factory/batch bank relation. -/
theorem packedKeyInput_batch_view {A : ℕ} (S₀ : Stacks 249 A) (S : Stacks 242 A)
    (hview : embStk packedHaloBatchReg S₀ = extendStacks (by decide) S)
    (rhs : List (Fin (A+4))) :
    embStk packedHaloBatchReg {S₀ with R := Function.update S₀.R 110 rhs} =
      extendStacks (by decide) {S with R := Function.update S.R 110 rhs} := by
  have hinj : Function.Injective packedHaloBatchReg := by
    intro i j h
    apply Fin.ext
    exact congrArg (fun k : Fin 249 => k.val) h
  have he := embStk_updateR hinj S₀ 110 rhs
  rw [show packedHaloBatchReg 110 = 110 by decide,hview] at he
  rw [he,extendStacks_updateR]
  rfl

/-- The three native bank views needed by the actual protected batch supplier. -/
structure PackedKeyBankViews {A : ℕ} (M : Stacks 276 A) (B : Stacks 263 A)
    (S₀ : Stacks 249 A) (S : Stacks 242 A) : Prop where
  protectedView : embStk packedKeySolverReg M = B
  publicationView : embStk packedHaloPublishedReg B = S₀
  batchView : embStk packedHaloBatchReg S₀ = extendStacks (by decide) S

/-- External queue/count writes preserve all native setup views. -/
theorem PackedKeyBankViews.external_update {A : ℕ} {M : Stacks 276 A} {B : Stacks 263 A}
    {S₀ : Stacks 249 A} {S : Stacks 242 A} (h : PackedKeyBankViews M B S₀ S)
    (i : Fin 276) (hi : 263 ≤ i.val) (xs : List (Fin (A+4))) :
    PackedKeyBankViews {M with R := Function.update M.R i xs} B S₀ S := by
  refine ⟨?_,h.publicationView,h.batchView⟩
  rw [embStk_updateR_off M i xs (packedKeySolverReg_off i hi)]
  exact h.protectedView

/-- Transport every native view through the input stage in one structural step. -/
theorem PackedKeyBankViews.input_update {A : ℕ} {M : Stacks 276 A} {B : Stacks 263 A}
    {S₀ : Stacks 249 A} {S : Stacks 242 A} (h : PackedKeyBankViews M B S₀ S)
    (tail rhs count : List (Fin (A+4))) :
    PackedKeyBankViews
      {M with R := (Function.update (Function.update (Function.update M.R 263 tail) 110 rhs) 251 count)}
      {B with R := (Function.update (Function.update B.R 110 rhs) 251 count)}
      {S₀ with R := Function.update S₀.R 110 rhs}
      {S with R := Function.update S.R 110 rhs} :=
  ⟨packedKeyInput_protected_view M B h.protectedView tail rhs count,
    packedKeyInput_publication_view B S₀ h.publicationView rhs count,
    packedKeyInput_batch_view S₀ S h.batchView rhs⟩

/-- The view record identifies the factory bank used by setup readiness. -/
theorem PackedKeyBankViews.factory_view {A : ℕ} {M : Stacks 276 A} {B : Stacks 263 A}
    {S₀ : Stacks 249 A} {S : Stacks 242 A} (h : PackedKeyBankViews M B S₀ S) :
    embStk (Fin.castLE (by decide : 242 ≤ 276)) M = S := by
  change embStk (Fin.castLE (by decide : 242 ≤ 248))
    (embStk packedHaloBatchReg (embStk packedHaloPublishedReg (embStk packedKeySolverReg M))) = S
  rw [h.protectedView,h.publicationView,h.batchView,embStk_extendStacks]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
