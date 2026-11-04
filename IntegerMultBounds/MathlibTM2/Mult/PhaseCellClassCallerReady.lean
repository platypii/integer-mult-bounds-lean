module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellComputedClassGeometryHeaders

/-! Retained words and fresh numerical storage for a selected class.
Only physical readiness is bundled; geometry and cost bounds remain ordinary facts. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.ComputedClassBanks
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {N A : ℕ}

structure ClassCallerReady (bank : ComputedClassBank → Fin N) (rg : TblR 12 → Fin N)
    (src : Fin 4 → Fin N) (masters : Fin 12 → Fin N) (widthMaster zeroMaster : Fin N)
    (B D s width radius L : ℕ) (value : Fin N → ℕ) (S : Stacks N A) : Prop where
  geometryWords : ∀ j, S.R (src j) = binSyms B (![s,width,radius,L] j)
  widthWord : (S.R widthMaster).length = D
  zeroWord : S.R zeroMaster = []
  masterWords : ∀ j, S.R (masters j) = binSyms D (value (masters j))
  tableBlank : ∀ r, S.R (rg r) = []
  numericalBlank : ∀ j, j ≠ .control .source → S.R (bank j) = []
  leftBlank : ∀ j, S.L (recovery bank (.work j)) = []

namespace ClassCallerReady
variable {bank : ComputedClassBank → Fin N} {rg : TblR 12 → Fin N}
  {src : Fin 4 → Fin N} {masters : Fin 12 → Fin N} {widthMaster zeroMaster : Fin N}
  {B D s width radius L : ℕ} {value : Fin N → ℕ} {S : Stacks N A}

theorem reframe (h : ClassCallerReady bank rg src masters widthMaster zeroMaster B D s width radius L value S)
    (F : Stacks N A) (output : Fin N)
    (hR : ∀ k, k ≠ output → F.R k = S.R k) (hL : F.L = S.L)
    (hsrc : ∀ j, src j ≠ output) (hmasters : ∀ j, masters j ≠ output)
    (hwidth : widthMaster ≠ output) (hzero : zeroMaster ≠ output)
    (htable : ∀ r, rg r ≠ output) (hbank : ∀ j, bank j ≠ output) :
    ClassCallerReady bank rg src masters widthMaster zeroMaster B D s width radius L value F := by
  exact ⟨fun j => (hR _ (hsrc j)).trans (h.geometryWords j),
    (congrArg List.length (hR _ hwidth)).trans h.widthWord,
    (hR _ hzero).trans h.zeroWord,
    fun j => (hR _ (hmasters j)).trans (h.masterWords j),
    fun r => (hR _ (htable r)).trans (h.tableBlank r),
    fun j hj => (hR _ (hbank j)).trans (h.numericalBlank j hj),
    by intro j; rw [hL]; exact h.leftBlank j⟩

theorem updateOutput (h : ClassCallerReady bank rg src masters widthMaster zeroMaster B D s width radius L value S)
    (output : Fin N) (xs : List (Fin (A+4)))
    (hsrc : ∀ j, src j ≠ output) (hmasters : ∀ j, masters j ≠ output)
    (hwidth : widthMaster ≠ output) (hzero : zeroMaster ≠ output)
    (htable : ∀ r, rg r ≠ output) (hbank : ∀ j, bank j ≠ output) :
    ClassCallerReady bank rg src masters widthMaster zeroMaster B D s width radius L value
      {S with R := Function.update S.R output xs} :=
  h.reframe _ output (fun _ hk => Function.update_of_ne hk xs S.R) rfl hsrc hmasters hwidth hzero htable hbank

end ClassCallerReady
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.ComputedClassBanks
