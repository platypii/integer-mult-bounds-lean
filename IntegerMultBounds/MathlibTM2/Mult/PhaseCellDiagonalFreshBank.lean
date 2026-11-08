module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellLocalDiagonalLayout

/-! Derive the diagonal stage's fresh banks from recovery's exact frame. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.LocalRecoveryLayout
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM
variable {A s : ℕ} [NeZero s]

structure DiagonalFresh (S : Stacks tapes A) : Prop where
  left : ∀ k, S.L k = []
  work : ∀ i : Fin 392, S.R (recovery (.work i)) = []

omit [NeZero s] in
theorem DiagonalFresh.role {S : Stacks tapes A} (h : DiagonalFresh S) (r : RsbR) : S.R (diagonalRole r) = [] :=
  h.work (diagonalRoleIndex r)
omit [NeZero s] in
theorem DiagonalFresh.multiplier {S : Stacks tapes A} (h : DiagonalFresh S) (i : Fin 64) : S.R (diagonalMul i) = [] :=
  h.work (diagonalMulIndex i)
omit [NeZero s] in
theorem DiagonalFresh.table {S : Stacks tapes A} (h : DiagonalFresh S) (r : TblR 48) : S.R (diagonalTable r) = [] :=
  h.work (diagonalTableIndex r)
omit [NeZero s] in
theorem DiagonalFresh.controls {S : Stacks tapes A} (h : DiagonalFresh S) :
    ∀ k ∈ [diagonalClock,diagonalBytes,diagonalSaved,diagonalTmp], S.R k = [] := by
  intro k hk
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
  rcases hk with hk | hk | hk | hk <;> subst k <;> exact h.work _

omit [NeZero s] in
theorem diagonalFresh_of_frame (S F : Stacks tapes A)
    (hwork : ∀ i : Fin 392, S.R (recovery (.work i)) = []) (hleft : ∀ k, S.L k = [])
    (hframe : ∀ i, F.R (recovery i) = S.R (recovery i)) (hL : F.L = S.L)
    (packet : List (Fin (A+4))) :
    DiagonalFresh {F with R := Function.update (Function.update F.R source []) (crop.reg 12) packet} := by
  let E : Stacks tapes A := {F with R := Function.update (Function.update F.R source []) (crop.reg 12) packet}
  have hw i : E.R (recovery (.work i)) = [] := by
    have hc : recovery (.work i) ≠ crop.reg 12 := by
      change recovery (.work i) ≠ recovery (.control .cropDst)
      simp [recovery_injective.eq_iff]
    have hs : recovery (.work i) ≠ source := (geometry_ne_recovery 108 (.work i)).symm
    simpa only [E,Function.update_of_ne hc,Function.update_of_ne hs,hframe] using hwork i
  exact ⟨fun k => (congrFun hL k).trans (hleft k),hw⟩

theorem diagonalFresh_of_cropped (d : InverseMasterInput s) (r : RawRecoveryJob s) (N offset rows : ℕ)
    (wl : List (Fin (A+4))) (S F : Stacks tapes A)
    (h : plan.CroppedReady crop d r N offset rows wl S)
    (hinput : S.R (plan.work 124) = []) (hleft : ∀ k, S.L k = [])
    (hframe : ∀ i, F.R (recovery i) = S.R (recovery i)) (hL : F.L = S.L)
    (packet : List (Fin (A+4))) :
    DiagonalFresh {F with R := Function.update (Function.update F.R source []) (crop.reg 12) packet} := by
  apply diagonalFresh_of_frame S F _ hleft hframe hL packet
  intro i
  by_cases hi : i = 124
  · subst i; exact hinput
  · exact h.blank i hi

omit [NeZero s] in
theorem DiagonalFresh.clean {S : Stacks tapes A} (h : DiagonalFresh S) : RsbClean diagonalMul S :=
  ⟨h.left,h.multiplier⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.LocalRecoveryLayout
