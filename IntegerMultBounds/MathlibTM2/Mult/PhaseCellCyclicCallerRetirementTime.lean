module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFittingCyclicComplexCaller
public import IntegerMultBounds.MathlibTM2.Host.ConsumedBankStock
public import IntegerMultBounds.MathlibTM2.Mult.ExportClearRegisterBank

/-! Cleanup time may be charged to pushes during the actual run. Unlike a
space bound, this preserves the numerical fast-time exponent unchanged. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.CyclicComplexCallerLayout
open IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

@[irreducible] noncomputable def executionPush (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : ℕ :=
  max (fittingCyclicInputPush (Q := Q) (A := A) (U := U))
    (max (cyclicFactorPreparationPush (Q := Q) (A := A) (U := U))
      (max 2 (mnProgPush (executedCyclicComplexCore (P := Empty) (A := A) (U := U) hR hQ))))

noncomputable def retiredTimeCost (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (run payload : ℕ) : ℕ :=
  (8*executionPush (A := A) (U := U) hR hQ+1)*run+8*payload+4*909+5

theorem retiredTimeCost_mono (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) {a b : ℕ}
    (hab : a ≤ b) (payload : ℕ) :
    retiredTimeCost (A := A) (U := U) hR hQ a payload ≤ retiredTimeCost (A := A) (U := U) hR hQ b payload := by
  have hm := Nat.mul_le_mul_left (8*executionPush (A := A) (U := U) hR hQ+1) hab
  unfold retiredTimeCost
  omega

theorem program_native (ports : CyclicComplexCallerLayout T) (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) :
    mnNativePushBound (executionPush (A := A) (U := U) hR hQ)
      (ports.program (P := P) (A := A) (U := U) hR hQ) := by
  have hinput : fittingCyclicInputPush (Q := Q) (A := A) (U := U) ≤ executionPush (A := A) (U := U) hR hQ := by
    unfold executionPush
    exact Nat.le_max_left _ _
  have hfactor : cyclicFactorPreparationPush (Q := Q) (A := A) (U := U) ≤ executionPush (A := A) (U := U) hR hQ := by
    unfold executionPush
    exact (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  have hcopy : 2 ≤ executionPush (A := A) (U := U) hR hQ := by
    unfold executionPush
    exact (Nat.le_max_left _ _).trans ((Nat.le_max_right _ _).trans (Nat.le_max_right _ _))
  have hcore : mnProgPush (executedCyclicComplexCore (P := Empty) (A := A) (U := U) hR hQ) ≤
      executionPush (A := A) (U := U) hR hQ := by
    unfold executionPush
    exact (Nat.le_max_right _ _).trans ((Nat.le_max_right _ _).trans (Nat.le_max_right _ _))
  unfold program factoredCyclicComplexCore preparedCyclicComplexCore
    installCyclicComplexCoreControls placedCyclicComplexCore
  exact ⟨mnNativePushBound_mono hinput (fittingCyclicCachedInputs_native ..),
    mnNativePushBound_mono hfactor (prepareCyclicFactorFromCached_native ..),
    mnNativePushBound_mono hcopy (copyUnaryHeaders_native ..),
    embProg_native _ Empty.elim _ (mnNativePushBound_mono hcore (WordCmd.empty_native _))⟩

/-- No spectator archive enters the retirement bill: its stock cancels through
the frame, leaving only consumed payload and pushes of the actual execution. -/
theorem exportClearRegisterBankCost_le_run (ports : CyclicComplexCallerLayout T)
    (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (dst : Fin T) (hdst : ∀ i, ports.bank i ≠ dst)
    (v w : HS T Q A U) (S F : Stacks T A) (steps : ℕ) (payload tail : List (Fin (A+4)))
    (hex : Exec body (ports.program hR hQ) (Host.mk v S) steps (Host.mk w F))
    (hblank : ∀ i, S.L (ports.bank i) = [] ∧ S.R (ports.bank i) = [])
    (hinput : F.inp = S.inp) (houtput : F.out = S.out)
    (hsourceL : F.L ports.archive = S.L ports.archive)
    (hsourceR : S.R ports.archive = payload++tail) (hfinal : F.R ports.archive = tail)
    (hframe : ∀ k, k ≠ ports.archive → (∀ i, ports.bank i ≠ k) → F.L k = S.L k ∧ F.R k = S.R k) :
    steps+exportClearRegisterBankCost ports.bank 850 dst F ≤
      retiredTimeCost (A := A) (U := U) hR hQ steps payload.length := by
  have hwithin := mn_native_exec_within hex _ (ports.program_native hR hQ) 0 _ (le_refl _)
  have hsize := hwithin.final
  simp only [Nat.add_zero] at hsize
  have hstock := registerBankStock_le_of_consume_frame ports.bank ports.injective ports.archive
    (fun i => (ports.archiveOff i).symm) v w S F payload tail _ hblank hinput houtput hsourceL
    hsourceR hfinal hframe hsize
  have hcleanup := exportClearRegisterBankCost_le ports.bank 850 dst hdst F
  unfold retiredTimeCost
  nlinarith only [hstock,hcleanup]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.CyclicComplexCallerLayout
