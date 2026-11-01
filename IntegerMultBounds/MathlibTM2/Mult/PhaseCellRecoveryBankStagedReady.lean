module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRecoveryBankReady
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellComputedCoreStep

/-! Endpoint reading supplies the two varying parameters; routing supplies the
halo payload. All other ordinary inputs survive both stages structurally. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellMatrix
namespace RecoveryBanks
variable {T A s : ℕ} [NeZero s] (bank : RecoveryBank → Fin T) (hinj : Function.Injective bank)

theorem stagedReady (r : PackedNormalizedJob A s) (wl : List (Fin (A+4))) (S : Stacks T A)
    (source origins : Fin T) (tail originTail : List (Fin (A+4)))
    (hsource : ∀ i, source ≠ bank i) (horigins : ∀ i, origins ≠ bank i)
    (hp : (S.R (bank (.control .precision))).length = r.p)
    (hW : (S.R (bank (.control .packet))).length = r.W)
    (hN : (S.R (bank (.control .replicas))).length = r.Fs.length)
    (hparameters : ∀ i : Fin 8, i ≠ 6 → i ≠ 7 →
      (S.R (bank (.parameter i))).length = r.masterInput.values i)
    (hwidth : S.R (bank (.scalar .wr)) = wl)
    (hscalar : ∀ i : TblR 25, i ≠ .wr → S.R (bank (.scalar i)) = [])
    (hmasters : ∀ i, S.R (bank (.master i)) = [])
    (hcontrols : ∀ i, i ∉ liveControls → S.R (bank (.control i)) = [])
    (hwork : ∀ i, S.R (bank (.work i)) = [])
    (hleft : ∀ i, S.L (bank (.work i)) = [])
    (hoffset : (S.R (bank (.control .cropOffset))).length = r.radius)
    (hrows : (S.R (bank (.control .cropRows))).length = coreLength s r.coreWidth r.k) :
    (plan bank hinj).LocalReady (normalize bank hinj) (queue bank hinj) (crop bank hinj) r wl
      ((plan bank hinj).routedState r source tail
        ((plan bank hinj).coreEndpointState r origins originTail S)) := by
  let E := (plan bank hinj).routedState r source tail
    ((plan bank hinj).coreEndpointState r origins originTail S)
  have hstable (i : RecoveryBank) (hw : i ≠ .work 124)
      (ha : i ≠ .parameter 6) (hb : i ≠ .parameter 7) : E.R (bank i) = S.R (bank i) := by
    simp [E, ComputedRecoveryPlan.routedState, ComputedRecoveryPlan.coreEndpointState,
      plan, masterPlan, Function.update_of_ne, hinj.eq_iff, hw, ha, hb,
      (hsource i).symm, (horigins i).symm]
  apply localReady bank hinj r wl E
  · rw [hstable (.control .precision) (by simp) (by simp) (by simp)]; exact hp
  · rw [hstable (.control .packet) (by simp) (by simp) (by simp)]; exact hW
  · rw [hstable (.control .replicas) (by simp) (by simp) (by simp)]; exact hN
  · intro i
    by_cases ha : i = 6
    · subst i
      simp [E, ComputedRecoveryPlan.routedState, ComputedRecoveryPlan.coreEndpointState,
        plan, masterPlan, hinj.eq_iff, (hsource _).symm,
        PackedNormalizedJob.masterInput, InverseMasterInput.values]
    · by_cases hb : i = 7
      · subst i
        simp [E, ComputedRecoveryPlan.routedState, ComputedRecoveryPlan.coreEndpointState,
          plan, masterPlan, hinj.eq_iff, (hsource _).symm,
          PackedNormalizedJob.masterInput, InverseMasterInput.values]
      · rw [hstable _ (by simp) (by simpa using ha) (by simpa using hb)]
        exact hparameters i ha hb
  · rw [hstable _ (by simp) (by simp) (by simp)]; exact hwidth
  · intro i hi
    rw [hstable _ (by simp) (by simp) (by simp)]; exact hscalar i hi
  · intro i
    rw [hstable _ (by simp) (by simp) (by simp)]; exact hmasters i
  · intro i hi
    rw [hstable _ (by simp) (by simp) (by simp)]; exact hcontrols i hi
  · intro i hi
    rw [hstable _ (by simpa using hi) (by simp) (by simp)]; exact hwork i
  · exact hleft
  · simp [E, ComputedRecoveryPlan.routedState, plan, ComputedRecoveryPlan.routedPayload]
  · rw [hstable _ (by simp) (by simp) (by simp)]; exact hoffset
  · rw [hstable _ (by simp) (by simp) (by simp)]; exact hrows

end RecoveryBanks
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
