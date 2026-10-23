module

public import IntegerMultBounds.MathlibTM2.Routing.InactiveClassifierFrame
public import IntegerMultBounds.MathlibTM2.Routing.ClassifierBankRepair

/-! The concrete classifier workspace extends the combined exact-repair bank.
Its core projection is exactly the generated bank used by exact repair. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

noncomputable section

abbrev inactiveClassifierT := inactiveProfileConfigurationT + 16

def inactiveClassifierTemporary : Fin inactiveProfileConfigurationT :=
  inactiveConfigurationCore (repairSetupSource (.inr .badMask))

def inactiveClassifierPhase : Fin inactiveProfileConfigurationT :=
  inactiveConfigurationCore (repairSetupSource (.inr .badPhase))

theorem inactiveClassifierOutputs_ne : inactiveClassifierTemporary ≠ inactiveClassifierPhase :=
  inactiveConfigurationCore_injective.ne (by simp [repairSetupSource])

theorem inactiveClassifierTemporary_src : inactiveClassifierTemporary ≠ inactiveConfigurationCore repairHost.src :=
  inactiveConfigurationSource_src _

theorem inactiveClassifierPhase_src : inactiveClassifierPhase ≠ inactiveConfigurationCore repairHost.src :=
  inactiveConfigurationSource_src _

theorem inactiveClassifierBank_project {A : ℕ} (p : Par) (S : Stacks inactiveClassifierT A) :
    embStk classifierCore
      { S with R := classifierPairBank p (classifierBankRepeat inactiveClassifierTemporary inactiveClassifierPhase) S.R } =
      { embStk classifierCore S with R := inactiveConfigurationClassifierBank p (embStk classifierCore S).R } := by
  have hR := classifierPairBank_project p inactiveClassifierTemporary inactiveClassifierPhase S.R
  change (fun i => classifierPairBank p (classifierBankRepeat inactiveClassifierTemporary inactiveClassifierPhase) S.R (classifierCore i)) =
    inactiveConfigurationClassifierBank p (embStk classifierCore S).R at hR
  exact congrArg (fun R => { embStk classifierCore S with R := R }) hR

end
end IntegerMultBounds.MathlibTM2.Routing
