module

public import IntegerMultBounds.MathlibTM2.Routing.LiveClassifierFrame
public import IntegerMultBounds.MathlibTM2.Routing.ClassifierBankRepair

/-! The concrete classifier workspace extends the combined exact-repair bank.
Its core projection is exactly the generated bank used by exact repair. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

noncomputable section

abbrev liveClassifierT := liveHeaderConfigurationT + 16

def liveClassifierTemporary : Fin liveHeaderConfigurationT :=
  liveHeaderConfigurationCore (repairSetupSource (.inr .badMask))

def liveClassifierPhase : Fin liveHeaderConfigurationT :=
  liveHeaderConfigurationCore (repairSetupSource (.inr .badPhase))

theorem liveClassifierOutputs_ne : liveClassifierTemporary ≠ liveClassifierPhase :=
  liveHeaderConfigurationCore_injective.ne (by simp [repairSetupSource])

theorem liveClassifierTemporary_src : liveClassifierTemporary ≠ liveHeaderConfigurationCore repairHost.src :=
  liveHeaderConfigurationSource_src _

theorem liveClassifierPhase_src : liveClassifierPhase ≠ liveHeaderConfigurationCore repairHost.src :=
  liveHeaderConfigurationSource_src _

theorem liveClassifierBank_project {A : ℕ} (p : Par) (S : Stacks liveClassifierT A) :
    embStk classifierCore
      { S with R := classifierPairBank p (classifierBankRepeat liveClassifierTemporary liveClassifierPhase) S.R } =
      { embStk classifierCore S with R := liveHeaderConfigurationClassifierBank p (embStk classifierCore S).R } := by
  have hR := classifierPairBank_project p liveClassifierTemporary liveClassifierPhase S.R
  change (fun i => classifierPairBank p (classifierBankRepeat liveClassifierTemporary liveClassifierPhase) S.R (classifierCore i)) =
    liveHeaderConfigurationClassifierBank p (embStk classifierCore S).R at hR
  exact congrArg (fun R => { embStk classifierCore S with R := R }) hR

end
end IntegerMultBounds.MathlibTM2.Routing
