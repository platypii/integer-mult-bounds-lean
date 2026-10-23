module

public import IntegerMultBounds.MathlibTM2.Routing.LiveHeaderWidths
public import IntegerMultBounds.MathlibTM2.Routing.RepairConfigurationInputFrame

/-! Core and auxiliary embeddings for live header and width generation. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.MathlibTM2.Host

noncomputable section

def liveHeaderConfigurationCore (i : Fin repairT) : Fin liveHeaderConfigurationT :=
  fieldCore (N := repairLiveHeaderT) (repairLiveHeaderRaw i)

theorem liveHeaderConfigurationCore_injective : Function.Injective liveHeaderConfigurationCore :=
  fieldCore_injective.comp (repairLiveHeaderRaw_injective)

theorem liveHeaderConfigurationSource_src (key : RepairSetupKey) :
    liveHeaderConfigurationCore (repairSetupSource key) ≠ liveHeaderConfigurationCore repairHost.src :=
  liveHeaderConfigurationCore_injective.ne (repairSetup_source_src key)

theorem liveHeaderConfigurationAux_src (i : Fin 6) :
    fieldAux i ≠ liveHeaderConfigurationCore repairHost.src :=
  (fieldCore_aux (repairLiveHeaderRaw repairHost.src) i).symm

end
end IntegerMultBounds.MathlibTM2.Routing
