module

public import IntegerMultBounds.MathlibTM2.Routing.LiveDescriptorWorkspace
public import IntegerMultBounds.MathlibTM2.Routing.RepairDescriptorGuard

/-! Shared-bank descriptor programs use a static mode and live row-count guard.
No binary width or numerical dimension is unrolled into the program. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host

noncomputable section

variable {N J Q A : ℕ} {P U : Type}

def liveAffineDescriptorProgram (j : Fin J) (out : Fin N) : Pr P (liveDescriptorT N J) Q A U :=
  affineProfileDescriptorProgram (sharedAffineProfile (liveBankProfile j)) (liveDescriptorAux .profileSaved)
    liveBankCoordinate (liveDescriptorAux .coordinateSaved) liveBankZero liveBankRuns (liveBankMask j)
    (liveDescriptorAux .archive) (liveDescriptorCore out)

def liveGroupedDescriptorProgram (j : Fin J) (out : Fin N) : Pr P (liveDescriptorT N J) Q A U :=
  repairADescriptorProgram (liveBankProfile j) (liveDescriptorAux .profileSaved)
    liveBankCoordinate (liveDescriptorAux .coordinateSaved) liveBankZero liveBankRuns (liveBankMask j)
    (liveDescriptorAux .archive) (liveDescriptorCore out)

def liveDescriptorBackend (mode : LiveDescriptorMode) (j : Fin J) (out : Fin N) : Pr P (liveDescriptorT N J) Q A U :=
  match mode with
  | .affine _ _ => liveAffineDescriptorProgram j out
  | .grouped _ => liveGroupedDescriptorProgram j out

def liveDescriptorProgram (mode : LiveDescriptorMode) (j : Fin J) (out : Fin N) : Pr P (liveDescriptorT N J) Q A U :=
  repairDescriptorGuardProgram (liveDescriptorAux (.rows j))
    (liveBankProfile j (.coordinate (.arithmetic .dst)))
    (liveBankProfile j (.coordinate (.arithmetic .tx)))
    (liveBankProfile j (.coordinate (.arithmetic .ty)))
    (liveBankProfile j (.coordinate (.arithmetic .tz))) (liveBankProfile j (.coordinate .gap))
    (liveDescriptorBackend mode j out)

end
end IntegerMultBounds.MathlibTM2.Routing
