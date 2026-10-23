module

public import IntegerMultBounds.MathlibTM2.Routing.OptionalAffineSourceCall
public import IntegerMultBounds.MathlibTM2.Host.WordTape

/-! Extract activity from the three-bit source suffix, archiving both tag bits
and activity so the complete raw record can later be restored. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Host.WordCmd
variable {T Q A : ℕ} {P U : Type}

def sourceSuffixActivity (src saved dst : Fin T) : Act T Q A U :=
  actThen (sourceActivityArchive src saved)
    (actThen (sourceActivityArchive src saved)
      (actThen (sourceActivityArchive src saved)
        (.push (.rt dst) (fun v => v.sym.getD blank) .done)))

theorem sourceSuffixActivity_run (src saved dst : Fin T)
    (hss : src ≠ saved) (hds : dst ≠ src) (hda : dst ≠ saved)
    (lo hi enabled : Bool) (rest : List (Fin (A + 4)))
    (v : HS T Q A U) (S : Stacks T A)
    (hraw : S.R src = bitSymbol lo :: bitSymbol hi :: bitSymbol enabled :: rest) :
    (sourceSuffixActivity src saved dst : Act T Q A U).run (mk v S) =
      mk { v with sym := some (bitSymbol enabled), flag := enabled }
        { S with R := Function.update (Function.update (Function.update S.R src rest) saved (bitSymbol enabled :: bitSymbol hi :: bitSymbol lo :: S.R saved)) dst (bitSymbol enabled :: S.R dst) } := by
  simp [sourceSuffixActivity, actThen, sourceActivityArchive, Action.run, update_rt, hraw,
    hss, hss.symm, hds, hda]
  congr 2
  funext j
  by_cases hs : j = src <;> by_cases ha : j = saved <;> by_cases hd : j = dst <;> simp_all

end IntegerMultBounds.MathlibTM2.Routing
