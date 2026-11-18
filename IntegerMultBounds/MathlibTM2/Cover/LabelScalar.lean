module

public import IntegerMultBounds.MathlibTM2.Cover.LabelCall
public import IntegerMultBounds.Machine.RecursiveViewedAction

/-! A scalar instruction reads the prepared label-view headers directly on the role bank. -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Cover.LabelScalar
noncomputable section

open IntegerMultBounds.Machine
open IntegerMultBounds.MathlibTM2.M8.RevMachine
open IntegerMultBounds.Networks.Shared50ModularControl (prime prime_prime)
open RecursiveInterchangeLayout (Descriptor volume)
open RecursiveViewedAction (Action actionSkeleton)
open SharedBankStageInput (raw)
open SharedPlacementAlphabet (setTape)
open RecursiveShiftRoleBank (source)
variable {T : ℕ}

def ports (io : Fin T) : Fin 9 → Fin (T+24) :=
  ![Fin.castAdd 24 io, Fin.natAdd T (2 : Fin 24), Fin.natAdd T (0 : Fin 24), Fin.natAdd T (1 : Fin 24), Fin.natAdd T (10 : Fin 24), Fin.natAdd T (8 : Fin 24), Fin.natAdd T (17 : Fin 24), Fin.natAdd T (15 : Fin 24), Fin.natAdd T (3 : Fin 24)]

theorem ports_injective (io : Fin T) : Function.Injective (ports io) := by
  intro i j h
  have hv := congrArg Fin.val h
  have hio := io.isLt
  fin_cases i <;> fin_cases j <;> first | rfl | (simp [ports] at hv <;> omega)

def block (io : Fin T) (act : Action 1) : Graph.Block (T+24) prime :=
  let sk := actionSkeleton (u := 0) act
  SharedBankFamily.ofProgram (Placement.placed sk.program
    (CleanSubbank.placement sk.slots (ports io) (ports_injective io)))

private theorem reads {v : Descriptor} {c k s t B : ℕ} (io : Fin T) (roles : Tapes T prime)
    (a : RecursiveViewedAction.Data 1 (LabelView.colView prime c k s t B v))
    (hh : roles.head io = 0) (hx : roles.tape io = source (a 0)) :
    SharedBank.payload (LabelCall.bank roles v (LabelPrepareClean.output prime v k s t c B)) (ports io) =
      RecursiveViewFrameRoleBank.bank (RecursiveRoleSerialization.roles a)
        (Routines.hdr (LabelView.colView prime c k s t B v)) (SharedBank.empty 1 prime) (SharedBank.empty 0 prime) := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;>
    simp [LabelCall.bank, ports, Tapes.append, hh, hx] <;> rfl

private theorem frame (io : Fin T) (roles : Tapes T prime) (v : Descriptor)
    (d : Fin 22 → Option (List Bool)) (f : ℤ → Fin (prime+4)) :
    SharedBank.strip (LabelCall.bank roles v d) (ports io) =
      SharedBank.strip (LabelCall.bank (setTape roles io f 0) v d) (ports io) := by
  apply congrArg₂ Tapes.mk <;> funext j <;> by_cases hj : ∃ i, ports io i = j
  all_goals simp only [hj, ↓reduceIte]
  all_goals induction j using Fin.addCases with
    | left j =>
      have hn : j ≠ io := by rintro rfl; exact hj ⟨0,rfl⟩
      simp [LabelCall.bank, Tapes.append, setTape, Function.update_of_ne hn]
    | right j => simp [LabelCall.bank, Tapes.append]

theorem runs {v : Descriptor} {k s t c B : ℕ} (hs : s < t) (ht : t < k)
    (hv : v.beforeH = B*prime^(k*c)) (hp : v.Positive) (io : Fin T) (roles : Tapes T prime)
    (act : Action 1) (a : RecursiveViewedAction.Data 1 (LabelView.colView prime c k s t B v))
    (hh : roles.head io = 0) (hx : roles.tape io = source (a 0)) :
    let u := LabelView.colView prime c k s t B v
    let d := LabelPrepareClean.output prime v k s t c B
    GraphContract.Runs (block io act) (LabelCall.bank roles v d)
      (LabelCall.bank (setTape roles io (source (RecursiveViewedAction.transform act a 0)) 0) v d)
      (RecursiveViewedAction.cost u act) := by
  let u := LabelView.colView prime c k s t B v
  have hvol : volume prime u = volume prime v := LabelView.colView_volume _ _ _ _ _ _ _ hv hs ht
  have hu : u.Positive := LeafCore.positive_of_volume (hvol ▸ RecursiveAffinePrepare.volume_positive prime_prime.two_le v hp)
  have h := RecursiveViewedAction.action_hoare act (Routines.hdr u) (SharedBank.empty 1 prime)
    (SharedBank.empty 0 prime) (Routines.hdr_headers _) hu a
  let sk := actionSkeleton (u := 0) act
  have hl := RecursiveViewedAction.action_slots (u := 0) act
  have hr := CleanSubbank.realizes sk.program sk.slots (ports io) sk.slots_injective (ports_injective io)
    _ _ _ _ _ ((SharedBankRawCompose.payload_raw _ _ hl).trans (reads io roles a hh hx).symm)
    ((SharedBankRawCompose.payload_raw _ _ hl).trans
      (reads io (setTape roles io (source (RecursiveViewedAction.transform act a 0)) 0) (RecursiveViewedAction.transform act a)
        (by simp [setTape]) (by simp [setTape])).symm)
    (SharedBankRawCompose.strip_raw _ _ hl) (SharedBankRawCompose.strip_raw _ _ hl) (frame io roles v _ _) h
  simpa only [GraphContract.Runs, block, SharedBankFamily.ofProgram, sk, u, SharedBankRawCompose.bank_eq_raw] using hr

end
end IntegerMultBounds.MathlibTM2.Cover.LabelScalar
