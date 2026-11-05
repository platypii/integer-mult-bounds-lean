module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCallerSolverAllocation
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCallerRawInput

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.CallerLayout
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv ScalarPlacement ScalarPlacement.ComputedClassBanks PackedTranspose
variable {T A D p u l target s t B W N radius width Vg Vr : ℕ}
noncomputable section

/-- Reserve the restoring solver's carry for an isolated RHS. All ordinary
caller ports lie outside this one reserved register. -/
def solverCarryState (S : Stacks (MachineTapes (T+solverRegisterCount)) A) (rhs : List (Fin (A+4))) :=
  {S with R := Function.update S.R (solverRegister T (.scratch 4)) rhs}

@[simp] theorem solverCarryState_raw (S : Stacks (MachineTapes (T+solverRegisterCount)) A)
    (rhs : List (Fin (A+4))) (i : Fin T) :
    (solverCarryState S rhs).R (unarySource _ (solverSource i)) = S.R (unarySource _ (solverSource i)) := by
  dsimp only [solverCarryState]
  exact Function.update_of_ne (solverRegister_ne_source T (.scratch 4) i).symm _ _

@[simp] theorem solverCarryState_header (S : Stacks (MachineTapes (T+solverRegisterCount)) A)
    (rhs : List (Fin (A+4))) (r : Role) :
    (solverCarryState S rhs).R (fullHeader _ r) = S.R (fullHeader _ r) := by
  dsimp only [solverCarryState]
  exact Function.update_of_ne (solverRegister_ne_header T (.scratch 4) r).symm _ _

@[simp] theorem solverCarryState_numerical (S : Stacks (MachineTapes (T+solverRegisterCount)) A)
    (rhs : List (Fin (A+4))) (b : ComputedClassBank → Fin T) (j : ComputedClassBank) :
    (solverCarryState S rhs).R (fullExposedClassBank (bank (solverSource ∘ b)) j) =
      S.R (fullExposedClassBank (bank (solverSource ∘ b)) j) := by
  rw [fullExposedClassBank_apply]
  exact solverCarryState_raw S rhs (b j)

theorem solverRegister_ne_exposure (r : SolverRole) (i : Fin 175) :
    solverRegister T r ≠ Fin.castAdd tapeCount (Fin.natAdd ((T+solverRegisterCount)+headerCount) i) := by
  intro he
  exact exposure_prefix_ne_private _ i ((Fin.castAdd_injective _ _) he)

@[simp] theorem solverCarryState_exposure (S : Stacks (MachineTapes (T+solverRegisterCount)) A)
    (rhs : List (Fin (A+4))) (i : Fin 175) :
    (solverCarryState S rhs).R (Fin.castAdd tapeCount (Fin.natAdd ((T+solverRegisterCount)+headerCount) i)) =
      S.R (Fin.castAdd tapeCount (Fin.natAdd ((T+solverRegisterCount)+headerCount) i)) := by
  dsimp only [solverCarryState]
  exact Function.update_of_ne (solverRegister_ne_exposure (.scratch 4) i).symm _ _

@[simp] theorem solverCarryState_routing (S : Stacks (MachineTapes (T+solverRegisterCount)) A)
    (rhs : List (Fin (A+4))) (i : Fin tapeCount) :
    (solverCarryState S rhs).R (Fin.natAdd (((T+solverRegisterCount)+headerCount)+175) i) =
      S.R (Fin.natAdd (((T+solverRegisterCount)+headerCount)+175) i) := by
  dsimp only [solverCarryState]
  exact Function.update_of_ne (solverRegister_ne_routing T (.scratch 4) i).symm _ _

theorem RawInput.solverCarry {src : Fin 11 → Fin T} {widthSource : Fin T} {widths : Fin 3 → Fin T}
    {S : Stacks (MachineTapes (T+solverRegisterCount)) A}
    (raw : RawInput (T+solverRegisterCount) A D p u l target s t B W N radius width Vg Vr
      (solverSource ∘ src) (solverSource widthSource) (solverSource ∘ widths) S)
    (rhs : List (Fin (A+4))) :
    RawInput (T+solverRegisterCount) A D p u l target s t B W N radius width Vg Vr
      (solverSource ∘ src) (solverSource widthSource) (solverSource ∘ widths) (solverCarryState S rhs) := by
  refine {raw with
    widthLength := ?_, values := ?_, widths := ?_, scalarBlank := ?_, rulerBlank := ?_,
    geometryBlank := ?_, ownedBlank := ?_, zeroBlank := ?_, routingBlank := ?_}
  · simpa only [solverCarryState_raw] using raw.widthLength
  · intro i; simpa only [Function.comp_apply,solverCarryState_raw] using raw.values i
  · intro f; simpa only [Function.comp_apply,solverCarryState_raw] using raw.widths f
  · intro i; exact (solverCarryState_header S rhs (.scalar i)).trans (raw.scalarBlank i)
  · intro f; exact (solverCarryState_header S rhs (.ruler f)).trans (raw.rulerBlank f)
  · intro f i; exact (solverCarryState_header S rhs (.geometry f i)).trans (raw.geometryBlank f i)
  · intro r hr; exact (solverCarryState_header S rhs r).trans (raw.ownedBlank r hr)
  · exact (solverCarryState_header S rhs .zero).trans raw.zeroBlank
  · intro i; exact (solverCarryState_routing S rhs i).trans (raw.routingBlank i)

end
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.CallerLayout
