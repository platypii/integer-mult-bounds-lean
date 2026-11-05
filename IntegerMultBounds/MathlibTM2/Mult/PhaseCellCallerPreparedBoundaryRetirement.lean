module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCallerPreparedBoundaryWords
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHeaderFrameRetirement

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.CallerLayout
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Fast.Main ScalarPlacement ScalarPlacement.ComputedClassBanks PackedTranspose
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {T Q A : ℕ} {P U : Type}
noncomputable section

def callerPreparedTemporaryHeaders (T : ℕ) : List (Fin (MachineTapes T)) :=
  List.ofFn (fun i : Fin 6 => fullHeader T (.publication (Fin.castAdd 1 i)))

theorem callerPreparedTemporaryHeaders_nodup (T : ℕ) : (callerPreparedTemporaryHeaders T).Nodup := by
  rw [callerPreparedTemporaryHeaders,List.nodup_ofFn]
  intro i j he
  exact (Fin.castAdd_injective _ _) (Role.publication.inj ((fullHeader_injective T) he))

theorem callerPreparedBoundaryState_frame (widthSource : Fin T) (p s width : ℕ)
    (S : Stacks (MachineTapes T) A) (hzero : S.R (fullHeader T .zero) = [])
    (i : Fin (MachineTapes T)) (hi : i ∉ callerPreparedTemporaryHeaders T) :
    (callerPreparedBoundaryState widthSource p s width S).R i = S.R i := by
  let M : Stacks (MachineTapes T) A :=
    {S with R := Function.update S.R (fullHeader T (.publication 3)) (List.replicate (2*p+13) tick)}
  have hp (j : Fin 6) : fullHeader T (.publication (Fin.castAdd 1 j)) ≠ i := by
    intro he
    exact hi (he ▸ List.mem_ofFn.mpr ⟨j,rfl⟩)
  have hread : M.R i = S.R i := by
    have hn : i ≠ fullHeader T (.publication 3) := (hp 3).symm
    dsimp only [M]
    exact Function.update_of_ne hn _ _
  change (callerBoundaryGeometryState widthSource s width (2*p+13) M).R i = _
  by_cases hz : i = fullHeader T .zero
  · subst i
    have hzeroM : M.R (fullHeader T .zero) = [] := hread.trans hzero
    exact (callerBoundaryGeometryState_zero widthSource s width (2*p+13) M hzeroM).trans hread
  · apply Eq.trans (callerBoundaryGeometryState_off widthSource s width (2*p+13) M i ?_ ?_) hread
    · intro slot
      fin_cases slot
      · change boundaryGeometryRegister T widthSource (boundarySeamCropSkip 0) ≠ _
        rw [boundaryGeometryRegister_zero]; exact Ne.symm hz
      · change boundaryGeometryRegister T widthSource (boundarySeamCropSkip 1) ≠ _
        rw [boundaryGeometryRegister_skip_one]; exact hp 4
      · change boundaryGeometryRegister T widthSource (boundarySeamCropSkip 2) ≠ _
        rw [boundaryGeometryRegister_skip_two]; exact hp 5
    · intro slot
      rw [boundaryGeometryRegister_count]
      exact hp (Fin.castAdd 3 slot)

theorem callerPreparedHeaders_source_off (T : ℕ) :
    fullHeader T (.publication 6) ∉ callerPreparedTemporaryHeaders T := by
  intro hm
  obtain ⟨j,hj⟩ := List.mem_ofFn.mp hm
  have hv := congrArg Fin.val (Role.publication.inj ((fullHeader_injective T) hj))
  change j.val = 6 at hv
  have := j.isLt
  omega

theorem callerPreparedHeaders_output_off (T : ℕ) :
    fullHeader T .output ∉ callerPreparedTemporaryHeaders T := by
  intro hm
  obtain ⟨j,hj⟩ := List.mem_ofFn.mp hm
  have he := (fullHeader_injective T) hj
  cases he

def callerPreparedBoundaryRetirement : Pr P (MachineTapes T) Q A U :=
  clearWords (callerPreparedTemporaryHeaders T)

/-- Release all generated controls and the narrow ruler. Header 6 has already
been consumed back to its original tail; only the published output remains. -/
theorem callerPreparedBoundaryRetire_exec (body : P → Pr P (MachineTapes T) Q A U)
    (widthSource : Fin T) (p s width : ℕ) (S : Stacks (MachineTapes T) A)
    (hzero : S.R (fullHeader T .zero) = [])
    (hblank : ∀ i : Fin 6, S.R (fullHeader T (.publication (Fin.castAdd 1 i))) = [])
    (xs : List (Fin (A+4))) (v : HS (MachineTapes T) Q A U) (depth : ℕ) :
    let F := callerPreparedBoundaryState widthSource p s width S
    let G := {F with R := (Function.update (Function.update F.R (fullHeader T (.publication 6))
      (S.R (fullHeader T (.publication 6))))) (fullHeader T .output) xs}
    ∃ v', v'.user = v.user ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v G)+depth) depth
        callerPreparedBoundaryRetirement (mk v G)
        (2*((callerPreparedTemporaryHeaders T).map (fun i => (F.R i).length)).sum+
          2*(callerPreparedTemporaryHeaders T).length+1)
        (mk v' {S with R := Function.update S.R (fullHeader T .output) xs}) := by
  dsimp only
  let F := callerPreparedBoundaryState widthSource p s width S
  obtain ⟨v',hu,he⟩ := retireHeaderFrame_pair_exec body (callerPreparedTemporaryHeaders T)
    (callerPreparedTemporaryHeaders_nodup T) S F rfl rfl rfl
    (callerPreparedBoundaryState_frame widthSource p s width S hzero)
    (by intro i hi; obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hi; exact hblank j)
    _ _ (callerPreparedHeaders_source_off T) (callerPreparedHeaders_output_off T)
    (S.R (fullHeader T (.publication 6))) xs v depth
  simp only [Function.update_eq_self] at he
  exact ⟨v',hu,he⟩

end
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.CallerLayout
