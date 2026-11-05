module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCallerSharedBoundaryPreparation
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHeaderFrameRetirement

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.CallerLayout
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv ScalarPlacement ScalarPlacement.ComputedClassBanks PackedTranspose
variable {T Q A : ℕ} {P U : Type}
noncomputable section

/-- The exact ownership boundary of shared caller setup, independent of its
parameter values and the number of replicas. -/
def sharedPreparationRole : Role → Bool
  | .word | .replicas | .volume | .scalar _ | .ruler _ | .geometry _ _ => true
  | _ => false

def sharedPreparationRoles : List Role :=
  (Finset.univ.filter (fun r => sharedPreparationRole r = true)).toList

@[simp] theorem mem_sharedPreparationRoles (r : Role) :
    r ∈ sharedPreparationRoles ↔ sharedPreparationRole r = true := by
  simp [sharedPreparationRoles]

def sharedBoundaryHeaders (T : ℕ) : List (Fin (MachineTapes (T+solverRegisterCount))) :=
  sharedPreparationRoles.map (fullHeader (T+solverRegisterCount))++[solverRegister T (.scratch 4)]

theorem RawInput.sharedPreparationHeaders_blank
    {T A D p u l target s t B W N radius width Vg Vr : ℕ}
    {src : Fin 11 → Fin T} {widthSource : Fin T} {widths : Fin 3 → Fin T}
    {S : Stacks (MachineTapes T) A}
    (raw : RawInput T A D p u l target s t B W N radius width Vg Vr src widthSource widths S)
    (hword : S.R (fullHeader T .word) = []) (hreplicas : S.R (fullHeader T .replicas) = [])
    (hvolume : S.R (fullHeader T .volume) = []) :
    ∀ r, sharedPreparationRole r = true → S.R (fullHeader T r) = [] := by
  intro r hr
  cases r with
  | scalar i => exact raw.scalarBlank i
  | ruler f => exact raw.rulerBlank f
  | geometry f i => exact raw.geometryBlank f i
  | word => exact hword
  | replicas => exact hreplicas
  | volume => exact hvolume
  | _ => simp [sharedPreparationRole] at hr

theorem sharedBoundaryHeaders_nodup (T : ℕ) : (sharedBoundaryHeaders T).Nodup := by
  have hroles : sharedPreparationRoles.Nodup := Finset.nodup_toList _
  have hheaders := hroles.map (fullHeader_injective (T+solverRegisterCount))
  rw [sharedBoundaryHeaders,List.nodup_append]
  refine ⟨hheaders,by simp,?_⟩
  intro k hk q hq he
  obtain ⟨r,_,rfl⟩ := List.mem_map.mp hk
  exact solverRegister_ne_header T (.scratch 4) r (he.trans (List.mem_singleton.mp hq)).symm

theorem sharedBoundaryHeaders_output (T : ℕ) : fullHeader (T+solverRegisterCount) .output ∉ sharedBoundaryHeaders T := by
  intro hm
  rcases List.mem_append.mp hm with hm | hm
  · obtain ⟨r,hr,he⟩ := List.mem_map.mp hm
    have hrole := fullHeader_injective _ he
    subst r
    simpa [sharedPreparationRole] using hr
  · exact solverRegister_ne_header T (.scratch 4) .output (List.mem_singleton.mp hm).symm

/-- After the selected proper/boundary run restores its prepared caller, clear
only setup-owned headers and the isolated RHS. The original caller is restored
exactly, apart from its final output bank. -/
theorem retireSharedBoundaryCaller_exec
    (body : P → Pr P (MachineTapes (T+solverRegisterCount)) Q A U)
    (S F : Stacks (MachineTapes (T+solverRegisterCount)) A)
    (hI : F.inp = S.inp) (hO : F.out = S.out) (hL : F.L = S.L)
    (hframe : ∀ k, k ≠ solverRegister T (.scratch 4) →
      k ≠ fullHeader _ .word → k ≠ fullHeader _ .replicas → k ≠ fullHeader _ .volume →
      (∀ i, k ≠ globals _ i) → (∀ f, k ≠ rulers _ f) →
      (∀ f i, k ≠ fullHeader _ (.geometry f i)) → F.R k = S.R k)
    (hheaders : ∀ r, sharedPreparationRole r = true → S.R (fullHeader _ r) = [])
    (hcarry : S.R (solverRegister T (.scratch 4)) = [])
    (ys : List (Fin (A+4))) (v : HS (MachineTapes (T+solverRegisterCount)) Q A U) (depth : ℕ) :
    let H := {F with R := Function.update F.R (fullHeader _ .output) ys}
    ∃ v', v'.user = v.user ∧
      ExecWithin body (fun k z => mnSize z+k ≤ mnSize (mk v H)+depth) depth
        (clearWords (sharedBoundaryHeaders T)) (mk v H)
        (2*((sharedBoundaryHeaders T).map (fun i => (F.R i).length)).sum+2*(sharedBoundaryHeaders T).length+1)
        (mk v' {S with R := Function.update S.R (fullHeader _ .output) ys}) := by
  have hmem (r : Role) (hr : sharedPreparationRole r = true) : fullHeader (T+solverRegisterCount) r ∈ sharedBoundaryHeaders T :=
    List.mem_append_left _ (List.mem_map.mpr ⟨r,(mem_sharedPreparationRoles r).mpr hr,rfl⟩)
  have hoff (k) (hk : k ∉ sharedBoundaryHeaders T) : F.R k = S.R k := by
    apply hframe k
    · intro he; exact hk (he.symm ▸ List.mem_append_right _ (by simp))
    all_goals first
      | exact fun he => hk (he.symm ▸ hmem _ rfl)
      | exact fun i he => hk (he.symm ▸ hmem _ rfl)
      | exact fun f i he => hk (he.symm ▸ hmem _ rfl)
  have hblank (k) (hk : k ∈ sharedBoundaryHeaders T) : S.R k = [] := by
    rcases List.mem_append.mp hk with hk | hk
    · obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hk
      exact hheaders r ((mem_sharedPreparationRoles r).mp hr)
    · simpa only [List.mem_singleton.mp hk] using hcarry
  obtain ⟨v',hu,he⟩ := retireHeaderFrame_pair_exec body (sharedBoundaryHeaders T) (sharedBoundaryHeaders_nodup T)
    S F hI hO hL hoff hblank (fullHeader _ .output) (fullHeader _ .output)
    (sharedBoundaryHeaders_output T) (sharedBoundaryHeaders_output T) ys ys v depth
  simp only [Function.update_idem] at he
  exact ⟨v',hu,he⟩

end
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.CallerLayout
