module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCallerSharedBoundaryRetirement

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.CallerLayout
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  ScalarPlacement CommonClassGeometry
variable {T A s : ℕ} [NeZero s]
noncomputable section

def sharedBoundaryRetireCost (S : Stacks (MachineTapes (T+solverRegisterCount)) A) : ℕ :=
  2*((sharedBoundaryHeaders T).map (fun i => (S.R i).length)).sum+2*(sharedBoundaryHeaders T).length+1

theorem sharedPreparationRoles_length_le : sharedPreparationRoles.length ≤ headerCount := by
  simpa only [sharedPreparationRoles,Finset.length_toList,headerCount,Finset.card_univ] using
    (Finset.card_filter_le (s := (Finset.univ : Finset Role)) (p := fun r => sharedPreparationRole r = true))

/-- Retirement visits only generated headers and the isolated RHS. Its bill
is linear in encoded volume and scalar widths, independent of borrowed tails. -/
theorem sharedBoundaryRetireCost_le
    {D p u l target t B W radius width Vg Vr : ℕ} (Fs : List (ZMod s → GaussianInt))
    (S : Stacks (MachineTapes (T+solverRegisterCount)) A)
    (input : SetupInput (T+solverRegisterCount) A D p u l target s t B W Fs.length radius width Vg Vr S)
    (hwords : ∀ f i, S.R (fullHeader _ (.geometry f i)) = binSyms (formatWidths B Vg Vr f) (![s,width,radius] i))
    (hword : (S.R (fullHeader _ .word)).length = W)
    (hreplicas : (S.R (fullHeader _ .replicas)).length = Fs.length)
    (hvolume : (S.R (fullHeader _ .volume)).length = s*W)
    (src : Fin 11 → Fin T) (widthSource : Fin (T+solverRegisterCount))
    (ready : BoundaryCallerReady src widthSource p u l target t W D radius width Fs S)
    (hwidth : inverseFullInputWidth p u l target s t ≤ W) :
    sharedBoundaryRetireCost S ≤
      2*(headerCount*(W+Fs.length+s*W+D+B+Vg+Vr)+Fs.length*s*W)+2*(headerCount+1)+1 := by
  let V := W+Fs.length+s*W+D+B+Vg+Vr
  have hformat (f : Fin 3) : formatWidths B Vg Vr f ≤ V := by
    fin_cases f <;> simp [formatWidths, V] <;> omega
  have hheader (r : Role) (hr : sharedPreparationRole r = true) : (S.R (fullHeader _ r)).length ≤ V := by
    cases r with
    | scalar i =>
      change (S.R (globals _ i)).length ≤ V
      rw [input.scalarWords, length_binSyms]
      dsimp only [V]
      omega
    | ruler f => exact (input.rulerLengths f).le.trans (hformat f)
    | geometry f i => rw [hwords,length_binSyms]; exact hformat f
    | word => rw [hword]; dsimp only [V]; omega
    | replicas => rw [hreplicas]; dsimp only [V]; omega
    | volume => rw [hvolume]; dsimp only [V]; omega
    | _ => simp [sharedPreparationRole] at hr
  have hsum (rs : List Role) (h : ∀ r ∈ rs, sharedPreparationRole r = true) :
      (rs.map (fun r => (S.R (fullHeader _ r)).length)).sum ≤ rs.length*V := by
    induction rs with
    | nil => simp
    | cons r rs ih =>
      simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.succ_mul]
      have hr := hheader r (h r (by simp))
      have hs := ih (fun r hr => h r (by simp [hr]))
      omega
  have hroles := sharedPreparationRoles_length_le
  have hsumRoles := (hsum sharedPreparationRoles (fun r hr => (mem_sharedPreparationRoles r).mp hr)).trans
    (Nat.mul_le_mul_right V hroles)
  have hrhs : (S.R (solverRegister T (.scratch 4))).length = Fs.length*s*inverseFullInputWidth p u l target s t := by
    rw [ready.input]
    simp only [length_cstream,List.length_flatten,List.map_map,Function.comp_def,length_chirpLine,
      List.map_const',List.sum_replicate,smul_eq_mul]
  have hrhsBound := Nat.mul_le_mul_left (Fs.length*s) hwidth
  unfold sharedBoundaryRetireCost
  simp only [sharedBoundaryHeaders,List.map_append,List.map_map,Function.comp_def,List.map_cons,List.map_nil,
    List.sum_append,List.sum_cons,List.sum_nil,Nat.add_zero,List.length_append,List.length_map,
    List.length_cons,List.length_nil,hrhs]
  dsimp only [V] at hsumRoles
  omega

end
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.CallerLayout
