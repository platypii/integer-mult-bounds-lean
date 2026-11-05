module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCallerSharedBoundaryRetirement
public import IntegerMultBounds.MathlibTM2.Host.RestoringOutputLength

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.CallerLayout
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {T Q A : ℕ} {P U : Type}
noncomputable section

/-- Bracket an output-only restoring consumer by actual shared initialization
and owned-header retirement. This argument is independent of numerical jobs,
selected dimensions and the concrete programs' internal execution proofs. -/
theorem finishSharedBoundaryCaller_exec
    (body : P → Pr P (MachineTapes (T+solverRegisterCount)) Q A U)
    (S F : Stacks (MachineTapes (T+solverRegisterCount)) A)
    (hI : F.inp = S.inp) (hO : F.out = S.out) (hL : F.L = S.L)
    (hframe : ∀ k, k ≠ solverRegister T (.scratch 4) →
      k ≠ fullHeader _ .word → k ≠ fullHeader _ .replicas → k ≠ fullHeader _ .volume →
      (∀ i, k ≠ globals _ i) → (∀ f, k ≠ rulers _ f) →
      (∀ f i, k ≠ fullHeader _ (.geometry f i)) → F.R k = S.R k)
    (hheaders : ∀ r, sharedPreparationRole r = true → S.R (fullHeader _ r) = [])
    (hcarry : S.R (solverRegister T (.scratch 4)) = [])
    (ys : List (Fin (A+4)))
    (prepProgram runProgram : Pr P (MachineTapes (T+solverRegisterCount)) Q A U)
    (prepTime : ℕ) (runTime : ℝ) (prepStock runStock depth : ℕ)
    (v v₁ v₂ : HS (MachineTapes (T+solverRegisterCount)) Q A U) (n₁ n₂ : ℕ)
    (hu₁ : v₁.user = v.user) (hu₂ : v₂.user = v₁.user)
    (hn₁ : n₁ ≤ prepTime) (hn₂ : (n₂ : ℝ) ≤ runTime)
    (hstock : mnSize (mk v₂ {F with R := Function.update F.R (fullHeader _ .output) ys}) = mnSize (mk v₁ F))
    (he₁ : ExecWithin body (fun k z => mnSize z+k ≤ mnSize (mk v S)+depth+prepStock) depth
      prepProgram (mk v S) n₁ (mk v₁ F))
    (he₂ : ExecWithin body (fun k z => mnSize z+k ≤ mnSize (mk v₁ F)+depth+runStock) depth
      runProgram (mk v₁ F) n₂ (mk v₂ {F with R := Function.update F.R (fullHeader _ .output) ys})) :
    let retireCost := 2*((sharedBoundaryHeaders T).map (fun i => (F.R i).length)).sum+
      2*(sharedBoundaryHeaders T).length+1
    ∃ v', ∃ m : ℕ, v'.user = v.user ∧ (m : ℝ) ≤ (prepTime : ℝ)+runTime+(retireCost : ℝ) ∧
      mnSize (mk v' {S with R := Function.update S.R (fullHeader _ .output) ys}) = mnSize (mk v S) ∧
      ExecWithin body (fun k z => mnSize z+k ≤ mnSize (mk v S)+depth+prepStock+runStock) depth
        (.seq prepProgram (.seq runProgram (clearWords (sharedBoundaryHeaders T)))) (mk v S) m
        (mk v' {S with R := Function.update S.R (fullHeader _ .output) ys}) := by
  obtain ⟨v₃,hu₃,he₃⟩ := retireSharedBoundaryCaller_exec body S F hI hO hL hframe hheaders hcarry ys v₂ depth
  have houtput : F.R (fullHeader _ .output) = S.R (fullHeader _ .output) := by
    apply hframe
    · exact (solverRegister_ne_header T (.scratch 4) .output).symm
    all_goals first
      | exact (fullHeader_injective _).ne (by intro he; cases he)
      | intro i; exact (fullHeader_injective _).ne (by intro he; cases he)
      | intro f i; exact (fullHeader_injective _).ne (by intro he; cases he)
  have hlen := (mn_replace_right_length_of_size v₁ v₂ F (fullHeader _ .output) ys hstock).trans
    (congrArg List.length houtput)
  have hFsize := he₁.final
  let bound := fun (k : ℕ) (z : Store (HΓ (T := MachineTapes (T+solverRegisterCount)) A)
    (HS (MachineTapes (T+solverRegisterCount)) Q A U)) =>
      mnSize z+k ≤ mnSize (mk v S)+depth+prepStock+runStock
  have e₁ : ExecWithin body bound depth _ _ _ _ := he₁.mono (by intro k z hz; dsimp only [bound]; omega)
  have e₂ : ExecWithin body bound depth _ _ _ _ := he₂.mono (by intro k z hz; dsimp only [bound]; omega)
  have e₃ : ExecWithin body bound depth _ _ _ _ := he₃.mono (by intro k z hz; dsimp only [bound]; omega)
  refine ⟨v₃,_,hu₃.trans (hu₂.trans hu₁),?_,mn_replace_right_size_of_length v v₃ S _ ys hlen,
    ExecWithin.seq e₁ (ExecWithin.seq e₂ e₃)⟩
  have hn₁R := (Nat.cast_le (α := ℝ)).mpr hn₁
  simpa only [Nat.cast_add,add_assoc] using add_le_add (add_le_add hn₁R hn₂) (le_refl (_ : ℝ))

end
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.CallerLayout
