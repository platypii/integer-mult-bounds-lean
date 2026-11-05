module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCallerSeededInputPreparation
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCallerSolverWidth

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.CallerLayout
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv ScalarPlacement CommonClassGeometry
  IntegerMultBounds.NLogN
variable {T Q A s : ℕ} [NeZero s] {P U : Type}
noncomputable section

def callerCanonicalInputPreparation (src : Fin 11 → Fin T) : Pr P (MachineTapes (T+solverRegisterCount)) Q A U :=
  .seq (callerSolverWidthProgram src) (.seq (callerSeededInputPreparation src)
    (clearWords [solverRegister T (.input (familyInverseScalarReg .wr))]))

/-- Initialize the canonical RHS from the ordinary common input and retained
rulers. Every generated scalar, master and control retires; the carry contains
the sole surviving copy required by the restoring boundary solver. -/
theorem callerCanonicalInputPreparation_exec
    (body : P → Pr P (MachineTapes (T+solverRegisterCount)) Q A U)
    (src : Fin 11 → Fin T) (hs : Function.Injective src)
    (p u l target t radius width : ℕ) (hst : s < t)
    (hband : PhaseCellBand.width p u ≤ s) (Fs : List (ZMod s → GaussianInt))
    (tail : List (Fin (A+4))) (v : HS (MachineTapes (T+solverRegisterCount)) Q A U)
    (S : Stacks (MachineTapes (T+solverRegisterCount)) A)
    (hraw : ∀ i, (S.R (unarySource _ (solverSource (src i)))).length =
      globalValues p u l target s t (inverseCallerWordWidth p u l target s t)
        (packedHaloCommonWidth p l s u (target+1) 2) Fs.length radius width i)
    (hzero : S.R (fullHeader _ .zero) = [])
    (hblank : ∀ r : SolverRole, S.R (solverRegister T r) = [])
    (hsrc : S.R (fullHeader _ .input) = cstream A (packedHaloCommonWidth p l s u (target+1) 2)
      (Fs.map (chirpLine s)).flatten++tail) (depth : ℕ) :
    let B := inverseCallerWordWidth p u l target s t
    let d := InverseMasterInput.ofCuts p u l target t 0 s hst (Nat.zero_le _) le_rfl hband
    let copyCost := callerCanonicalInputCopyCost p u l target s t Fs.length
    ∃ v' n, v'.user = v.user ∧
      n ≤ (4*B+5)+(d.timeCost+copyCost+callerInputMasterRetireCost p u l target s t)+(2*B+3) ∧
      ExecWithin body (fun k z => mnSize z+k ≤ mnSize (mk v S)+depth+
        2*(4*B+5)+d.stock+8*copyCost) depth
        (callerCanonicalInputPreparation src) (mk v S) n
        (mk v' {S with R := (Function.update S.R (solverRegister T (.scratch 4))
          (cstream A (inverseFullInputWidth p u l target s t) (Fs.map (chirpLine s)).flatten))}) := by
  let B := inverseCallerWordWidth p u l target s t
  let d := InverseMasterInput.ofCuts p u l target t 0 s hst (Nat.zero_le _) le_rfl hband
  let copyCost := callerCanonicalInputCopyCost p u l target s t Fs.length
  let M := callerSolverWidthState B S
  have hM (k) (hk : k ≠ solverRegister T (.input (familyInverseScalarReg .wr))) : M.R k = S.R k := by
    dsimp only [M,callerSolverWidthState]
    exact Function.update_of_ne hk _ _
  obtain ⟨v₁,hu₁,he₁⟩ := callerSolverWidth_exec body src B v S
    (by simpa [B,globalValues] using hraw 6) (hblank _) (hblank _) depth
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := callerSeededInputPreparation_exec body src hs p u l target t radius width hst hband
    Fs tail v₁ M
    (by
      intro i
      rw [hM _ (solverRegister_ne_source T _ (src i)).symm]
      exact hraw i)
    ((hM _ (solverRegister_ne_header T _ .zero).symm).trans hzero)
    (by simp [M,callerSolverWidthState,B])
    (by intro r hr; exact (hM _ ((solverRegister_injective T).ne hr)).trans (hblank r))
    ((hM _ (solverRegister_ne_header T _ .input).symm).trans hsrc) depth
  let dst := solverRegister T (.scratch 4)
  let xs := cstream A (inverseFullInputWidth p u l target s t) (Fs.map (chirpLine s)).flatten
  have hdst : dst ≠ solverRegister T (.input (familyInverseScalarReg .wr)) :=
    (solverRegister_injective T).ne (by intro he; cases he)
  obtain ⟨v₃,hu₃,he₃⟩ := callerSolverWidthRetire_exec body B S (hblank _) dst dst hdst hdst xs xs v₂ depth
  simp only [Function.update_idem] at he₃
  have hMsize := he₁.final
  have hHsize := he₂.final
  let bound := fun (k : ℕ) (z : Store (HΓ (T := MachineTapes (T+solverRegisterCount)) A)
    (HS (MachineTapes (T+solverRegisterCount)) Q A U)) =>
      mnSize z+k ≤ mnSize (mk v S)+depth+2*(4*B+5)+d.stock+8*copyCost
  have e₁ : ExecWithin body bound depth _ _ _ _ := he₁.mono (by
    intro k z hz
    dsimp only [bound]
    omega)
  have e₂ : ExecWithin body bound depth _ _ _ _ := he₂.mono (by
    intro k z hz
    dsimp only [bound,d,copyCost,M] at hz ⊢
    omega)
  have e₃ : ExecWithin body bound depth _ _ _ _ := he₃.mono (by
    intro k z hz
    dsimp only [bound,d,copyCost,M,xs,dst] at hz ⊢
    dsimp only [M] at hHsize
    omega)
  exact ⟨v₃,_,hu₃.trans (hu₂.trans hu₁),by dsimp only [B,d,copyCost] at *; omega,
    ExecWithin.seq e₁ (ExecWithin.seq e₂ e₃)⟩

/-- After the restoring solver/publication consumer, retire the isolated RHS
while retaining the single final output update. Cleanup allocates no stock. -/
theorem callerCanonicalInputRetire_exec
    (body : P → Pr P (MachineTapes (T+solverRegisterCount)) Q A U)
    (S : Stacks (MachineTapes (T+solverRegisterCount)) A)
    (hblank : S.R (solverRegister T (.scratch 4)) = [])
    (output : Fin (MachineTapes (T+solverRegisterCount)))
    (hoff : output ≠ solverRegister T (.scratch 4))
    (rhs ys : List (Fin (A+4))) (v : HS (MachineTapes (T+solverRegisterCount)) Q A U) (depth : ℕ) :
    let M := {S with R := Function.update S.R (solverRegister T (.scratch 4)) rhs}
    let H := {M with R := Function.update M.R output ys}
    ∃ v', v'.user = v.user ∧
      ExecWithin body (fun k z => mnSize z+k ≤ mnSize (mk v H)+depth) depth
        (clearWords [solverRegister T (.scratch 4)]) (mk v H) (2*rhs.length+3)
        (mk v' {S with R := Function.update S.R output ys}) := by
  let carry := solverRegister T (.scratch 4)
  let M : Stacks (MachineTapes (T+solverRegisterCount)) A := {S with R := Function.update S.R carry rhs}
  obtain ⟨v',hu,he⟩ := retireHeaderFrame_pair_exec body [carry] (by simp) S M rfl rfl rfl
    (by
      intro k hk
      dsimp only [M]
      exact Function.update_of_ne (by simpa only [List.mem_singleton] using hk) _ _)
    (by intro k hk; simpa only [List.mem_singleton.mp hk] using hblank)
    output output (by simpa only [List.mem_singleton] using hoff)
    (by simpa only [List.mem_singleton] using hoff) ys ys v depth
  simp only [Function.update_idem] at he
  have hcost : 2*([carry].map (fun i => (M.R i).length)).sum+2*[carry].length+1 =
      2*rhs.length+3 := by
    simp [M]
  rw [hcost] at he
  exact ⟨v',hu,he⟩

end
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.CallerLayout
