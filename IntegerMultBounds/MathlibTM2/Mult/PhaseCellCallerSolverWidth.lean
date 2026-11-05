module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCallerSolverReady
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellAffineHeader
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHeaderFrameRetirement

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.CallerLayout
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv CommonClassGeometry ScalarPlacement
variable {T Q A : ℕ} {P U : Type}
noncomputable section

/-- Borrow the scalar arithmetic width B (global 6), independently of the
payload word width W (global 7). The retained source may contain any symbols. -/
def callerSolverWidthProgram (src : Fin 11 → Fin T) : Pr P (MachineTapes (T+solverRegisterCount)) Q A U :=
  affineHeader 1 0 (unarySource _ (solverSource (src 6)))
    (solverRegister T (.input (familyInverseScalarReg .wr))) (solverRegister T (.scratch 0))

def callerSolverWidthState (B : ℕ) (S : Stacks (MachineTapes (T+solverRegisterCount)) A) :=
  {S with R := (Function.update S.R (solverRegister T (.input (familyInverseScalarReg .wr)))
    (List.replicate B tick))}

theorem callerSolverWidth_exec (body : P → Pr P (MachineTapes (T+solverRegisterCount)) Q A U)
    (src : Fin 11 → Fin T) (B : ℕ) (v : HS (MachineTapes (T+solverRegisterCount)) Q A U)
    (S : Stacks (MachineTapes (T+solverRegisterCount)) A)
    (hB : (S.R (unarySource _ (solverSource (src 6)))).length = B)
    (hdst : S.R (solverRegister T (.input (familyInverseScalarReg .wr))) = [])
    (htmp : S.R (solverRegister T (.scratch 0)) = []) (depth : ℕ) :
    ∃ v', v'.user = v.user ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+2*(4*B+5)) depth
        (callerSolverWidthProgram src) (mk v S) (4*B+5) (mk v' (callerSolverWidthState B S)) := by
  have hreg : [unarySource (T+solverRegisterCount) (solverSource (src 6)),
      solverRegister T (.input (familyInverseScalarReg .wr)),solverRegister T (.scratch 0)].Nodup := by
    have hs := fun r => (solverRegister_ne_source T r (src 6)).symm
    simp [hs,(solverRegister_injective T).eq_iff]
  obtain ⟨v',hu,he⟩ := affineHeader_exec body 1 0 _ _ _ hreg v S hdst htmp
  simp only [hB,one_mul,Nat.add_zero] at he
  exact ⟨v',hu,mn_native_exec_within he 2 (affineHeader_native 1 0 _ _ _) depth
    (mnSize (mk v S)+depth+2*(4*B+5)) (by omega)⟩

theorem callerSolverWidthState_ready {s : ℕ} [NeZero s] (src : Fin 11 → Fin T)
    (p u l target t W radius width : ℕ) (Fs : List (ZMod s → GaussianInt))
    (S : Stacks (MachineTapes (T+solverRegisterCount)) A)
    (hraw : ∀ i, (S.R (unarySource _ (solverSource (src i)))).length =
      globalValues p u l target s t (inverseCallerWordWidth p u l target s t) W Fs.length radius width i)
    (hzero : S.R (fullHeader _ .zero) = [])
    (hblank : ∀ r : SolverRole, S.R (solverRegister T r) = [])
    (hleft : ∀ i, S.L (solverRegister T (.input i)) = [])
    (hambient : S.R (fullHeader _ .input) =
      cstream A (inverseFullInputWidth p u l target s t) (Fs.map (chirpLine s)).flatten) :
    (callerFullLineInput T src).Ready p u l target t Fs
      (callerSolverWidthState (inverseCallerWordWidth p u l target s t) S) := by
  let B := inverseCallerWordWidth p u l target s t
  let M := callerSolverWidthState B S
  have hoff (k : Fin (MachineTapes (T+solverRegisterCount)))
      (hk : k ≠ solverRegister T (.input (familyInverseScalarReg .wr))) : M.R k = S.R k := by
    dsimp only [M,callerSolverWidthState]
    exact Function.update_of_ne hk _ _
  refine callerFullLineInput_ready src p u l target t B W radius width Fs M ?_ ?_ ?_ ?_ hleft ?_ ?_
  · intro i
    rw [hoff _ (solverRegister_ne_source T (.input (familyInverseScalarReg .wr)) (src i)).symm]
    exact hraw i
  · exact (hoff _ (solverRegister_ne_header T (.input (familyInverseScalarReg .wr)) .zero).symm).trans hzero
  · dsimp only [M,callerSolverWidthState]
    exact Function.update_self _ _ _
  · intro i hi
    apply (hoff _ ?_).trans (hblank (.input i))
    exact (solverRegister_injective T).ne (by intro he; exact hi (SolverRole.input.inj he))
  · intro i
    exact (hoff _ ((solverRegister_injective T).ne (by intro he; cases he))).trans (hblank (.scratch i))
  · exact (hoff _ (solverRegister_ne_header T (.input (familyInverseScalarReg .wr)) .input).symm).trans hambient

/-- Retire the borrowed width after its consumer, retaining both physical
data-port updates. The generic generated-header frame lemma supplies cleanup. -/
theorem callerSolverWidthRetire_exec (body : P → Pr P (MachineTapes (T+solverRegisterCount)) Q A U)
    (B : ℕ) (S : Stacks (MachineTapes (T+solverRegisterCount)) A)
    (hblank : S.R (solverRegister T (.input (familyInverseScalarReg .wr))) = [])
    (src dst : Fin PackedTranspose.tapeCount) (xs ys : List (Fin (A+4)))
    (v : HS (MachineTapes (T+solverRegisterCount)) Q A U) (depth : ℕ) :
    let port := Fin.natAdd (((T+solverRegisterCount)+headerCount)+175)
    let M := callerSolverWidthState B S
    let F := {M with R := (Function.update (Function.update M.R (port src) xs) (port dst) ys)}
    ∃ v', v'.user = v.user ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v F)+depth) depth
        (clearWords [solverRegister T (.input (familyInverseScalarReg .wr))])
        (mk v F) (2*B+3)
        (mk v' {S with R := (Function.update (Function.update S.R (port src) xs) (port dst) ys)}) := by
  dsimp only
  let seed := solverRegister T (.input (familyInverseScalarReg .wr))
  let M := callerSolverWidthState B S
  have hframe (i : Fin (MachineTapes (T+solverRegisterCount))) (hi : i ∉ [seed]) : M.R i = S.R i := by
    have hn : i ≠ seed := by simpa only [List.mem_singleton] using hi
    dsimp only [M,callerSolverWidthState]
    exact Function.update_of_ne hn _ _
  have hport (i : Fin PackedTranspose.tapeCount) :
      Fin.natAdd (((T+solverRegisterCount)+headerCount)+175) i ∉ [seed] := by
    simpa only [List.mem_singleton] using (solverRegister_ne_routing T (.input (familyInverseScalarReg .wr)) i).symm
  obtain ⟨v',hu,he⟩ := retireHeaderFrame_pair_exec body [seed] (by simp) S M rfl rfl rfl hframe
    (by intro i hi; simpa only [List.mem_singleton.mp hi] using hblank)
    _ _ (hport src) (hport dst) xs ys v depth
  have hlength : (M.R seed).length = B := by simp [M,callerSolverWidthState,seed]
  refine ⟨v',hu,?_⟩
  simpa only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil,
    hlength,Nat.add_zero,Nat.mul_one,Nat.mul_zero,Nat.reduceAdd,Nat.add_assoc] using he

end
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.CallerLayout
