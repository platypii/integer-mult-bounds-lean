module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCallerSolverAllocation
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRestoredInverseMasters
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInverseMasterInput

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.CallerLayout
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry ScalarPlacement
variable {T Q A s : ℕ} [NeZero s] {P U : Type}
noncomputable section

def callerInputMaster (T : ℕ) (i : Fin 10) := solverRegister T (.input (familyInverseMasterPort i))

theorem callerInputMaster_injective (T : ℕ) : Function.Injective (callerInputMaster T) := by
  intro i j he
  exact familyInverseMasterPort_injective (SolverRole.input.inj (solverRegister_injective T he))

def callerInputMastersProgram (src : Fin 11 → Fin T) : Pr P (MachineTapes (T+solverRegisterCount)) Q A U :=
  restoredSupplierMasters (fun r => solverRegister T (.input (familyInverseScalarReg r)))
    (solverParameter T src) (callerInputMaster T)
    (solverRegister T (.scratch 0)) (solverRegister T (.scratch 1))
    (solverRegister T (.scratch 2)) (solverRegister T (.scratch 3)) (solverRegister T (.scratch 4))

/-- Generate the inverse precision masters in their existing input-bank slots.
The scalar table and scratch registers restore, including arbitrary carry data. -/
theorem callerInputMasters_exec
    (body : P → Pr P (MachineTapes (T+solverRegisterCount)) Q A U)
    (src : Fin 11 → Fin T) (p u l target t : ℕ) (hst : s < t)
    (hband : PhaseCellBand.width p u ≤ s)
    (v : HS (MachineTapes (T+solverRegisterCount)) Q A U)
    (S : Stacks (MachineTapes (T+solverRegisterCount)) A)
    (hvalues : ∀ i, (S.R (solverParameter T src i)).length = ![p,u,l,target,s,t,0,s] i)
    (hwidth : S.R (solverRegister T (.input (familyInverseScalarReg .wr))) =
      List.replicate (inverseCallerWordWidth p u l target s t) tick)
    (hblank : ∀ i, i ≠ familyInverseScalarReg .wr → S.R (solverRegister T (.input i)) = [])
    (hscratch : ∀ i : Fin 4, S.R (solverRegister T (.scratch (Fin.castAdd 1 i))) = []) (depth : ℕ) :
    let d := InverseMasterInput.ofCuts p u l target t 0 s hst (Nat.zero_le _) le_rfl hband
    ∃ v' F n, v'.user = v.user ∧ n ≤ d.timeCost ∧
      ExecWithin body (fun k z => mnSize z+k ≤ mnSize (mk v S)+depth+d.stock) depth
        (callerInputMastersProgram src) (mk v S) n (mk v' F) ∧
      (∀ i, F.R (callerInputMaster T i) = List.replicate (inverseMasterValues p u l target s t 0 s i) tick) ∧
      F.inp = S.inp ∧ F.out = S.out ∧ F.L = S.L ∧
      ∀ k, (∀ i, callerInputMaster T i ≠ k) → F.R k = S.R k := by
  let d := InverseMasterInput.ofCuts p u l target t 0 s hst (Nat.zero_le _) le_rfl hband
  have hrg : Function.Injective (fun r => solverRegister T (.input (familyInverseScalarReg r))) := by
    intro r q he
    exact familyInverseScalarReg_injective (SolverRole.input.inj (solverRegister_injective T he))
  have hsep (i : Fin 10) (r : TblR 25) :
      solverRegister T (.input (familyInverseScalarReg r)) ≠ callerInputMaster T i := by
    intro he
    exact familyInverseScalarReg_master i r (SolverRole.input.inj (solverRegister_injective T he))
  have hblankTable (r : TblR 25) (hr : r ≠ .wr) :
      S.R (solverRegister T (.input (familyInverseScalarReg r))) = [] :=
    hblank _ (fun he => hr (familyInverseScalarReg_injective he))
  have hmasters (i : Fin 10) : S.R (callerInputMaster T i) = [] :=
    hblank _ (Ne.symm (familyInverseScalarReg_master i .wr))
  have hscratch' : ∀ k ∈ [solverRegister T (.scratch 0),solverRegister T (.scratch 1),
      solverRegister T (.scratch 2),solverRegister T (.scratch 3)], S.R k = [] := by
    intro k hk
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl
    · exact hscratch 0
    · exact hscratch 1
    · exact hscratch 2
    · exact hscratch 3
  exact restoredInverseMasters_exec (body := body) _ hrg _ _ (callerInputMaster_injective T) hsep
    _ _ _ _ _ (callerFullLineInput T src).parameterRegs
    (by intro r; exact (solverRegister_injective T).ne (by intro he; cases he))
    hst (Nat.zero_le _) le_rfl hband d.band_room d.geometry_room d.precision_room d.values_fit
    _ (List.length_replicate ..) v S hvalues hwidth hblankTable hmasters hscratch' depth

end
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.CallerLayout
