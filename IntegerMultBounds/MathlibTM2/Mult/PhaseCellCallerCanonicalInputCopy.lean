module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCallerInputMasters
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCanonicalInputCopy
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHeaderFrameRetirement

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.CallerLayout
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv ScalarPlacement ScalarPlacement.ComputedClassBanks
variable {T Q A s : ℕ} [NeZero s] {P U : Type}
noncomputable section

/-- Raw dimensions stay in the retained bank; all generated controls reuse the
solver's seven control slots. The isolated RHS occupies its restoring carry. -/
def callerInputCopyPort (T : ℕ) (src : Fin 11 → Fin T) : Fin 13 → Fin (MachineTapes (T+solverRegisterCount)) :=
  ![unarySource _ (solverSource (src 8)),unarySource _ (solverSource (src 4)),
    unarySource _ (solverSource (src 7)),solverRegister T (.control 1),solverRegister T (.control 2),
    fullHeader _ .input,solverRegister T (.scratch 4),solverRegister T (.scratch 1),
    solverRegister T (.scratch 2),solverRegister T (.control 0),solverRegister T (.scratch 0),
    solverRegister T (.control 3),solverRegister T (.control 4)]

theorem callerInputCopyPort_nodup (src : Fin 11 → Fin T) (hs : Function.Injective src) :
    (List.ofFn (callerInputCopyPort T src)).Nodup := by
  have hraw : Function.Injective (fun i => unarySource (T+solverRegisterCount) (solverSource (src i))) :=
    (unarySource_injective _).comp ((Fin.castAdd_injective _ _).comp hs)
  have hsource (r : SolverRole) (i : Fin 11) := solverRegister_ne_source T r (src i)
  have hheader (i : Fin 11) : fullHeader (T+solverRegisterCount) .input ≠
      unarySource _ (solverSource (src i)) := by
    intro he
    exact header_ne_bank id .input _ (classCallerRegister_injective he)
  simp [callerInputCopyPort,List.ofFn_succ,hraw.eq_iff,(solverRegister_injective T).eq_iff,
    fun r i => (hsource r i).symm,solverRegister_ne_header,
    fun r h => (solverRegister_ne_header T r h).symm,fun i => (hheader i).symm]

def callerCanonicalInputCopyProgram (src : Fin 11 → Fin T) : Pr P (MachineTapes (T+solverRegisterCount)) Q A U :=
  canonicalInputCopyProgram (callerInputMaster T 2) (callerInputCopyPort T src)

noncomputable abbrev callerCanonicalInputCopyCost := @canonicalInputCopyCost

/-- The exact caller copy derives its width from a generated inverse master;
it restores all controls and preserves the common input and borrowed suffix. -/
theorem callerCanonicalInputCopy_exec
    (body : P → Pr P (MachineTapes (T+solverRegisterCount)) Q A U)
    (src : Fin 11 → Fin T) (hs : Function.Injective src)
    (p u l target t : ℕ) (Fs : List (ZMod s → GaussianInt))
    (tail : List (Fin (A+4))) (v : HS (MachineTapes (T+solverRegisterCount)) Q A U)
    (S : Stacks (MachineTapes (T+solverRegisterCount)) A)
    (hN : (S.R (unarySource _ (solverSource (src 8)))).length = Fs.length)
    (hline : (S.R (unarySource _ (solverSource (src 4)))).length = s)
    (hwide : (S.R (unarySource _ (solverSource (src 7)))).length = packedHaloCommonWidth p l s u (target+1) 2)
    (hmaster : (S.R (callerInputMaster T 2)).length = inverseMasterValues p u l target s t 0 s 2)
    (hsrc : S.R (fullHeader _ .input) = cstream A (packedHaloCommonWidth p l s u (target+1) 2)
      (Fs.map (chirpLine s)).flatten++tail)
    (hfresh : ∀ r : SolverRole, (∀ i, r ≠ .input (familyInverseMasterPort i)) →
      r ≠ .input (familyInverseScalarReg .wr) → S.R (solverRegister T r) = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ callerCanonicalInputCopyCost p u l target s t Fs.length ∧
      Exec body (callerCanonicalInputCopyProgram src) (mk v S) n
        (mk v' {S with R := (Function.update S.R (solverRegister T (.scratch 4))
          (cstream A (inverseFullInputWidth p u l target s t) (Fs.map (chirpLine s)).flatten))}) := by
  let r := callerInputCopyPort T src
  have hreg : [r 0,r 1,r 2,r 3,r 4,r 5,r 6,r 7,r 8,r 9,r 10,r 11,r 12].Nodup := by
    simpa [r,callerInputCopyPort,List.ofFn_succ] using callerInputCopyPort_nodup src hs
  have hwreg : [callerInputMaster T 2,r 9,r 8].Nodup := by
    simp [r,callerInputCopyPort,callerInputMaster,(solverRegister_injective T).eq_iff]
  have hblank (q : SolverRole) (hq : ∀ i, q ≠ .input i) : S.R (solverRegister T q) = [] :=
    hfresh q (fun i => hq _) (hq _)
  have hcopy := canonicalInputCopy_exec body (callerInputMaster T 2) r hreg hwreg
    p u l target t Fs tail v S
    (by simpa [r,callerInputCopyPort] using hN)
    (by simpa [r,callerInputCopyPort] using hline)
    (by simpa [r,callerInputCopyPort] using hwide) hmaster
    (by simpa [r,callerInputCopyPort] using hsrc) (by
      intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact hblank _ (by intro i he; cases he))
  simpa [r,callerInputCopyPort,callerCanonicalInputCopyProgram,canonicalInputCopyProgram] using hcopy

end
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.CallerLayout
