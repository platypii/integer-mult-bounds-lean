module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellMasterHeaderBank
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedBoundaryTableRouting
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedBoundaryFactorWorkspace
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedBoundarySolve

/-! A native packed factory bank assembled from master headers and binary
geometry words, rather than an assumed decoded-loop readiness certificate. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host

variable {A : ℕ}

def packedFactoryNativeReg (i : Fin 224) : Fin 242 :=
  packedBoundaryTableRouting (packedBoundaryFactorReg (preparedBoundaryCoreReg i))

theorem packedFactoryNativeReg_injective : Function.Injective packedFactoryNativeReg :=
  packedBoundaryTableRouting_injective.comp
    (packedBoundaryFactorReg_injective.comp preparedBoundaryCoreReg_injective)

/-- The native placement leaves the geometry interval 154 through 167 free. -/
theorem packedFactoryNativeReg_gap (i : Fin 224) (j : Fin 242)
    (hj : 154 ≤ j.val) (hj' : j.val < 168) : packedFactoryNativeReg i ≠ j := by
  intro h
  have h132 : j ≠ 132 := by intro he; have := congrArg Fin.val he; omega
  have h220 : j ≠ 220 := by intro he; have := congrArg Fin.val he; omega
  have hswap : packedBoundaryTableRouting j = j := by
    simp [packedBoundaryTableRouting, Equiv.swap_apply_def, h132, h220]
  have he : packedBoundaryFactorReg (preparedBoundaryCoreReg i) = j :=
    packedBoundaryTableRouting_injective (h.trans hswap.symm)
  have hv := congrArg Fin.val he
  have hi := i.isLt
  by_cases h140 : preparedBoundaryCoreReg i = (140 : Fin 226)
  · simp [packedBoundaryFactorReg, h140] at hv
    omega
  by_cases h143 : preparedBoundaryCoreReg i = (143 : Fin 226)
  · simp [packedBoundaryFactorReg, h143] at hv
    omega
  by_cases h206 : preparedBoundaryCoreReg i = (206 : Fin 226)
  · simp [packedBoundaryFactorReg, h206] at hv
    omega
  by_cases hlo : (preparedBoundaryCoreReg i).val < 154
  · simp [packedBoundaryFactorReg, h140, h143, h206, hlo] at hv
    omega
  · simp [packedBoundaryFactorReg, h140, h143, h206, hlo] at hv
    omega

/-- Ordinary unary master words occupy the native core; binary interval
metadata occupies its disjoint geometry workspace. Only the host tapes of
`H` are retained. -/
def packedFactoryInputBank (H : Stacks 242 A) (P N q l s t u band a b V : ℕ) : Stacks 242 A :=
  embOvr packedFactoryNativeReg
    {masterHeaderBank (A := A) (masterHeaderValues P N q l s t u band a b) [] with
      inp := H.inp
      out := H.out}.get
    {H with
      L := fun _ => []
      R := fun k => if k = 155 then binSyms V a else
        if k = 165 then binSyms V (b-a) else if k = 163 then List.replicate V Node.tick else []}

theorem packedFactoryInputBank_native (H : Stacks 242 A) (P N q l s t u band a b V : ℕ) :
    embStk preparedBoundaryCoreReg (embStk packedBoundaryFactorReg
      (embStk packedBoundaryTableRouting (packedFactoryInputBank H P N q l s t u band a b V))) =
      {masterHeaderBank (A := A) (masterHeaderValues P N q l s t u band a b) [] with
        inp := H.inp
        out := H.out} := by
  unfold packedFactoryInputBank
  exact embStk_ovr packedFactoryNativeReg_injective
    {masterHeaderBank (A := A) (masterHeaderValues P N q l s t u band a b) [] with
      inp := H.inp, out := H.out} _

theorem packedFactoryInputBank_headers (H : Stacks 242 A) (P N q l s t u band a b V : ℕ)
    (i : Fin 10) :
    (packedFactoryInputBank H P N q l s t u band a b V).R
      (packedFactoryNativeReg (inverseMasterCorePort i)) =
      List.replicate (masterHeaderValues P N q l s t u band a b i) Node.tick := by
  have hv := congrArg (fun S : Stacks 224 A => S.R (inverseMasterCorePort i))
    (packedFactoryInputBank_native H P N q l s t u band a b V)
  exact hv.trans (masterHeaderBank_headers _ [] i)

theorem packedFactoryInputBank_source (H : Stacks 242 A) (P N q l s t u band a b V : ℕ) :
    (packedFactoryInputBank H P N q l s t u band a b V).R 110 = [] := by
  have hv := congrArg (fun S : Stacks 224 A => S.R 110)
    (packedFactoryInputBank_native H P N q l s t u band a b V)
  exact hv.trans (masterHeaderBank_source (masterHeaderValues P N q l s t u band a b) [])

theorem packedFactoryInputBank_left (H : Stacks 242 A) (P N q l s t u band a b V : ℕ)
    (i : Fin 242) : (packedFactoryInputBank H P N q l s t u band a b V).L i = [] := by
  simp only [packedFactoryInputBank, embOvr, Stacks.get, masterHeaderBank, embExt]
  split <;> rfl

/-- The exact packed native view is ready from its constructed words. -/
theorem packedFactoryInputBank_ready (H : Stacks 242 A) (P N q l s t u band a b V : ℕ) :
    LengthKeyReady P N q l s t u band 0 0 []
      (embStk componentReg (embStk boundaryArithmeticReg (embStk tableReg
        (embStk boundaryFactorLegacyReg (embStk preparedBoundaryCoreReg
          (embStk packedBoundaryFactorReg (embStk packedBoundaryTableRouting
            (packedFactoryInputBank H P N q l s t u band a b V)))))))) := by
  rw [packedFactoryInputBank_native]
  exact masterHeaderBank_ready P N q l s t u band a b [] H.inp H.out

theorem packedFactoryInputBank_geometry (H : Stacks 242 A) (P N q l s t u band a b V : ℕ) :
    let S := packedFactoryInputBank H P N q l s t u band a b V
    S.R 155 = binSyms V a ∧ S.R 165 = binSyms V (b-a) ∧
      S.R 163 = List.replicate V Node.tick := by
  have hf (j : Fin 242) (hj : 154 ≤ j.val) (hj' : j.val < 168) :=
    (embOvr_off (e := packedFactoryNativeReg)
      ({masterHeaderBank (A := A) (masterHeaderValues P N q l s t u band a b) [] with
        inp := H.inp, out := H.out}.get)
      {H with L := fun _ => [], R := fun k => if k = 155 then binSyms V a else
        if k = 165 then binSyms V (b-a) else if k = 163 then List.replicate V Node.tick else []}
      (fun i => packedFactoryNativeReg_gap i j hj hj')).2
  exact ⟨by simpa [packedFactoryInputBank] using hf 155 (by decide) (by decide),
    by simpa [packedFactoryInputBank] using hf 165 (by decide) (by decide),
    by simpa [packedFactoryInputBank] using hf 163 (by decide) (by decide)⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
