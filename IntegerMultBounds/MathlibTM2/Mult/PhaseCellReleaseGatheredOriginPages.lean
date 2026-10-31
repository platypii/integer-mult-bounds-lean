module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedPairedLocalHaloClass
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReleasePairedOriginPages

/-! Place coordinate-page retirement in the gather bank and restore its entry ABI. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def releaseGatheredOriginPages (plan : ReplicaInteriorPlacement T) : Pr P T Q A U :=
  releasePairedOriginPages (plan.gather 116) (plan.gather 115) (plan.gather 104)
    (plan.gather 113) (plan.gather 109) (plan.gather 105) (plan.gather 106)

def releasedGatheredOriginPagesBank (plan : ReplicaInteriorPlacement T) (F S : Stacks T A) : Stacks T A :=
  {F with R := (Function.update (Function.update (Function.update F.R (plan.gather 113)
    (S.R (plan.gather 113))) (plan.gather 109) (S.R (plan.gather 109))) (plan.gather 116) [])}

theorem releasedGatheredOriginPagesBank_gather (plan : ReplicaInteriorPlacement T) (F S : Stacks T A)
    (V s t band a b L : ℕ) (hcount : S.R (plan.gather 116) = [])
    (hgather : embStk plan.gather F = embStk plan.gather (pairedLocalHaloClassBank plan S V s t band a b L)) :
    embStk plan.gather (releasedGatheredOriginPagesBank plan F S) = embStk plan.gather S := by
  refine Stacks.ext ?_ ?_ ?_ ?_
  · have hh := congrArg (fun B : Stacks 126 A => B.inp) hgather
    exact hh
  · have hh := congrArg (fun B : Stacks 126 A => B.out) hgather
    exact hh
  · have hh := congrArg (fun B : Stacks 126 A => B.L) hgather
    exact hh
  · funext k
    have hk := congrFun (congrArg Stacks.R hgather) k
    change F.R (plan.gather k) = (pairedLocalHaloClassBank plan S V s t band a b L).R (plan.gather k) at hk
    change (releasedGatheredOriginPagesBank plan F S).R (plan.gather k) = S.R (plan.gather k)
    by_cases h116 : k = 116
    · subst k; simp [releasedGatheredOriginPagesBank,hcount]
    by_cases h109 : k = 109
    · subst k; simp [releasedGatheredOriginPagesBank,plan.gather_injective.eq_iff]
    by_cases h113 : k = 113
    · subst k; simp [releasedGatheredOriginPagesBank,plan.gather_injective.eq_iff]
    simpa [releasedGatheredOriginPagesBank,pairedLocalHaloClassBank,plan.gather_injective.eq_iff,
      h116,h109,h113] using hk

theorem releaseGatheredOriginPages_exec_within (plan : ReplicaInteriorPlacement T)
    (V s t band a b L : ℕ) (v : HS T Q A U) (F S : Stacks T A)
    (hV : (S.R (plan.gather 115)).length = V)
    (hclean : ∀ k ∈ [(104 : Fin 126),105,106], S.R (plan.gather k) = [])
    (hgather : embStk plan.gather F = embStk plan.gather (pairedLocalHaloClassBank plan S V s t band a b L))
    (depth : ℕ) :
    ∃ v' m, v'.user = v.user ∧ m ≤ releasePairedOriginPagesCost (haloLengthGroup s t band a b L).length V ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v F)+depth+
        2*releasePairedOriginPagesCost (haloLengthGroup s t band a b L).length V) depth
        (releaseGatheredOriginPages plan) (mk v F) m (mk v' (releasedGatheredOriginPagesBank plan F S)) := by
  have hg (k : Fin 126) : F.R (plan.gather k) =
      (pairedLocalHaloClassBank plan S V s t band a b L).R (plan.gather k) :=
    congrFun (congrArg Stacks.R hgather) k
  apply releasePairedOriginPages_exec_within
    (plan.gather 116) (plan.gather 115) (plan.gather 104) (plan.gather 113) (plan.gather 109)
    (plan.gather 105) (plan.gather 106)
    (List.Nodup.map plan.gather_injective (show [(116 : Fin 126),115,104,113,109,105,106].Nodup by decide))
    (haloLengthGroup s t band a b L).length V
    (haloOriginPackets A V s t band a b L) ((haloPackedOffsets s t band a b L).flatMap (binSyms V))
    (S.R (plan.gather 113)) (S.R (plan.gather 109))
  · simp
  · simp [List.length_flatMap]
  · simp [hg,pairedLocalHaloClassBank]
  · simpa [hg,pairedLocalHaloClassBank,plan.gather_injective.eq_iff] using hV
  · simp [hg,pairedLocalHaloClassBank,plan.gather_injective.eq_iff]
  · simp [hg,pairedLocalHaloClassBank,plan.gather_injective.eq_iff]
  · intro k hk
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl | rfl
    · simpa [hg,pairedLocalHaloClassBank,plan.gather_injective.eq_iff] using hclean 104 (by simp)
    · simpa [hg,pairedLocalHaloClassBank,plan.gather_injective.eq_iff] using hclean 105 (by simp)
    · simpa [hg,pairedLocalHaloClassBank,plan.gather_injective.eq_iff] using hclean 106 (by simp)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
