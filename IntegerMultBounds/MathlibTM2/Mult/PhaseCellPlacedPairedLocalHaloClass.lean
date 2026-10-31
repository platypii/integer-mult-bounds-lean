module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedPairedLocalHaloClass
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaInteriorPlacement
public import IntegerMultBounds.MathlibTM2.Host.EmbedStock

/-! Generate both class pages inside the existing gather bank. Only the three
owned output ports change; the numerical bank and unrelated tapes survive. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def placedPairedLocalHaloClass (plan : ReplicaInteriorPlacement T) : Pr P T Q A U :=
  embProg (fun i : Fin 117 => plan.gather (Fin.castLE (by decide) i)) Empty.elim
    (preparedPairedLocalHaloClass (P₀ := Empty))

def pairedLocalHaloClassBank (plan : ReplicaInteriorPlacement T) (S : Stacks T A)
    (V s t band a b L : ℕ) : Stacks T A :=
  {S with R := (Function.update (Function.update (Function.update S.R (plan.gather 109)
    ((haloPackedOffsets s t band a b L).flatMap (binSyms V)++S.R (plan.gather 109)))
    (plan.gather 113) (haloOriginPackets A V s t band a b L++S.R (plan.gather 113)))
    (plan.gather 116) (List.replicate (haloLengthGroup s t band a b L).length tick))}

theorem pairedLocalHaloClassBank_solver (plan : ReplicaInteriorPlacement T) (S : Stacks T A)
    (V s t band a b L : ℕ) :
    embStk plan.solver (pairedLocalHaloClassBank plan S V s t band a b L) = embStk plan.solver S := by
  refine Stacks.ext rfl rfl rfl ?_
  funext k
  simp [pairedLocalHaloClassBank,embStk,(plan.disjoint 109 k).symm,
    (plan.disjoint 113 k).symm,(plan.disjoint 116 k).symm]

theorem pairedLocalHaloClassBank_restore (plan : ReplicaInteriorPlacement T) (S : Stacks T A)
    (V s t band a b L : ℕ) (hcount : S.R (plan.gather 116) = []) :
    let F := pairedLocalHaloClassBank plan S V s t band a b L
    {F with R := (Function.update (Function.update (Function.update F.R
      (plan.gather 113) (S.R (plan.gather 113)))
      (plan.gather 109) (S.R (plan.gather 109))) (plan.gather 116) [])} = S := by
  dsimp only
  refine Stacks.ext rfl rfl rfl ?_
  funext k
  by_cases h116 : k = plan.gather 116
  · subst k; simp [hcount]
  by_cases h109 : k = plan.gather 109
  · subst k; simp [plan.gather_injective.eq_iff]
  by_cases h113 : k = plan.gather 113
  · subst k; simp [plan.gather_injective.eq_iff]
  simp [pairedLocalHaloClassBank,h116,h109,h113]

theorem placedPairedLocalHaloClass_exec_within (plan : ReplicaInteriorPlacement T)
    (V s t band a b L : ℕ) (hwide : 8*(t+1)^2+2*band+8 < 2^V)
    (hs : 0 < s) (hst : s < t) (hband : band ≤ s) (hab : a ≤ b) (hbs : b ≤ s)
    (hL : 0 < L) (hLs : L ≤ s) (hA : 4 ≤ A) (v : HS T Q A U) (S : Stacks T A)
    (hsSrc : (S.R (plan.gather 97)).length = s) (htSrc : (S.R (plan.gather 98)).length = t)
    (hbSrc : (S.R (plan.gather 100)).length = band) (haSrc : (S.R (plan.gather 111)).length = a)
    (hbEndSrc : (S.R (plan.gather 113)).length = b) (hLSrc : (S.R (plan.gather 102)).length = L)
    (hV : (S.R (plan.gather 115)).length = V)
    (hfresh : ∀ k ∈ [(104 : Fin 126),106,116], S.R (plan.gather k) = [])
    (hblank : ∀ k : Fin 126, k.val < 31 → S.R (plan.gather k) = []) (depth : ℕ) :
    ∃ v' n, v'.user = v.user ∧ n ≤ preparedPairedLocalHaloClassCost V s t band a b L ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
        3*preparedPairedLocalHaloClassCost V s t band a b L) depth (placedPairedLocalHaloClass plan)
        (mk v S) n (mk v' (pairedLocalHaloClassBank plan S V s t band a b L)) := by
  let e := fun i : Fin 117 => plan.gather (Fin.castLE (by decide) i)
  have he : Function.Injective e := plan.gather_injective.comp (Fin.castLE_injective (by decide))
  obtain ⟨vi,F,n,hu,hn,hei,hi,ho,hl,hr⟩ := preparedPairedLocalHaloClass_exec_within (body := fun p : Empty => nomatch p)
    V s t band a b L hwide hs hst hband hab hbs hL hLs hA (embDn e v) (embStk e S)
    hsSrc htSrc hbSrc haSrc hbEndSrc hLSrc hV
    (hfresh _ (by simp)) (hfresh _ (by simp)) (hfresh _ (by simp))
    (fun k hk => hblank (Fin.castLE (by decide) k) hk) depth
  have hF : F = {embStk e S with R := (Function.update (Function.update (Function.update (embStk e S).R 109
      ((haloPackedOffsets s t band a b L).flatMap (binSyms V)++S.R (plan.gather 109)))
      113 (haloOriginPackets A V s t band a b L++S.R (plan.gather 113)))
      116 (List.replicate (haloLengthGroup s t band a b L).length tick))} := Stacks.ext hi ho hl hr
  rw [hF] at hei
  obtain ⟨v',hv',hu',hei'⟩ := exec_emb_ovr_within_stock e he (body' := body)
    (fun p : Empty => nomatch p) hei v rfl S rfl
  have hbank : embOvr e {embStk e S with R := (Function.update (Function.update (Function.update (embStk e S).R 109
      ((haloPackedOffsets s t band a b L).flatMap (binSyms V)++S.R (plan.gather 109)))
      113 (haloOriginPackets A V s t band a b L++S.R (plan.gather 113)))
      116 (List.replicate (haloLengthGroup s t band a b L).length tick))}.get S =
      pairedLocalHaloClassBank plan S V s t band a b L := by
    let B : Stacks 117 A := {embStk e S with R := (Function.update (Function.update (embStk e S).R 109
      ((haloPackedOffsets s t band a b L).flatMap (binSyms V)++S.R (plan.gather 109)))
      113 (haloOriginPackets A V s t band a b L++S.R (plan.gather 113)))}
    change embOvr e {B with R := Function.update B.R 116 _}.get S = _
    rw [embOvr_updR he]
    dsimp only [B]
    rw [embOvr_updateR_updateR he]
    rfl
  rw [hbank] at hei'
  exact ⟨v',n,hu'.trans hu,hn,hei'⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
