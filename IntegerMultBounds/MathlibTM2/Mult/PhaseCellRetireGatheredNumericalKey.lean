module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetireReplicaNumericalKey
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaInteriorPlacement
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReleaseCellRuntime
public import IntegerMultBounds.MathlibTM2.Host.EmbedUpdate
public import IntegerMultBounds.MathlibTM2.Host.EmbedStock

/-! Retire a completed numerical key inside the physical disjoint placement.
Its low bank is exactly the released input expected by header installation. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
open ScalarPlacement
variable {Q A : ℕ} {U : Type}

theorem retiredReplicaNumericalKeyBank_low (S : Stacks 121 A)
    (rhsTail cacheTail : List (Fin (A+4)))
    (hleft : ∀ k, (embStk weightCacheCoreReg S).L k = [])
    (hclean : ∀ k : Fin 117, k ≠ 93 → k ≠ 110 → (embStk weightCacheCoreReg S).R k = []) :
    embStk weightCacheCoreReg (retiredReplicaNumericalKeyBank S rhsTail cacheTail) =
      releasedCellBank [] rhsTail (S.R 93) S.inp S.out := by
  ext1
  · rfl
  · rfl
  · funext k; exact hleft k
  · funext k
    have hk117 : k.val ≠ 117 := by omega
    have hk118 : k.val ≠ 118 := by omega
    by_cases h93 : k = 93
    · subst k; simp [embStk,weightCacheCoreReg,retiredReplicaNumericalKeyBank,releasedCellBank]
    by_cases h110 : k = 110
    · subst k; simp [embStk,weightCacheCoreReg,retiredReplicaNumericalKeyBank,releasedCellBank]
    have hv93 : k.val ≠ 93 := fun h => h93 (Fin.ext h)
    have hv110 : k.val ≠ 110 := fun h => h110 (Fin.ext h)
    simpa [embStk,weightCacheCoreReg,retiredReplicaNumericalKeyBank,releasedCellBank,
      Function.update_apply,Fin.ext_iff,hk117,hk118,hv93,hv110] using hclean k h93 h110

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def retiredGatheredNumericalKeyBank (plan : ReplicaInteriorPlacement T) (S : Stacks T A)
    (rhsTail cacheTail : List (Fin (A+4))) : Stacks T A :=
  {S with R := (Function.update (Function.update (Function.update S.R
    (plan.solver 110) rhsTail) (plan.solver 117) cacheTail) (plan.solver 118) [])}

theorem retiredGatheredNumericalKeyBank_solver (plan : ReplicaInteriorPlacement T) (S : Stacks T A)
    (rhsTail cacheTail : List (Fin (A+4))) :
    embStk plan.solver (retiredGatheredNumericalKeyBank plan S rhsTail cacheTail) =
      retiredReplicaNumericalKeyBank (embStk plan.solver S) rhsTail cacheTail := by
  ext1
  · rfl
  · rfl
  · rfl
  · funext k
    simp [retiredGatheredNumericalKeyBank,retiredReplicaNumericalKeyBank,embStk,
      Function.update_apply,plan.solver_injective.eq_iff]

def retireGatheredNumericalKey (plan : ReplicaInteriorPlacement T) : Pr P T Q A U :=
  embProg plan.solver Empty.elim (retireReplicaNumericalKey (P := Empty))

theorem retireGatheredNumericalKey_exec_within (plan : ReplicaInteriorPlacement T) (n : ℕ)
    (rhs rhsTail page cacheTail : List (Fin (A+4)))
    (hrhsLen : rhs.length = n) (hpageLen : page.length = 2*n)
    (v : HS T Q A U) (S : Stacks T A)
    (hrhs : S.R (plan.solver 110) = rhs++rhsTail) (hpage : S.R (plan.solver 117) = page++cacheTail)
    (hclock : (S.R (plan.solver 118)).length = 2*n)
    (hclean : ∀ k ∈ [(116 : Fin 121),119,120], S.R (plan.solver k) = []) (depth : ℕ) :
    ∃ v' m, v'.user = v.user ∧ m ≤ 32*n+20 ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+3*(32*n+20)) depth
        (retireGatheredNumericalKey plan) (mk v S) m
        (mk v' (retiredGatheredNumericalKeyBank plan S rhsTail cacheTail)) := by
  obtain ⟨vi,m,hu,hm,hei⟩ := retireReplicaNumericalKey_exec_within
    (body := fun p : Empty => nomatch p) n rhs rhsTail page cacheTail hrhsLen hpageLen
    (embDn plan.solver v) (embStk plan.solver S) hrhs hpage hclock hclean depth
  obtain ⟨v',hv',hu',he⟩ := exec_emb_ovr_within_stock plan.solver plan.solver_injective
    (body' := body) (fun p : Empty => nomatch p) hei v rfl S rfl
  have hbank : embOvr plan.solver (retiredReplicaNumericalKeyBank (embStk plan.solver S) rhsTail cacheTail).get S =
      {S with R := (Function.update (Function.update (Function.update S.R
        (plan.solver 110) rhsTail) (plan.solver 117) cacheTail) (plan.solver 118) [])} := by
    let B : Stacks 121 A := {embStk plan.solver S with R :=
      (Function.update (Function.update (embStk plan.solver S).R 110 rhsTail) 117 cacheTail)}
    change embOvr plan.solver {B with R := Function.update B.R 118 []}.get S = _
    rw [embOvr_updR plan.solver_injective]
    dsimp only [B]
    rw [embOvr_updateR_updateR plan.solver_injective]
  rw [hbank] at he
  exact ⟨v',m,hu'.trans hu,hm,he⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
