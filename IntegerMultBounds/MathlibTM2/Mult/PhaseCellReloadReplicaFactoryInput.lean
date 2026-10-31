module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReloadReplicaFactoryHeaders
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReloadReplicaOriginPackets

/-! Retained scalar masters and one ambient-origin page rebuild the ordinary
numerical factory input after retirement. Every gather tape is restored. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {T Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ T Q A U}

def reloadReplicaFactoryInput (plan : ReplicaInteriorPlacement T) : Pr P₀ T Q A U :=
  .seq (reloadReplicaFactoryHeaders plan)
    (reloadReplicaOriginPackets (plan.gather 121) (plan.gather 116) (plan.gather 115) (plan.gather 104)
      (plan.gather 107) (plan.gather 113) (plan.solver 109) (plan.gather 105) (plan.gather 106))

def reloadReplicaFactoryInputCost (P stage q l s t u band N B L w : ℕ) :=
  replicaFactoryHeaderCost P stage q l s t u band N B L w+
    reloadReplicaOriginPacketsCost N B (weightWorkspaceWidth P q w t u)

theorem reloadReplicaFactoryInput_exec_within (plan : ReplicaInteriorPlacement T)
    (P stage q l s t u band N B L w : ℕ) (hw : w = 2*q+8) (lo : ℕ → ℕ)
    (borrowed output suffix : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hbank : embStk weightCacheCoreReg (embStk plan.solver S) = releasedCellBank [] borrowed output S.inp S.out)
    (hmasters : ∀ r ∈ replicaFactoryHeaderCopies, (S.R (plan.gather r.1)).length =
      replicaFactoryHeaderValue P stage q l s t u band N B L w r.1)
    (hV : (S.R (plan.gather 115)).length = weightWorkspaceWidth P q w t u)
    (hpage : S.R (plan.gather 113) =
      (List.range B).flatMap (fun i => binSyms (weightWorkspaceWidth P q w t u) (lo i))++suffix)
    (hclean : ∀ k ∈ [(7 : Fin 126),104,105,106,107], S.R (plan.gather k) = []) (depth : ℕ) :
    ∃ v' F m, v'.user = v.user ∧ m ≤ reloadReplicaFactoryInputCost P stage q l s t u band N B L w ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
        2*reloadReplicaFactoryInputCost P stage q l s t u band N B L w) depth
        (reloadReplicaFactoryInput plan) (mk v S) m (mk v' F) ∧
      embStk weightCacheCoreReg (embStk plan.solver F) =
        replicaWeightFactoryInputBank A P stage q l s t u band N B L w lo [] borrowed output S.inp S.out ∧
      embStk plan.gather F = embStk plan.gather S ∧ F.inp = S.inp ∧ F.out = S.out ∧ F.L = S.L ∧
      ∀ k, (∀ r ∈ replicaFactoryHeaderCopies, plan.solver (weightCacheCoreReg r.2) ≠ k) → F.R k = S.R k := by
  let V := weightWorkspaceWidth P q w t u
  let page : List (Fin (A+4)) := (List.range B).flatMap (fun i => binSyms V (lo i))
  let rs := placedReplicaFactoryHeaderCopies plan
  let value := fun k => (S.R k).length
  obtain ⟨v₁,hu₁,he₁,hheader,hleft,hframe⟩ := reloadReplicaFactoryHeaders_exec_within (body := body)
    plan P stage q l s t u band N B L w borrowed output v S hbank hmasters (hclean _ (by simp)) depth
  let M : Stacks T A := {S with R := unaryCopiesR value S.R rs}
  have hg (k : Fin 126) : M.R (plan.gather k) = S.R (plan.gather k) :=
    hframe _ (fun r hr => (plan.disjoint k (weightCacheCoreReg r.2)).symm)
  have hcost : copyUnaryHeadersCost value rs = replicaFactoryHeaderCost P stage q l s t u band N B L w := by
    unfold copyUnaryHeadersCost
    change (replicaFactoryHeaderCopies.map (fun r => 4*value (plan.gather r.1)+4)).sum+1 = _
    rw [show replicaFactoryHeaderCopies.map (fun r => 4*value (plan.gather r.1)+4) =
      replicaFactoryHeaderCopies.map (fun r => 4*replicaFactoryHeaderValue P stage q l s t u band N B L w r.1+4) from
        List.map_congr_left (fun r hr => congrArg (fun n => 4*n+4) (hmasters r hr))]
    exact replicaFactoryHeaderCopies_cost P stage q l s t u band N B L w
  have hN : (S.R (plan.gather 121)).length = N := by
    simpa [replicaFactoryHeaderValue] using hmasters (121,113) (by simp [replicaFactoryHeaderCopies])
  have hB : (S.R (plan.gather 116)).length = B := by
    simpa [replicaFactoryHeaderValue] using hmasters (116,116) (by simp [replicaFactoryHeaderCopies])
  have hlen : page.length = B*V := by simp [page,List.length_flatMap]
  let regs : List (Fin 126 ⊕ Fin 121) :=
    [.inl 121,.inl 116,.inl 115,.inl 104,.inl 107,.inl 113,.inr 109,.inl 105,.inl 106]
  have hregs := List.Nodup.map plan.bank_injective (show regs.Nodup by decide)
  have hreg : [plan.gather 121,plan.gather 116,plan.gather 115,plan.gather 104,plan.gather 107,
      plan.gather 113,plan.solver 109,plan.gather 105,plan.gather 106].Nodup := by
    simpa only [regs,List.map_cons,List.map_nil,ReplicaInteriorPlacement.bank,Sum.elim_inl,Sum.elim_inr] using hregs
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := reloadReplicaOriginPackets_exec (body := body)
    (plan.gather 121) (plan.gather 116) (plan.gather 115) (plan.gather 104) (plan.gather 107)
    (plan.gather 113) (plan.solver 109) (plan.gather 105) (plan.gather 106) hreg N B V page suffix hlen v₁ M
    (by rw [hg]; exact hN) (by rw [hg]; exact hB) (by rw [hg]; exact hV)
    (by rw [hg]; exact hpage)
    (by
      intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl
      all_goals rw [hg]; exact hclean _ (by simp))
  let F : Stacks T A := {M with R := Function.update M.R (plan.solver 109) (page++((List.replicate N page).flatten++M.R (plan.solver 109)))}
  have hlevel : M.R (plan.solver 109) = List.replicate l tick := by
    have hh := congrArg (fun B : Stacks 117 A => B.R 109) hheader
    exact hh.trans (replicaFactoryUnaryBank_level A P stage q l s t u band N B L w borrowed output S.inp S.out)
  let e := fun k => plan.solver (weightCacheCoreReg k)
  have he : Function.Injective e := plan.solver_injective.comp weightCacheCoreReg_injective
  have hproj := embStk_updateR he M 109 (page++((List.replicate N page).flatten++M.R (plan.solver 109)))
  change embStk weightCacheCoreReg (embStk plan.solver F) =
    {embStk weightCacheCoreReg (embStk plan.solver M) with R :=
      (Function.update (embStk weightCacheCoreReg (embStk plan.solver M)).R 109
        (page++((List.replicate N page).flatten++M.R (plan.solver 109))))} at hproj
  rw [hheader,hlevel] at hproj
  have hfinal := hproj.trans (replicaFactoryUnaryBank_packets A P stage q l s t u band N B L w hw lo borrowed output S.inp S.out)
  have hm : copyUnaryHeadersCost value rs+m₂ ≤ reloadReplicaFactoryInputCost P stage q l s t u band N B L w := by
    rw [hcost]
    exact Nat.add_le_add_left hm₂ _
  have hex := Exec.seq he₁.toExec he₂
  have hpush : mnNativePushBound 2 (reloadReplicaFactoryInput (P₀ := P₀) (Q := Q) (A := A) (U := U) plan) :=
    ⟨copyUnaryHeaders_native _ _,reloadReplicaOriginPackets_native _ _ _ _ _ _ _ _ _⟩
  have hframeF : ∀ k, (∀ r ∈ replicaFactoryHeaderCopies, plan.solver (weightCacheCoreReg r.2) ≠ k) → F.R k = S.R k := by
    intro k hk
    have hk109 := hk (108,109) (by simp [replicaFactoryHeaderCopies])
    have hkDst : k ≠ plan.solver 109 := hk109.symm
    change Function.update M.R (plan.solver 109) (page++((List.replicate N page).flatten++M.R (plan.solver 109))) k = S.R k
    rw [Function.update_of_ne hkDst]
    exact hframe k hk
  have hgather : embStk plan.gather F = embStk plan.gather S := by
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    exact hframeF _ (fun r hr => (plan.disjoint k (weightCacheCoreReg r.2)).symm)
  exact ⟨v₂,F,copyUnaryHeadersCost value rs+m₂,hu₂.trans hu₁,hm,
    mn_native_exec_within hex 2 hpush depth _ (Nat.add_le_add_left (Nat.mul_le_mul_left 2 hm) _),
    hfinal,hgather,rfl,rfl,rfl,hframeF⟩

theorem reloadReplicaFactoryInputCost_replicas (P stage q l s t u band N B L w : ℕ) :
    reloadReplicaFactoryInputCost P stage q l s t u band N B L w =
      reloadReplicaFactoryInputCost P stage q l s t u band 0 B L w+
        N*(10*(B*weightWorkspaceWidth P q w t u)+19) := by
  unfold reloadReplicaFactoryInputCost replicaFactoryHeaderCost reloadReplicaOriginPacketsCost
  ring

/-- Only copied origin bytes and replica ticks repeat across RHSs. -/
theorem reloadReplicaFactoryInputCost_le_shared (P stage q l s t u band N B L w cV : ℕ)
    (hB : 1 ≤ B) (hL : 1 ≤ L) (hw : 1 ≤ w) (hV : weightWorkspaceWidth P q w t u ≤ cV*w) :
    reloadReplicaFactoryInputCost P stage q l s t u band N B L w ≤
      reloadReplicaFactoryInputCost P stage q l s t u band 0 B L w+(10*cV+19)*N*(B*L*w) := by
  have hrow : B*w ≤ B*L*w := Nat.mul_le_mul_right w (Nat.le_mul_of_pos_right B hL)
  have hv : B*weightWorkspaceWidth P q w t u ≤ cV*(B*L*w) := by
    calc
      _ ≤ B*(cV*w) := Nat.mul_le_mul_left B hV
      _ = cV*(B*w) := by ring
      _ ≤ _ := Nat.mul_le_mul_left cV hrow
  have hone : 1 ≤ B*L*w := Nat.mul_pos (Nat.mul_pos hB hL) hw
  have hbytes := Nat.mul_le_mul_left (10*N) hv
  have hticks := Nat.mul_le_mul_left (19*N) hone
  rw [reloadReplicaFactoryInputCost_replicas]
  nlinarith only [hbytes,hticks]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
