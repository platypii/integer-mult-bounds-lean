module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReloadReplicaCouplingHeaders
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedCouplingCounters

/-! Reload ordinary coupling headers and generate scalar counters once in the
released numerical bank. All gather masters and reserved cache tails survive. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def prepareReplicaCouplingNative (plan : ReplicaInteriorPlacement T) : Pr P T Q A U :=
  .seq (reloadReplicaCouplingHeaders plan)
    (placedCouplingCounters (fun i => plan.solver (weightCacheCoreReg i)))

def prepareReplicaCouplingNativeCost (precision q w s t u band a b : ℕ) :=
  replicaCouplingHeaderCost precision q w s t u band a b+replicaCouplingCountersCost q w band

theorem prepareReplicaCouplingNative_exec_within (plan : ReplicaInteriorPlacement T)
    (precision q w s t u band a b : ℕ) (hw5 : 5 ≤ w) (hqw : q+4 ≤ w)
    (borrowed output : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hbank : embStk weightCacheCoreReg (embStk plan.solver S) = releasedCellBank [] borrowed output S.inp S.out)
    (hmasters : ∀ r ∈ replicaCouplingHeaderCopies, (S.R (plan.gather r.1)).length =
      replicaCouplingMasterValue precision q w s t u band a b r.1)
    (htmp : S.R (plan.gather 7) = []) (depth : ℕ) :
    ∃ v' F n, v'.user = v.user ∧ n ≤ prepareReplicaCouplingNativeCost precision q w s t u band a b ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
        3*prepareReplicaCouplingNativeCost precision q w s t u band a b) depth
        (prepareReplicaCouplingNative plan) (mk v S) n (mk v' F) ∧
      RetainedCouplingReady precision q w s t u band a b borrowed (embStk weightCacheCoreReg (embStk plan.solver F)) ∧
      embStk plan.gather F = embStk plan.gather S ∧ F.L = S.L ∧ F.inp = S.inp ∧ F.out = S.out ∧
      (∀ j : Fin 121, 117 ≤ j.val → F.R (plan.solver j) = S.R (plan.solver j)) ∧
      (∀ k, (∀ i : Fin 117, plan.solver (weightCacheCoreReg i) ≠ k) → F.R k = S.R k) := by
  obtain ⟨v₁,hu₁,he₁,hready,hgather₁,hleft₁,hframe₁,_⟩ := reloadReplicaCouplingHeaders_exec_within (body := body)
    plan precision q w s t u band a b borrowed output v S hbank hmasters htmp depth
  let J : Stacks T A := {S with R := unaryCopiesR (fun k => (S.R k).length) S.R (placedReplicaHeaderCopies plan replicaCouplingHeaderCopies)}
  let e := fun i => plan.solver (weightCacheCoreReg i)
  have he : Function.Injective e := plan.solver_injective.comp weightCacheCoreReg_injective
  change CouplingReady precision q w s t u band a b borrowed (embStk e J) at hready
  obtain ⟨v₂,F,n₂,hu₂,hn₂,he₂,hretained,_,hleft₂,hi₂,ho₂,hframe₂⟩ :=
    placedCouplingCounters_exec_within (body := body) e he hw5 hqw borrowed v₁ J hready depth
  have hgather₂ : embStk plan.gather F = embStk plan.gather J := by
    refine Stacks.ext hi₂ ho₂ ?_ ?_
    · exact congrArg (fun L => L ∘ plan.gather) hleft₂
    · funext k
      exact hframe₂ _ (fun i => (plan.disjoint k (weightCacheCoreReg i)).symm)
  refine ⟨v₂,F,replicaCouplingHeaderCost precision q w s t u band a b+n₂,hu₂.trans hu₁,?_,?_,?_,
    hgather₂.trans hgather₁,hleft₂.trans hleft₁,hi₂,ho₂,?_,?_⟩
  · unfold prepareReplicaCouplingNativeCost
    omega
  · have hsize := he₁.final
    change mnSize (mk v₁ J)+depth ≤ mnSize (mk v S)+depth+
      2*replicaCouplingHeaderCost precision q w s t u band a b at hsize
    refine .seq (he₁.mono ?_) (he₂.mono ?_)
    all_goals intro d z hz; dsimp only [prepareReplicaCouplingNativeCost,replicaCouplingCountersCost] at *; omega
  · exact hretained
  · intro j hj
    have hsep (i : Fin 117) : e i ≠ plan.solver j := by
      intro h
      have hv := congrArg Fin.val (plan.solver_injective h)
      simp only [weightCacheCoreReg] at hv
      have hi := i.isLt
      omega
    have hF : F.R (plan.solver j) = J.R (plan.solver j) := hframe₂ _ hsep
    apply hF.trans
    apply hframe₁
    intro r hr
    exact hsep r.2

  · intro k hk
    apply (hframe₂ _ hk).trans
    exact hframe₁ k (fun r _ => hk r.2)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
