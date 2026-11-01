module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReloadReplicaCouplingHeaders
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCouplingReadinessStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetainedCouplingCounters
public import IntegerMultBounds.MathlibTM2.Host.EmbedStock

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
    (embProg (fun i => plan.solver (weightCacheCoreReg i)) Empty.elim (couplingReadiness (P₀ := Empty)))

def replicaCouplingCountersCost (q w band : ℕ) := prepareCost q w+6*q+4*band+10

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
  obtain ⟨v₁,hu₁,he₁,hready,hgather₁,hleft₁,hframe₁⟩ := reloadReplicaCouplingHeaders_exec_within (body := body)
    plan precision q w s t u band a b borrowed output v S hbank hmasters htmp depth
  let J : Stacks T A := {S with R := unaryCopiesR (fun k => (S.R k).length) S.R (placedReplicaHeaderCopies plan replicaCouplingHeaderCopies)}
  let e := fun i => plan.solver (weightCacheCoreReg i)
  have he : Function.Injective e := plan.solver_injective.comp weightCacheCoreReg_injective
  change CouplingReady precision q w s t u band a b borrowed (embStk e J) at hready
  obtain ⟨vi,n₂,hu₂,hn₂,hei,hretained⟩ := retainedCouplingCounters_exec (body := fun p : Empty => nomatch p)
    q w hw5 hqw borrowed (embDn e v₁) (embStk e J) hready
  have hei' := mn_native_exec_within hei 3 couplingReadiness_native depth _
    (Nat.add_le_add_left (Nat.mul_le_mul_left 3 hn₂) _)
  obtain ⟨v₂,hv₂,hu₂',he₂⟩ := exec_emb_ovr_within_stock e he (body' := body) (ι := Empty.elim)
    (fun p : Empty => nomatch p) hei' v₁ rfl J rfl
  let F : Stacks T A := embOvr e {embStk e J with R := counterR q w (embStk e J).R}.get J
  have hgather₂ : embStk plan.gather F = embStk plan.gather J := by
    refine Stacks.ext rfl rfl ?_ ?_ <;> funext k
    · exact (embOvr_off _ J (fun i => (plan.disjoint k (weightCacheCoreReg i)).symm)).1
    · exact (embOvr_off _ J (fun i => (plan.disjoint k (weightCacheCoreReg i)).symm)).2
  refine ⟨v₂,F,replicaCouplingHeaderCost precision q w s t u band a b+n₂,hu₂'.trans (hu₂.trans hu₁),?_,?_,?_,
    hgather₂.trans hgather₁,?_,rfl,rfl,?_,?_⟩
  · unfold prepareReplicaCouplingNativeCost replicaCouplingCountersCost
    omega
  · have hsize := he₁.final
    change mnSize (mk v₁ J)+depth ≤ mnSize (mk v S)+depth+
      2*replicaCouplingHeaderCost precision q w s t u band a b at hsize
    refine .seq (he₁.mono ?_) (he₂.mono ?_)
    all_goals intro d z hz; dsimp only [prepareReplicaCouplingNativeCost,replicaCouplingCountersCost] at *; omega
  · change RetainedCouplingReady precision q w s t u band a b borrowed (embStk e F)
    dsimp only [F]
    rw [embStk_ovr he]
    exact hretained
  · exact (embOvr_right_left J _).trans hleft₁
  · intro j hj
    have hsep (i : Fin 117) : e i ≠ plan.solver j := by
      intro h
      have hv := congrArg Fin.val (plan.solver_injective h)
      simp only [weightCacheCoreReg] at hv
      have hi := i.isLt
      omega
    have hF : F.R (plan.solver j) = J.R (plan.solver j) := (embOvr_off _ J hsep).2
    apply hF.trans
    apply hframe₁
    intro r hr
    exact hsep r.2

  · intro k hk
    apply ((embOvr_off _ J hk).2).trans
    exact hframe₁ k (fun r _ => hk r.2)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
