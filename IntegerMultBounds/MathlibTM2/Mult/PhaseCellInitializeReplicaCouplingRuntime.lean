module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaCouplingPageStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedCouplingCounters

/-! Generate shared geometry and coefficients before scalar counters. The final
retained readiness, page and geometry are the inputs to every replica pass. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def initializeReplicaCouplingRuntime {plan : ReplicaInteriorPlacement T}
    (placement : ReplicaCouplingPlacement plan) : Pr P T Q A U :=
  .seq (initializeReplicaCouplingPage placement)
    (placedCouplingCounters (fun i => plan.solver (weightCacheCoreReg i)))

def initializeReplicaCouplingRuntimeCost (V precision q w s t u band a b : ℕ) :=
  prepareReplicaCouplingGeometryCost V s t band a b+
    sharedCouplingCoefficientIntervalCost precision q w s t u band a b V+replicaCouplingCountersCost q w band

theorem initializeReplicaCouplingRuntime_exec_within {plan : ReplicaInteriorPlacement T}
    (placement : ReplicaCouplingPlacement plan) {V precision q w s t u band a b : ℕ} [NeZero s]
    (hA : 4 ≤ A) (hw5 : 5 ≤ w) (hqw : q+4 ≤ w) (hprecision : 13 ≤ precision) (hst : s < t) (hab : a ≤ b) (hb : b ≤ s) (ha : a < s)
    (hwide : 8*(t+1)^2+4*band+8 < 2^V) (hfitV : a+((b-a)+2*band)+s < 2^V)
    (raw : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hready : CouplingReady precision q w s t u band a b raw (embStk weightCacheCoreReg (embStk plan.solver S)))
    (hV : (S.R (plan.gather 115)).length = V) (htmp : S.R (plan.gather 7) = [])
    (h107 : S.R (placement.bank 107) = [])
    (hblank : ∀ k ∈ ([(0 : Fin 168),1,2,3,145,146,147,148,149,151,154,155,156,157,163,164,165]), S.R (placement.bank k) = [])
    (hfresh : ∀ k ∈ [(135 : Fin 168),139,140,143,166], S.R (placement.bank k) = []) (depth : ℕ) :
    ∃ v' F n, v'.user = v.user ∧
      n ≤ initializeReplicaCouplingRuntimeCost V precision q w s t u band a b ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
        24*(initializeReplicaCouplingRuntimeCost V precision q w s t u band a b)) depth
        (initializeReplicaCouplingRuntime placement) (mk v S) n (mk v' F) ∧
      RetainedCouplingReady precision q w s t u band a b raw (embStk weightCacheCoreReg (embStk plan.solver F)) ∧
      CouplingIntervalMetadata V s t band a b a (b-a) (embStk placement.bank F) ∧
      F.R (placement.bank 138) = cstream A w (couplingCoefficientPageInterval precision q s t u band a b a (b-a))++S.R (placement.bank 138) ∧
      embStk plan.gather F = embStk plan.gather S ∧ F.L = S.L ∧ F.inp = S.inp ∧ F.out = S.out ∧
      (F.R (placement.bank 139)).length = (couplingCoefficientPageInterval precision q s t u band a b a (b-a)).length ∧
      (F.R (placement.bank 140)).length = 2*band+1 ∧
      (∀ k, (∀ i : Fin 168, placement.bank i ≠ k) → F.R k = S.R k) ∧
      (∀ k ∈ [(127 : Fin 168),143,166,158,135,167], S.R (placement.bank k) = [] → F.R (placement.bank k) = []) ∧
      embStk weightCacheCoreReg (embStk plan.solver F) =
        {embStk weightCacheCoreReg (embStk plan.solver S) with R := counterR q w (embStk weightCacheCoreReg (embStk plan.solver S)).R} := by
  obtain ⟨v₁,J,n₁,hu₁,hn₁,he₁,hreadyJ,hmeta,hpage,hgather₁,hleft₁,hi₁,ho₁,hcount,hrows,hoff₁,hfreshJ,hnativeJ⟩ :=
    initializeReplicaCouplingPage_exec_within (body := body) placement hA hprecision hst hab hb ha hwide hfitV
      raw v S hready hV htmp h107 hblank hfresh depth
  let e := fun i => plan.solver (weightCacheCoreReg i)
  have he : Function.Injective e := plan.solver_injective.comp weightCacheCoreReg_injective
  obtain ⟨v₂,F,n₂,hu₂,hn₂,he₂,hretained,hcounter,hleft₂,hi₂,ho₂,hframe₂⟩ :=
    placedCouplingCounters_exec_within (body := body) e he hw5 hqw raw v₁ J hreadyJ depth
  have hhigh (k : Fin 168) (hk : 117 ≤ k.val) : F.R (placement.bank k) = J.R (placement.bank k) := by
    apply hframe₂
    intro i hi
    have hv : i.val = k.val := congrArg Fin.val (placement.bank_injective ((placement.bank_native i).trans hi))
    have hiBound := i.isLt
    omega
  have hgather₂ : embStk plan.gather F = embStk plan.gather J := by
    refine Stacks.ext hi₂ ho₂ ?_ ?_
    · exact congrArg (fun L => L ∘ plan.gather) hleft₂
    · funext k
      exact hframe₂ _ (fun i => (plan.disjoint k (weightCacheCoreReg i)).symm)
  refine ⟨v₂,F,n₁+n₂,hu₂.trans hu₁,?_,?_,hretained,?_,?_,hgather₂.trans hgather₁,
    hleft₂.trans hleft₁,hi₂.trans hi₁,ho₂.trans ho₁,?_,?_,?_,?_,?_⟩
  · unfold initializeReplicaCouplingRuntimeCost
    omega
  · have hsize := he₁.final
    refine .seq (he₁.mono ?_) (he₂.mono ?_)
    all_goals intro d z hz; dsimp only [initializeReplicaCouplingRuntimeCost] at *; omega
  · apply hmeta.of_frame (hhigh 163 (by decide))
    intro k hk
    apply hhigh
    simp only [couplingIntervalPorts,List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · exact (hhigh 138 (by decide)).trans hpage
  · rw [hhigh 139 (by decide)]
    exact hcount
  · rw [hhigh 140 (by decide)]
    exact hrows

  · intro k hk
    apply (hframe₂ k (fun i => by
      change plan.solver (weightCacheCoreReg i) ≠ k
      rw [← placement.bank_native i]
      exact hk _)).trans
    exact hoff₁ k hk

  · intro k hk hkS
    rw [hhigh k (by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)]
    exact hfreshJ k hk hkS

  · change embStk e F = {embStk e S with R := counterR q w (embStk e S).R}
    have hh : embStk e J = embStk e S := hnativeJ
    rw [hcounter,hh]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
