module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPrepareReplicaCouplingGeometry
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPrepareReplicaCouplingPage

/-! Build binary geometry and the shared coefficient page once before initializing
scalar counters. Both setup executions preserve ordinary coupling readiness. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def initializeReplicaCouplingPage {plan : ReplicaInteriorPlacement T}
    (placement : ReplicaCouplingPlacement plan) : Pr P T Q A U :=
  .seq (prepareReplicaCouplingGeometry placement) (prepareReplicaCouplingPage placement)

theorem initializeReplicaCouplingPage_exec {plan : ReplicaInteriorPlacement T}
    (placement : ReplicaCouplingPlacement plan) {V precision q w s t u band a b : ℕ} [NeZero s]
    (hA : 4 ≤ A) (hprecision : 13 ≤ precision) (hst : s < t) (hab : a ≤ b) (hb : b ≤ s) (ha : a < s)
    (hwide : 8*(t+1)^2+4*band+8 < 2^V) (hfitV : a+((b-a)+2*band)+s < 2^V)
    (raw : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hready : CouplingReady precision q w s t u band a b raw (embStk weightCacheCoreReg (embStk plan.solver S)))
    (hV : (S.R (plan.gather 115)).length = V) (htmp : S.R (plan.gather 7) = [])
    (h107 : S.R (placement.bank 107) = [])
    (hblank : ∀ k ∈ ([(0 : Fin 168),1,2,3,145,146,147,148,149,151,154,155,156,157,163,164,165]), S.R (placement.bank k) = [])
    (hfresh : ∀ k ∈ [(135 : Fin 168),139,140,143,166], S.R (placement.bank k) = []) :
    ∃ v' F n, v'.user = v.user ∧
      n ≤ prepareReplicaCouplingGeometryCost V s t band a b+sharedCouplingCoefficientIntervalCost precision q w s t u band a b V ∧
      Exec body (initializeReplicaCouplingPage placement) (mk v S) n (mk v' F) ∧
      CouplingReady precision q w s t u band a b raw (embStk weightCacheCoreReg (embStk plan.solver F)) ∧
      CouplingIntervalMetadata V s t band a b a (b-a) (embStk placement.bank F) ∧
      F.R (placement.bank 138) = cstream A w (couplingCoefficientPageInterval precision q s t u band a b a (b-a))++S.R (placement.bank 138) ∧
      embStk plan.gather F = embStk plan.gather S ∧ F.L = S.L ∧ F.inp = S.inp ∧ F.out = S.out ∧
      (F.R (placement.bank 139)).length = (couplingCoefficientPageInterval precision q s t u band a b a (b-a)).length ∧
      (F.R (placement.bank 140)).length = 2*band+1 ∧
      (∀ k, (∀ i : Fin 168, placement.bank i ≠ k) → F.R k = S.R k) ∧
      (∀ k ∈ [(127 : Fin 168),143,166,158,135,167], S.R (placement.bank k) = [] → F.R (placement.bank k) = []) ∧
      embStk weightCacheCoreReg (embStk plan.solver F) = embStk weightCacheCoreReg (embStk plan.solver S) := by
  have hheaders : ∀ p ∈ couplingGeometryAssignments,
      (S.R (placement.bank p.1)).length = couplingGeometryHeaderValue s t band a b p.1 := by
    intro p hp
    simp only [couplingGeometryAssignments,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp only [couplingGeometryHeaderValue,↓reduceIte]
    · simpa [embStk,ReplicaCouplingPlacement.bank,weightCacheCoreReg] using hready.axis
    · simpa [embStk,ReplicaCouplingPlacement.bank,weightCacheCoreReg] using hready.period
    · simpa [embStk,ReplicaCouplingPlacement.bank,weightCacheCoreReg] using hready.bandwidth
    · simpa [embStk,ReplicaCouplingPlacement.bank,weightCacheCoreReg] using hready.lower
    · simpa [embStk,ReplicaCouplingPlacement.bank,weightCacheCoreReg] using hready.upper
    · simpa [embStk,ReplicaCouplingPlacement.bank,weightCacheCoreReg] using hready.lower
    · simpa [embStk,ReplicaCouplingPlacement.bank,weightCacheCoreReg] using hready.upper
  have hbV : b < 2^V := by nlinarith only [hwide,hb,hst]
  obtain ⟨v₁,G,n₁,hu₁,hn₁,he₁,hmeta,hgather₁,hnative₁,hleft₁,hi₁,ho₁,hoff₁,hframe₁⟩ :=
    prepareReplicaCouplingGeometry_exec_within (body := body) placement V s t band a b hab hbV hfitV
      v S hV hheaders hblank htmp 0
  have hreadyG : CouplingReady precision q w s t u band a b raw (embStk weightCacheCoreReg (embStk plan.solver G)) := by
    rw [hnative₁]
    exact hready
  obtain ⟨v₂,F,n₂,hu₂,hn₂,he₂,hview,hgather₂,hnative₂,hmetaF,hleft₂,hi₂,ho₂,hoff₂⟩ :=
    prepareReplicaCouplingPage_exec (body := body) placement hA hprecision hst hab hb ha hwide hfitV raw v₁ G hreadyG hmeta
      (by rw [hframe₁ 107 (by decide) (by decide)]; exact h107)
      (by intro k hk
          have hn : k ≠ 163 ∧ k ∉ ([(145 : Fin 168),146,147,148,149,151,154,155,156,164,165]) := by
            simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
            rcases hk with rfl | rfl | rfl | rfl | rfl <;> decide
          rw [hframe₁ k hn.1 hn.2]
          exact hfresh k hk)
  refine ⟨v₂,F,n₁+n₂,hu₂.trans hu₁,by omega,.seq he₁.toExec he₂,?_,hmetaF,?_,
    hgather₂.trans hgather₁,hleft₂.trans hleft₁,hi₂.trans hi₁,ho₂.trans ho₁,?_,?_,?_,?_,hnative₂.trans hnative₁⟩
  · rw [hnative₂]
    exact hreadyG
  · have hp := congrFun (congrArg Stacks.R hview) 138
    change F.R (placement.bank 138) = _ at hp
    simpa [sharedCouplingPageState,embStk_R,hframe₁ 138 (by decide) (by decide)] using hp
  · have hp := congrFun (congrArg Stacks.R hview) 139
    change F.R (placement.bank 139) = _ at hp
    simp only [sharedCouplingPageState,Function.update_apply] at hp
    simp [hp]
  · have hp := congrFun (congrArg Stacks.R hview) 140
    change F.R (placement.bank 140) = _ at hp
    simp only [sharedCouplingPageState,Function.update_apply] at hp
    simp [hp]

  · intro k hk
    exact (hoff₂ k hk).trans (hoff₁ k hk)

  · intro k hk hkS
    have hn : k ≠ 163 ∧ k ∉ ([(145 : Fin 168),146,147,148,149,151,154,155,156,164,165]) := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have hG := (hframe₁ k hn.1 hn.2).trans hkS
    have hp := congrFun (congrArg Stacks.R hview) k
    change F.R (placement.bank k) = _ at hp
    rw [hp]
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [sharedCouplingPageState,embStk_R,hG]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
