module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInitializeReplicaCouplingPage
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCouplingCoefficientPageStock

/-! Native workspace for the actual shared geometry and coefficient-page phase. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

theorem initializeReplicaCouplingPage_native {plan : ReplicaInteriorPlacement T}
    (placement : ReplicaCouplingPlacement plan) :
    mnNativePushBound 24 (initializeReplicaCouplingPage (P := P) (Q := Q) (A := A) (U := U) placement) := by
  change mnNativePushBound 24 (.seq (prepareReplicaCouplingGeometry placement) (prepareReplicaCouplingPage placement))
  refine ⟨⟨?_,?_⟩,?_⟩
  · simp [ucopy,umulSym,scanR,drainR,popDo,keepIn,pushN,moveR,moveStep,whileR,peekR,mnNativePushBound,mnActPush]
  · exact embProg_native placement.bank Empty.elim _
      (mnNativePushBound_mono (by decide) generateCouplingGeometry_native)
  · exact embProg_native placement.bank Empty.elim _ ordinaryCouplingCoefficientInterval_native

theorem initializeReplicaCouplingPage_exec_within {plan : ReplicaInteriorPlacement T}
    (placement : ReplicaCouplingPlacement plan) {V precision q w s t u band a b : ℕ} [NeZero s]
    (hA : 4 ≤ A) (hprecision : 13 ≤ precision) (hst : s < t) (hab : a ≤ b) (hb : b ≤ s) (ha : a < s)
    (hwide : 8*(t+1)^2+4*band+8 < 2^V) (hfitV : a+((b-a)+2*band)+s < 2^V)
    (raw : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hready : CouplingReady precision q w s t u band a b raw (embStk weightCacheCoreReg (embStk plan.solver S)))
    (hV : (S.R (plan.gather 115)).length = V) (htmp : S.R (plan.gather 7) = [])
    (h107 : S.R (placement.bank 107) = [])
    (hblank : ∀ k ∈ ([(0 : Fin 168),1,2,3,145,146,147,148,149,151,154,155,156,157,163,164,165]), S.R (placement.bank k) = [])
    (hfresh : ∀ k ∈ [(135 : Fin 168),139,140,143,166], S.R (placement.bank k) = []) (depth : ℕ) :
    ∃ v' F n, v'.user = v.user ∧
      n ≤ prepareReplicaCouplingGeometryCost V s t band a b+sharedCouplingCoefficientIntervalCost precision q w s t u band a b V ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
        24*(prepareReplicaCouplingGeometryCost V s t band a b+sharedCouplingCoefficientIntervalCost precision q w s t u band a b V)) depth
        (initializeReplicaCouplingPage placement) (mk v S) n (mk v' F) ∧
      CouplingReady precision q w s t u band a b raw (embStk weightCacheCoreReg (embStk plan.solver F)) ∧
      CouplingIntervalMetadata V s t band a b a (b-a) (embStk placement.bank F) ∧
      F.R (placement.bank 138) = cstream A w (couplingCoefficientPageInterval precision q s t u band a b a (b-a))++S.R (placement.bank 138) ∧
      embStk plan.gather F = embStk plan.gather S ∧ F.L = S.L ∧ F.inp = S.inp ∧ F.out = S.out ∧
      (F.R (placement.bank 139)).length = (couplingCoefficientPageInterval precision q s t u band a b a (b-a)).length ∧
      (F.R (placement.bank 140)).length = 2*band+1 ∧
      (∀ k, (∀ i : Fin 168, placement.bank i ≠ k) → F.R k = S.R k) ∧
      (∀ k ∈ [(127 : Fin 168),143,166,158,135,167], S.R (placement.bank k) = [] → F.R (placement.bank k) = []) ∧
      embStk weightCacheCoreReg (embStk plan.solver F) = embStk weightCacheCoreReg (embStk plan.solver S) := by
  obtain ⟨v',F,n,hu,hn,he,hreadyF,hmeta,hpage,hgather,hleft,hi,ho,hcount,hrows,hoff,hfreshF,hnative⟩ :=
    initializeReplicaCouplingPage_exec (body := body) placement hA hprecision hst hab hb ha hwide hfitV
      raw v S hready hV htmp h107 hblank hfresh
  exact ⟨v',F,n,hu,hn,mn_native_exec_within he 24 (initializeReplicaCouplingPage_native placement) depth _
    (Nat.add_le_add_left (Nat.mul_le_mul_left 24 hn) _),hreadyF,hmeta,hpage,hgather,hleft,hi,ho,hcount,hrows,hoff,hfreshF,hnative⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
