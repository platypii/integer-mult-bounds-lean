module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaCouplingPageStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedCouplingCounters
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedInitializeCouplingMasks

/-! Generate shared geometry and coefficients before scalar counters. The final
retained readiness, page and geometry are the inputs to every replica pass. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def initializeCachedReplicaCouplingRuntime {plan : ReplicaInteriorPlacement T}
    (placement : ReplicaCouplingPlacement plan) : Pr P T Q A U :=
  .seq (.seq (initializeReplicaCouplingPage placement) (placedInitializeCouplingMasks placement.bank false))
    (placedCouplingCounters (fun i => plan.solver (weightCacheCoreReg i)))

def initializeCachedReplicaCouplingRuntimeCost (V precision q w s t u band a b : ℕ) :=
  prepareReplicaCouplingGeometryCost V s t band a b+
    sharedCouplingCoefficientIntervalCost precision q w s t u band a b V+
    initializeRecoveryMasksCost V (b-a) band+replicaCouplingCountersCost q w band

noncomputable def initializeCachedReplicaCouplingRuntimeWorkspace (V precision q w s t u band a b : ℕ) : ℕ :=
  24*(prepareReplicaCouplingGeometryCost V s t band a b+
    sharedCouplingCoefficientIntervalCost precision q w s t u band a b V+replicaCouplingCountersCost q w band)+
  mnProgPush (initializeCouplingMasks false (P := Empty) (Q := Q) (A := A) (U := U))*
    initializeRecoveryMasksCost V (b-a) band

theorem initializeCachedReplicaCouplingRuntime_exec_within {plan : ReplicaInteriorPlacement T}
    (placement : ReplicaCouplingPlacement plan) {V precision q w s t u band a b : ℕ} [NeZero s]
    (hA : 4 ≤ A) (hw5 : 5 ≤ w) (hqw : q+4 ≤ w) (hprecision : 13 ≤ precision) (hst : s < t) (hab : a ≤ b) (hb : b ≤ s) (ha : a < s) (hband : band ≤ s)
    (hwide : 8*(t+1)^2+4*band+8 < 2^V) (hfitV : a+((b-a)+2*band)+s < 2^V)
    (raw : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hready : CouplingReady precision q w s t u band a b raw (embStk weightCacheCoreReg (embStk plan.solver S)))
    (hV : (S.R (plan.gather 115)).length = V) (htmp : S.R (plan.gather 7) = [])
    (h107 : S.R (placement.bank 107) = [])
    (hblank : ∀ k ∈ ([(0 : Fin 168),1,2,3,145,146,147,148,149,151,154,155,156,157,163,164,165]), S.R (placement.bank k) = [])
    (hfresh : ∀ k ∈ [(135 : Fin 168),139,140,143,166], S.R (placement.bank k) = []) (h136 : S.R (placement.bank 136) = []) (h158 : S.R (placement.bank 158) = [])
    (h159 : S.R (placement.bank 159) = []) (h161 : S.R (placement.bank 161) = []) (depth : ℕ) :
    ∃ v' F n, v'.user = v.user ∧
      n ≤ initializeCachedReplicaCouplingRuntimeCost V precision q w s t u band a b ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
        initializeCachedReplicaCouplingRuntimeWorkspace (Q := Q) (A := A) (U := U) V precision q w s t u band a b) depth
        (initializeCachedReplicaCouplingRuntime placement) (mk v S) n (mk v' F) ∧
      RetainedCouplingReady precision q w s t u band a b raw (embStk weightCacheCoreReg (embStk plan.solver F)) ∧
      CouplingIntervalMetadata V s t band a b a (b-a) (embStk placement.bank F) ∧
      F.R (placement.bank 138) = cstream A w (couplingCoefficientPageInterval precision q s t u band a b a (b-a))++S.R (placement.bank 138) ∧
      embStk plan.gather F = embStk plan.gather S ∧ F.L = S.L ∧ F.inp = S.inp ∧ F.out = S.out ∧
      (F.R (placement.bank 139)).length = (couplingCoefficientPageInterval precision q s t u band a b a (b-a)).length ∧
      (F.R (placement.bank 140)).length = 2*band+1 ∧
      (∀ k, (∀ i : Fin 168, placement.bank i ≠ k) → F.R k = S.R k) ∧
      (∀ k ∈ [(127 : Fin 168),143,166,158,135,167], S.R (placement.bank k) = [] → F.R (placement.bank k) = []) ∧
      embStk weightCacheCoreReg (embStk plan.solver F) =
        {embStk weightCacheCoreReg (embStk plan.solver S) with R := counterR q w (embStk weightCacheCoreReg (embStk plan.solver S)).R} ∧
      (∀ k : Fin 168, 117 ≤ k.val → k ∉ replicaCouplingSetupPorts → k ≠ 159 → k ≠ 161 →
        F.R (placement.bank k) = S.R (placement.bank k)) ∧
      F.R (placement.bank 159) = (couplingRibbonFlags (s := s) false t band a b a (b-a)).map (fun flag => pairSym A flag flag) ∧
      F.R (placement.bank 161) = recoveryGuardIntervalSymbols true A s t (2*band) a b a (b-a) := by
  obtain ⟨v₀,J₀,n₀,hu₀,hn₀,he₀,hready₀,hmeta₀,hpage₀,hgather₀,hleft₀,hi₀,ho₀,hcount₀,hrows₀,hoff₀,hfresh₀,hnative₀,hshared₀⟩ :=
    initializeReplicaCouplingPage_exec_within (body := body) placement hA hprecision hst hab hb ha hwide hfitV
      raw v S hready hV htmp h107 hblank hfresh depth
  have hclean (k : Fin 168) (hk : k.val < 63) : J₀.R (placement.bank k) = [] := by
    have hn := hready₀.low ⟨k.val,by omega⟩ hk
    rw [← placement.native_view J₀] at hn
    exact hn
  obtain ⟨v₁,nm,hum,hnm,hem⟩ := placedInitializeCouplingMasks_exec_within (body := body)
    placement.bank placement.bank_injective false hst (ha.le) hb hband (by omega) hwide hfitV v₀ J₀ hmeta₀ hclean
    (by rw [hshared₀ 136 (by decide)]; exact h136)
    (by rw [hshared₀ 158 (by decide)]; exact h158)
    (by rw [hshared₀ 159 (by decide)]; exact h159)
    (by rw [hshared₀ 161 (by decide)]; exact h161)
  let J := couplingMasksState placement.bank false s t band a b a (b-a) J₀
  have hmask (k : Fin 168) (hk159 : k ≠ 159) (hk161 : k ≠ 161) :
      J.R (placement.bank k) = J₀.R (placement.bank k) := by
    exact couplingMasksState_frame placement.bank false s t band a b a (b-a) J₀ (placement.bank k)
      (fun hh => hk159 (placement.bank_injective hh)) (fun hh => hk161 (placement.bank_injective hh))
  have hnativeMask : embStk weightCacheCoreReg (embStk plan.solver J) =
      embStk weightCacheCoreReg (embStk plan.solver J₀) := by
    rw [← placement.native_view J,← placement.native_view J₀]
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    exact hmask _ (by have := k.isLt; intro hh; have := congrArg Fin.val hh; simp only [Fin.val_castLE] at this; omega)
      (by have := k.isLt; intro hh; have := congrArg Fin.val hh; simp only [Fin.val_castLE] at this; omega)
  have hreadyJ : CouplingReady precision q w s t u band a b raw (embStk weightCacheCoreReg (embStk plan.solver J)) := by
    rw [hnativeMask]; exact hready₀
  have hmeta := hmeta₀.of_frame (F := embStk placement.bank J) (hmask 163 (by decide) (by decide)) (by
    intro k hk
    have hh : k ≠ 159 ∧ k ≠ 161 := by
      simp only [couplingIntervalPorts,List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact hmask k hh.1 hh.2)
  have hpage := (hmask 138 (by decide) (by decide)).trans hpage₀
  have hcount : (J.R (placement.bank 139)).length = (couplingCoefficientPageInterval precision q s t u band a b a (b-a)).length := by rw [hmask 139 (by decide) (by decide)]; exact hcount₀
  have hrows : (J.R (placement.bank 140)).length = 2*band+1 := by rw [hmask 140 (by decide) (by decide)]; exact hrows₀
  have hgather₁ : embStk plan.gather J = embStk plan.gather S := by
    refine (show embStk plan.gather J = embStk plan.gather J₀ from Stacks.ext rfl rfl rfl ?_).trans hgather₀
    funext k
    exact couplingMasksState_frame placement.bank false s t band a b a (b-a) J₀ (plan.gather k)
      (placement.bank_gather_disjoint 159 k).symm (placement.bank_gather_disjoint 161 k).symm
  have hoff₁ (k : Fin T) (hk : ∀ i : Fin 168, placement.bank i ≠ k) : J.R k = S.R k :=
    (couplingMasksState_frame placement.bank false s t band a b a (b-a) J₀ k (hk 159).symm (hk 161).symm).trans (hoff₀ k hk)
  have hfreshJ (k : Fin 168) (hk : k ∈ [(127 : Fin 168),143,166,158,135,167])
      (hS : S.R (placement.bank k) = []) : J.R (placement.bank k) = [] := by
    have hh : k ≠ 159 ∧ k ≠ 161 := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact (hmask k hh.1 hh.2).trans (hfresh₀ k hk hS)
  have hnativeJ := hnativeMask.trans hnative₀
  have hu₁ := hum.trans hu₀
  have hleft₁ : J.L = S.L := hleft₀
  have hi₁ : J.inp = S.inp := hi₀
  have ho₁ : J.out = S.out := ho₀
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
  refine ⟨v₂,F,(n₀+nm)+n₂,hu₂.trans hu₁,?_,?_,hretained,?_,?_,hgather₂.trans hgather₁,
    hleft₂.trans hleft₁,hi₂.trans hi₁,ho₂.trans ho₁,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · unfold initializeCachedReplicaCouplingRuntimeCost
    omega
  · have hsize := he₀.final
    have hmaskSize := (hem depth).final
    change mnSize (mk v₁ J)+depth ≤ _ at hmaskSize
    refine .seq (.seq (he₀.mono ?_) ((hem depth).mono ?_)) (he₂.mono ?_)
    all_goals intro d z hz; dsimp only [initializeCachedReplicaCouplingRuntimeWorkspace] at *; omega
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

  · intro k hk hnot hk159 hk161
    exact (hhigh k hk).trans ((hmask k hk159 hk161).trans (hshared₀ k hnot))
  · rw [hhigh 159 (by decide)]
    simp [J,couplingMasksState,placement.bank_injective.ne (by decide : (159 : Fin 168) ≠ 161)]
  · rw [hhigh 161 (by decide)]
    simp [J,couplingMasksState]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
