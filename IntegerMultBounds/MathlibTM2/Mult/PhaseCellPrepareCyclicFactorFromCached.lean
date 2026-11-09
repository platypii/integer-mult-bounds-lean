module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInstallCyclicFactorSeeds
public import IntegerMultBounds.MathlibTM2.Host.ClosedProgramStock
public import IntegerMultBounds.MathlibTM2.Host.NativePushBoundMono

/-! Cached masters generate the factor's ordinary seeds and boundary page in
one physical execution, preserving both numerical inputs and external storage. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
open CyclicReplicaPlacement
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

private theorem owned_preimage {m n : ℕ} (job : CachedReplicaPassPlacement m)
    (e : Fin m → Fin n) (he : Function.Injective e) {k : Fin n}
    (h : (job.reindex e he).Owns k) : ∃ i, job.Owns i ∧ e i = k := by
  cases h with
  | bank i => exact ⟨job.coupling.bank i,.bank i,by simp [CachedReplicaPassPlacement.reindex]⟩
  | gather i => exact ⟨job.plan.gather i,.gather i,rfl⟩
  | solver i => exact ⟨job.plan.solver i,.solver i,rfl⟩
  | output => exact ⟨job.output,.output,rfl⟩
  | rhs => exact ⟨job.rhs,.rhs,rfl⟩

private theorem cached_of_factor_frame {s : ℕ} {H : ReplicaHaloProblem s}
    (bank : Fin 834 → Fin T) (hbank : Function.Injective bank) (job : CachedReplicaPassPlacement 834)
    (hsep : ∀ i, ¬job.Owns (factorReg i)) {buffers : ReplicaLoopBuffers A} {S G : Stacks T A}
    (h : CachedReplicaPassInput H (job.reindex bank hbank) buffers S)
    (hI : G.inp = S.inp) (hO : G.out = S.out) (hL : G.L = S.L)
    (hR : ∀ k, (∀ i, bank (factorReg i) ≠ k) → G.R k = S.R k) :
    CachedReplicaPassInput H (job.reindex bank hbank) buffers G := by
  apply h.of_frame hI hO
  intro k hk
  refine ⟨congrFun hL k,hR k ?_⟩
  obtain ⟨j,hj,rfl⟩ := owned_preimage job bank hbank hk
  intro i hi
  have he := hbank hi
  apply hsep i
  rw [he]
  exact hj

def prepareCyclicFactorFromCached (bank : Fin 834 → Fin T) (span tmp : Fin T) : Pr P T Q A U :=
  .seq (installCyclicFactorSeeds (bank ∘ factorReg)
    (cachedFactorSeedSource (bank ∘ left.plan.gather) span) tmp)
    (embProg (bank ∘ factorReg) id prepareCyclicFactorInput)

@[irreducible] def cyclicFactorPreparationPush : ℕ :=
  max 2 (mnProgPush (prepareCyclicBoundaryPage (P := Empty) (Q := Q) (A := A) (U := U)))

theorem prepareCyclicFactorFromCached_native (bank : Fin 834 → Fin T) (span tmp : Fin T) :
    mnNativePushBound (cyclicFactorPreparationPush (Q := Q) (A := A) (U := U))
      (prepareCyclicFactorFromCached (P := P) (Q := Q) (A := A) (U := U) bank span tmp) := by
  have hcopy : 2 ≤ cyclicFactorPreparationPush (Q := Q) (A := A) (U := U) := by
    unfold cyclicFactorPreparationPush
    exact Nat.le_max_left _ _
  have hpage : mnProgPush (prepareCyclicBoundaryPage (P := Empty) (Q := Q) (A := A) (U := U)) ≤
      cyclicFactorPreparationPush (Q := Q) (A := A) (U := U) := by
    unfold cyclicFactorPreparationPush
    exact Nat.le_max_right _ _
  unfold prepareCyclicFactorFromCached installCyclicFactorSeeds prepareCyclicFactorInput
  exact ⟨mnNativePushBound_mono hcopy (copyUnaryHeaders_native _ _),
    embProg_native _ id _ (embProg_native _ Empty.elim _
      (mnNativePushBound_mono hpage (WordCmd.empty_native _)))⟩

/-- The intermediate seed bank is produced, rather than supplied. Its actual
page-generation cost is retained for the caller's setup ledger. -/
theorem prepareCyclicFactorFromCached_exec {p l s t u target a n : ℕ} [NeZero s]
    (bank : Fin 834 → Fin T) (hbank : Function.Injective bank)
    (hst : s < t) (ha : a < s) (hn : n ≤ s) (hband : PhaseCellBand.width p u ≤ s)
    (H K : ReplicaHaloProblem s) (buffersL buffersR : ReplicaLoopBuffers A)
    (span tmp : Fin T)
    (hsourceOff : ∀ i j, cachedFactorSeedSource (bank ∘ left.plan.gather) span i ≠ bank (factorReg j))
    (hsourceTmp : ∀ i, cachedFactorSeedSource (bank ∘ left.plan.gather) span i ≠ tmp)
    (hfactorTmp : ∀ i, bank (factorReg i) ≠ tmp) (v : HS T Q A U) (S : Stacks T A)
    (hleft : CachedReplicaPassInput H (left.reindex bank hbank) buffersL S)
    (hright : CachedReplicaPassInput K (right.reindex bank hbank) buffersR S)
    (hprofile : masterHeaderValues (2^15*H.p) (H.stage+1) H.precision H.l s H.t H.u H.band H.origin n =
      cyclicFactorMasterValues p l s t u target a n)
    (hspan : (S.R span).length = n)
    (hblank : ∀ i, S.R (bank (factorReg i)) = [])
    (hfactorLeft : ∀ i, S.L (bank (factorReg i)) = []) (htmp : S.R tmp = []) :
    let rs := masterHeaderCopies ((bank ∘ factorReg) ∘ Fin.castLE (by decide : 224 ≤ 234))
      (cachedFactorSeedSource (bank ∘ left.plan.gather) span)
    let copies := copyUnaryHeadersCost (fun k => (S.R k).length) rs
    ∃ (v' : HS T Q A U) (F G : Stacks T A) (steps : ℕ), v'.user = v.user ∧
      CyclicFactorSeedInput p l s t u target a n [] (embStk (bank ∘ factorReg) F) ∧
      steps ≤ copies+prepareCyclicBoundaryPageCost
        (embStk (Fin.castLE (by decide : 154 ≤ 234)) (embStk (bank ∘ factorReg) F)).R
        s t (PhaseCellBand.width p u) a n ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+0+
        cyclicFactorPreparationPush (Q := Q) (A := A) (U := U)*(copies+prepareCyclicBoundaryPageCost
          (embStk (Fin.castLE (by decide : 154 ≤ 234)) (embStk (bank ∘ factorReg) F)).R
          s t (PhaseCellBand.width p u) a n)) 0
        (prepareCyclicFactorFromCached bank span tmp) (mk v S) steps (mk v' G) ∧
      Exec body (prepareCyclicFactorFromCached bank span tmp) (mk v S) steps (mk v' G) ∧
      CyclicResidualBatchInput p l s t u target a n [] [] (embStk (bank ∘ factorReg) G) ∧
      CachedReplicaPassInput H (left.reindex bank hbank) buffersL G ∧
      CachedReplicaPassInput K (right.reindex bank hbank) buffersR G ∧
      (∀ k, (∀ i, bank (factorReg i) ≠ k) → G.L k = S.L k ∧ G.R k = S.R k) ∧
      G.R (bank (factorReg 226)) = [] ∧ G.R (bank (factorReg 229)) = [] := by
  dsimp only
  obtain ⟨v₁,F,hu₁,he₁,hseed,hI,hO,hL,hR⟩ := installCyclicFactorSeeds_from_cached_exec
    (body := body) H (bank ∘ left.plan.gather) buffersL (bank ∘ factorReg)
    (hbank.comp factorReg_injective) span tmp hsourceOff hsourceTmp hfactorTmp v S
    hleft.headers hprofile hspan hblank hfactorLeft htmp
  have hl := cached_of_factor_frame bank hbank left (fun i => (factor_disjoint i).1) hleft hI hO hL hR
  have hr := cached_of_factor_frame bank hbank right (fun i => (factor_disjoint i).2) hright hI hO hL hR
  obtain ⟨v₂,G,m,hu₂,hm,he₂,hinput,hl',hr',hframe,hhigh⟩ := prepareCyclicFactorInput_placed_exec
    (outerBody := body) bank hbank hst ha hn hband H K buffersL buffersR v₁ F [] hseed hl hr
  let copies := copyUnaryHeadersCost (fun k => (S.R k).length)
    (masterHeaderCopies ((bank ∘ factorReg) ∘ Fin.castLE (by decide : 224 ≤ 234))
      (cachedFactorSeedSource (bank ∘ left.plan.gather) span))
  have hsteps := Nat.add_le_add_left hm copies
  have hex := Exec.seq he₁ he₂
  have hscaled := Nat.mul_le_mul_left (cyclicFactorPreparationPush (Q := Q) (A := A) (U := U)) hsteps
  have hwithin := mn_native_exec_within hex _ (prepareCyclicFactorFromCached_native bank span tmp) 0 _
    (Nat.add_le_add_left hscaled _)
  refine ⟨v₂,F,G,_,hu₂.trans hu₁,hseed,hsteps,
    hwithin,hex,hinput,hl',hr',?_,?_,?_⟩
  · intro k hk
    exact ⟨(hframe k hk).1.trans (congrFun hL k),(hframe k hk).2.trans (hR k hk)⟩
  · exact (hhigh 226 (by decide)).trans (hseed.new 226 (by decide))
  · exact (hhigh 229 (by decide)).trans (hseed.new 229 (by decide))

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
