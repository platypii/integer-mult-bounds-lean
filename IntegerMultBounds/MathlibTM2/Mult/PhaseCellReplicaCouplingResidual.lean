module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaLocalCoupling
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFinishReplicaCouplingRow

/-! One staged replica computes its residual, archives it and releases both
owned source prefixes. The shared coefficient page is restored by construction. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def replicaResidualState {plan : ReplicaInteriorPlacement T} (placement : ReplicaCouplingPlacement plan)
    (dst : Fin T) (fieldTail rhsTail words : List (Fin (A+4))) (S : Stacks T A) : Stacks T A :=
  {S with R := (Function.update (Function.update (Function.update S.R (placement.bank 132) fieldTail)
    (placement.bank 93) rhsTail) dst (words++S.R dst))}

theorem replicaResidualState_native {plan : ReplicaInteriorPlacement T} (placement : ReplicaCouplingPlacement plan)
    (dst : Fin T) (hdst : ∀ i : Fin 117, plan.solver (weightCacheCoreReg i) ≠ dst)
    (fieldTail rhsTail words : List (Fin (A+4))) (S : Stacks T A) :
    embStk weightCacheCoreReg (embStk plan.solver (replicaResidualState placement dst fieldTail rhsTail words S)) =
      {embStk weightCacheCoreReg (embStk plan.solver S) with
        R := Function.update (embStk weightCacheCoreReg (embStk plan.solver S)).R 93 rhsTail} := by
  refine Stacks.ext rfl rfl rfl ?_
  funext i
  let e := fun i => plan.solver (weightCacheCoreReg i)
  have h132 : e i ≠ placement.bank 132 := by
    intro h
    have hv : i.val = 132 := congrArg Fin.val (placement.bank_injective ((placement.bank_native i).trans h))
    have hi := i.isLt
    omega
  have h93 : e i = placement.bank 93 ↔ i = 93 := by
    change e i = placement.bank (Fin.castLE (by decide : 117 ≤ 168) (93 : Fin 117)) ↔ i = 93
    rw [placement.bank_native (93 : Fin 117)]
    exact ⟨fun h => (plan.solver_injective.comp weightCacheCoreReg_injective) h,congrArg e⟩
  change Function.update (Function.update (Function.update S.R (placement.bank 132) fieldTail)
    (placement.bank 93) rhsTail) dst (words++S.R dst) (e i) = Function.update (S.R ∘ e) 93 rhsTail i
  have hidst : e i ≠ dst := hdst i
  simp [Function.update_apply,hidst,h93,h132]

theorem replicaResidualState_ready {plan : ReplicaInteriorPlacement T} (placement : ReplicaCouplingPlacement plan)
    {precision q w s t u band a b : ℕ} (dst : Fin T)
    (hdst : ∀ i : Fin 117, plan.solver (weightCacheCoreReg i) ≠ dst)
    (fieldTail rhsTail words raw : List (Fin (A+4))) (S : Stacks T A)
    (h : RetainedCouplingReady precision q w s t u band a b raw (embStk weightCacheCoreReg (embStk plan.solver S))) :
    RetainedCouplingReady precision q w s t u band a b raw
      (embStk weightCacheCoreReg (embStk plan.solver (replicaResidualState placement dst fieldTail rhsTail words S))) := by
  rw [replicaResidualState_native placement dst hdst]
  apply h.of_frame (S' := {embStk weightCacheCoreReg (embStk plan.solver S) with
    R := Function.update (embStk weightCacheCoreReg (embStk plan.solver S)).R 93 rhsTail}) rfl
  intro k h93 _ _
  exact Function.update_of_ne h93 _ _

noncomputable def replicaCouplingResidual {plan : ReplicaInteriorPlacement T}
    (placement : ReplicaCouplingPlacement plan) (volume dst saved tmp : Fin T)
    (hQ : SS.states ≤ Q) (boundary : Bool) : Pr P T Q A U :=
  .seq (replicaLocalCoupling placement hQ boundary)
    (finishReplicaCouplingRow volume (placement.bank 132) (placement.bank 110) dst saved tmp)

theorem replicaCouplingResidual_exec {plan : ReplicaInteriorPlacement T}
    (placement : ReplicaCouplingPlacement plan) (volume dst saved tmp : Fin T) (hQ : SS.states ≤ Q) {precision q w s t u band a b origin N : ℕ} [NeZero s]
    (boundary : Bool) (hA : 96 ≤ A) (hw5 : 5 ≤ w) (hqw : q+4 ≤ w)
    (hst : s < t)
    (C B : ZMod s → GaussianInt)
    (hfit : origin+N ≤ s)
    (tail pageTail rhsTail raw : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hready : RetainedCouplingReady precision q w s t u band a b raw (embStk weightCacheCoreReg (embStk plan.solver S)))
    (hlocalOrigin : origin = a) (hlocalEnd : b = a+N) (hsep : N+band ≤ s)
    (hsource : S.R (placement.bank 132) = cstream A w (packedInterval a N C)++tail) (h127 : S.R (placement.bank 127) = [])
    (hrows : (S.R (placement.bank 140)).length = 2*band+1)
    (hpage : S.R (placement.bank 138) = cstream A w (couplingCoefficientPageInterval precision q s t u band a b origin N)++pageTail)
    (hrhs : S.R (placement.bank 93) = cstream A w (packedInterval origin N B)++rhsTail)
    (h143 : S.R (placement.bank 143) = [])
    (hCfits : ∀ j, Fits w (C j))
    (has : ∀ j < N, ∀ z ∈ couplingCoefficientWords precision q s t u band (origin+j), Fits w z ∧ z.im = 0)
    (V : ℕ) (h166 : S.R (placement.bank 166) = [])
    (h139 : (S.R (placement.bank 139)).length = (couplingCoefficientPageInterval precision q s t u band a b origin N).length)
    (haS : a ≤ s) (hbS : b ≤ s) (hbandS : band ≤ s)
    (hwide : 8*(t+1)^2+4*band+8 < 2^V)
    (hfitV : origin+(N+2*band)+s < 2^V)
    (hgeometry : CouplingIntervalMetadata V s t band a b origin N (embStk placement.bank S))
    (h158 : S.R (placement.bank 158) = []) (h135 : S.R (placement.bank 135) = []) (h167 : S.R (placement.bank 167) = [])
    (hreg : [volume,placement.bank 132,placement.bank 110,dst,saved,tmp,placement.bank 93].Nodup)
    (hvolume : (S.R volume).length = N*w) (hsaved : S.R saved = []) (htmp : S.R tmp = []) :
    ∃ v' m, v'.user = v.user ∧
      m ≤ replicaLocalCouplingCost boundary precision q w s t u band a b origin N V+finishReplicaCouplingRowCost (N*w) ∧
      Exec body (replicaCouplingResidual placement volume dst saved tmp hQ boundary) (mk v S) m
        (mk v' (replicaResidualState placement dst tail rhsTail
          (cstream A w (packedInterval origin N (guardedCouplingRowField precision q t u band a b boundary C B))) S)) := by
  have hr := hreg
  regs_ne hr
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := replicaLocalCoupling_exec (body := body) placement hQ boundary
    hA hw5 hqw hst C B hfit tail pageTail rhsTail raw v S hready hlocalOrigin hlocalEnd hsep
    hsource h127 hrows hpage hrhs h143 hCfits has V h166 h139 haS hbS hbandS hwide hfitV hgeometry h158 h135 h167
  let ys := cstream A w (packedInterval origin N (guardedCouplingRowField precision q t u band a b boundary C B))
  let J : Stacks T A := {S with R := Function.update (Function.update S.R (placement.bank 93) rhsTail) (placement.bank 110) (ys++S.R (placement.bank 110))}
  have hys : ys.length = N*w := by simp [ys,packedInterval_length _ hfit]
  have hfieldLen : (cstream A w (packedInterval a N C)).length = N*w := by
    rw [← hlocalOrigin]
    simp [packedInterval_length _ hfit]
  obtain ⟨v₂,hu₂,he₂⟩ := finishReplicaCouplingRow_exec_within (body := body) volume (placement.bank 132)
    (placement.bank 110) dst saved tmp (by regs_nodup) (N*w)
    (cstream A w (packedInterval a N C)) ys tail (S.R (placement.bank 110)) hfieldLen hys v₁ J
    (by simpa [J,‹volume ≠ placement.bank 110›,‹volume ≠ placement.bank 93›] using hvolume)
    (by simpa [J,‹placement.bank 132 ≠ placement.bank 110›,‹placement.bank 132 ≠ placement.bank 93›] using hsource)
    (by simp [J])
    (by simpa [J,‹placement.bank 110 ≠ saved›.symm,‹saved ≠ placement.bank 93›] using hsaved)
    (by simpa [J,‹placement.bank 110 ≠ tmp›.symm,‹tmp ≠ placement.bank 93›] using htmp) 0
  refine ⟨v₂,n₁+finishReplicaCouplingRowCost (N*w),hu₂.trans hu₁,by omega,(Exec.seq he₁ he₂.toExec).cast rfl ?_⟩
  apply congrArg (mk v₂)
  dsimp only [replicaResidualState]
  refine Stacks.ext rfl rfl rfl ?_
  funext k
  by_cases hfield : k = placement.bank 132
  · subst k
    simp [J,‹placement.bank 132 ≠ dst›,‹placement.bank 132 ≠ placement.bank 110›,‹placement.bank 132 ≠ placement.bank 93›]
  by_cases hrhs : k = placement.bank 93
  · subst k
    simp [J,ys,‹dst ≠ placement.bank 93›.symm,‹placement.bank 110 ≠ placement.bank 93›.symm,
      ‹placement.bank 132 ≠ placement.bank 93›.symm]
  by_cases hdst : k = dst
  · subst k
    simp [J,ys,‹placement.bank 110 ≠ dst›.symm,‹dst ≠ placement.bank 93›]
  by_cases hresidual : k = placement.bank 110
  · subst k
    simp [J,‹placement.bank 110 ≠ dst›,‹placement.bank 110 ≠ placement.bank 93›,
      ‹placement.bank 132 ≠ placement.bank 110›.symm]
  simp [J,hfield,hrhs,hdst,hresidual]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
