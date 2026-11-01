module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaCouplingPlacement
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCachedLocalFeedCouplingInterval
public import IntegerMultBounds.MathlibTM2.Host.EmbedUpdate

/-! Execute replica-local coupling with shared ribbon and guard caches.
No geometry table is evaluated in the repeated row call; only RHS and result change. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

noncomputable def cachedReplicaLocalCoupling {plan : ReplicaInteriorPlacement T}
    (placement : ReplicaCouplingPlacement plan) (hQ : SS.states ≤ Q) : Pr P T Q A U :=
  embProg placement.bank Empty.elim (cachedLocalFeedCouplingInterval hQ)

def cachedReplicaLocalCouplingCost (boundary : Bool) (precision q w s t u band a b origin N V : ℕ) : ℕ :=
  (((16*N*w+21*N+14*band*w+13*band+11*V+46)+cachedGatheredRibbonCost (N+2*band) w+(12*((N+2*band)*w)+11*(N+2*band)+14)) +
        (12*((N+2*band)*w)+17*N+26*band+11*V+24) +
        ((6*N+6)+(6*N+11*V+6+(retainedPageSpatialIntervalLoopCost boundary q w s t band a b origin N+
        (22*N+22*V+22+transferCountedLineCost N w+
          transferCountedLineCost (couplingCoefficientPageInterval precision q s t u band a b origin N).length w))))) + (28*N*w+36*N+11*V+26)

theorem cachedReplicaLocalCoupling_exec {plan : ReplicaInteriorPlacement T}
    (placement : ReplicaCouplingPlacement plan) (hQ : SS.states ≤ Q) {precision q w s t u band a b origin N : ℕ} [NeZero s]
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
    (hbS : b ≤ s) (hbandS : band ≤ s) (hNV : N < 2^V)
    (hgeometry : CouplingIntervalMetadata V s t band a b origin N (embStk placement.bank S))
    (h159 : S.R (placement.bank 159) = (couplingRibbonFlags (s := s) boundary t band a b origin N).map
      (fun flag => pairSym A flag flag))
    (h161 : S.R (placement.bank 161) = recoveryGuardIntervalSymbols true A s t (2*band) a b origin N)
    (h158 : S.R (placement.bank 158) = []) (h135 : S.R (placement.bank 135) = []) (h167 : S.R (placement.bank 167) = []) :
    ∃ v' m, v'.user = v.user ∧
      m ≤ cachedReplicaLocalCouplingCost boundary precision q w s t u band a b origin N V ∧
      Exec body (cachedReplicaLocalCoupling placement hQ) (mk v S) m
        (mk v' {S with R := (Function.update (Function.update S.R (placement.bank 93) rhsTail) (placement.bank 110)
          (cstream A w (packedInterval origin N (guardedCouplingRowField precision q t u band a b boundary C B))++S.R (placement.bank 110)))}) := by
  let J := embStk placement.bank S
  have hreadyB : RetainedCouplingReady precision q w s t u band a b raw
      (embStk groupReg (embStk intervalPageReg J)) := (placement.native_view S).symm ▸ hready
  have h165 : J.R 165 = binSyms V N := by
    simpa [couplingIntervalValue] using hgeometry.encoded 165 (by simp [couplingIntervalPorts])
  obtain ⟨vi,m,hu,hm,he⟩ := cachedLocalFeedCouplingInterval_exec_within (body := fun f : Empty => nomatch f)
    hQ boundary hA hw5 hqw hst C B hfit tail pageTail rhsTail raw
    (mnProgPush (rmulOne (P := Empty) (Q := Q) (A := A) (U := U) mul mul_injective (by decide) hQ cr))
    (le_refl _) (embDn placement.bank v) J hreadyB hlocalOrigin hlocalEnd hsep hsource h127 hrows hpage
    hrhs h143 hCfits has V hNV h165 h166 h139 hbS hbandS h159 h161 h158 h135 h167
  obtain ⟨v',_,hu',he'⟩ := exec_emb_ovr (ι := Empty.elim) (body' := body)
    placement.bank_injective (fun f : Empty => nomatch f) (he 0).toExec v rfl S rfl
  refine ⟨v',m,hu'.trans hu,hm,he'.cast rfl ?_⟩
  apply congrArg (mk v')
  rw [embOvr_updateR_updateR placement.bank_injective]
  rfl

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
