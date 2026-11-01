module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaCouplingPlacement
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCachedReplicaLocalCoupling
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaCouplingResidual
public import IntegerMultBounds.MathlibTM2.Host.EmbedUpdate

/-! Archive a cached coupling result using the generic residual finishing rule.
The row restores its retained masks, coefficient page and borrowed queue suffixes. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

noncomputable def cachedReplicaCouplingResidual {plan : ReplicaInteriorPlacement T}
    (placement : ReplicaCouplingPlacement plan) (volume dst saved tmp : Fin T) (hQ : SS.states ≤ Q) : Pr P T Q A U :=
  .seq (cachedReplicaLocalCoupling placement hQ)
    (finishReplicaCouplingRow volume (placement.bank 132) (placement.bank 110) dst saved tmp)

theorem cachedReplicaCouplingResidual_exec {plan : ReplicaInteriorPlacement T}
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
    (hbS : b ≤ s) (hbandS : band ≤ s) (hNV : N < 2^V)
    (hgeometry : CouplingIntervalMetadata V s t band a b origin N (embStk placement.bank S))
    (h159 : S.R (placement.bank 159) = (couplingRibbonFlags (s := s) boundary t band a b origin N).map
      (fun flag => pairSym A flag flag))
    (h161 : S.R (placement.bank 161) = recoveryGuardIntervalSymbols true A s t (2*band) a b origin N)
    (h158 : S.R (placement.bank 158) = []) (h135 : S.R (placement.bank 135) = []) (h167 : S.R (placement.bank 167) = [])
    (hreg : [volume,placement.bank 132,placement.bank 110,dst,saved,tmp,placement.bank 93].Nodup)
    (hvolume : (S.R volume).length = N*w) (hsaved : S.R saved = []) (htmp : S.R tmp = []) :
    ∃ v' m, v'.user = v.user ∧
      m ≤ cachedReplicaLocalCouplingCost boundary precision q w s t u band a b origin N V+finishReplicaCouplingRowCost (N*w) ∧
      Exec body (cachedReplicaCouplingResidual placement volume dst saved tmp hQ) (mk v S) m
        (mk v' (replicaResidualState placement dst tail rhsTail
          (cstream A w (packedInterval origin N (guardedCouplingRowField precision q t u band a b boundary C B))) S)) := by
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := cachedReplicaLocalCoupling_exec (body := body) placement hQ boundary
    hA hw5 hqw hst C B hfit tail pageTail rhsTail raw v S hready hlocalOrigin hlocalEnd hsep
    hsource h127 hrows hpage hrhs h143 hCfits has V h166 h139 hbS hbandS hNV hgeometry h159 h161 h158 h135 h167
  let ys := cstream A w (packedInterval origin N (guardedCouplingRowField precision q t u band a b boundary C B))
  have hys : ys.length = N*w := by simp [ys,packedInterval_length _ hfit]
  have hfieldLen : (cstream A w (packedInterval a N C)).length = N*w := by
    rw [←hlocalOrigin]
    simp [packedInterval_length _ hfit]
  exact replicaCouplingResidual_finish placement (cachedReplicaLocalCoupling placement hQ)
    volume dst saved tmp (N*w) (cstream A w (packedInterval a N C)) ys tail rhsTail hfieldLen hys
    v v₁ S n₁ (cachedReplicaLocalCouplingCost boundary precision q w s t u band a b origin N V)
    hu₁ hn₁ he₁ hreg hvolume hsource hsaved htmp

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
