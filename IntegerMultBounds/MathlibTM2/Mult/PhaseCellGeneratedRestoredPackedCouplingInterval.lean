module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedRestoredCouplingInterval
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedSpatialCouplingInputs
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGuardedPackedCouplingRow
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedBinaryRecoveryGuardInterval
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRestoreIntervalCouplingPass
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedFinishCouplingCoefficientInterval

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Fast.TableVM
variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 168 Q A U}

theorem generatedRestoredPackedCouplingInterval_exec (hQ : SS.states ≤ Q) {P q w s t u band a b origin N : ℕ} [NeZero s]
    (boundary : Bool) (hA : 96 ≤ A) (hw5 : 5 ≤ w) (hqw : q+4 ≤ w)
    (hst : s < t)
    (C B : ZMod s → GaussianInt)
    (hfit : origin+N ≤ s)
    (tail pageTail rhsTail raw : List (Fin (A+4))) (v : HS 168 Q A U) (S : Stacks 168 A)
    (hready : RetainedCouplingReady P q w s t u band a b raw (embStk groupReg (embStk intervalPageReg S)))
    (hsource : S.R 141 = cstream A w (couplingSourceInterval boundary t band a b origin N C)++tail)
    (hrows : (S.R 140).length = 2*band+1)
    (hpage : S.R 138 = cstream A w (couplingCoefficientPageInterval P q s t u band a b origin N)++pageTail)
    (hrhs : S.R 93 = cstream A w (packedInterval origin N B)++rhsTail)
    (h143 : S.R 143 = [])
    (hxs : ∀ j < N, ∀ x ∈ couplingInputWords boundary t band a b (origin+j) C, Fits w x)
    (has : ∀ j < N, ∀ z ∈ couplingCoefficientWords P q s t u band (origin+j), Fits w z ∧ z.im = 0)
    (V : ℕ) (hNV : N < 2^V) (h165 : S.R 165 = binSyms V N) (h166 : S.R 166 = [])
    (h139 : (S.R 139).length = (couplingCoefficientPageInterval P q s t u band a b origin N).length)
    (value : Fin 117 → ℕ) (hvs : value 97 = s) (hvt : value 98 = t)
    (hvb : value 100 = 2*band) (hva : value 101 = a) (hvu : value 103 = b)
    (hvi : value 107 = origin) (hvc : value 108 = origin+N)
    (haS : a ≤ s) (hbS : b ≤ s) (hwide : 8*(t+1)^2+4*band+8 < 2^V)
    (hbound : ∀ i, value (intervalGuardBankSource i) < 2^V)
    (hV : ((embStk intervalGuardPlacement S).R 115).length = V)
    (hmeta : ∀ i, (embStk intervalGuardPlacement S).R (intervalGuardBankSource i) =
      binSyms V (value (intervalGuardBankSource i))) :
    ∃ v' m, v'.user = v.user ∧
      m ≤ 144*V+145+((46*N+2)*tblC V 1+66*V+2*N+70)+(6*N+11*V+6+(retainedPageSpatialIntervalLoopCost boundary q w s t band a b origin N+
        (22*N+22*V+22+transferCountedLineCost N w+
          transferCountedLineCost (couplingCoefficientPageInterval P q s t u band a b origin N).length w))) ∧
      Exec body (generatedRestoredCouplingInterval hQ boundary) (mk v S) m
        (mk v' {S with R := (Function.update (Function.update S.R 93 rhsTail) 113
          (cstream A w (packedInterval origin N (guardedCouplingRowField P q t u band a b boundary C B)).reverse++S.R 113))}) := by
  have hlen : (packedInterval origin N B).length ≤ (couplingSourceInterval boundary t band a b origin N C).length := by
    rw [packedInterval_length B hfit,couplingSourceInterval_length _ _ _ _ _ _ _ _ hfit]
    omega
  have he := generatedRestoredCouplingInterval_exec (body := body) hQ boundary hA hw5 hqw hst C
    (couplingSourceInterval boundary t band a b origin N C) (packedInterval origin N B) hlen
    (by intro j hj
        exact couplingSourceInterval_window boundary t band a b origin N j C hfit
          (by simpa only [packedInterval_length B hfit] using hj))
    (by simpa only [packedInterval_length B hfit] using hfit)
    tail pageTail rhsTail raw v S hready hsource hrows
    (by simpa only [packedInterval_length B hfit] using hpage) hrhs h143
    (by simpa only [packedInterval_length B hfit] using hxs)
    (by simpa only [packedInterval_length B hfit] using has) V
    (by simpa only [packedInterval_length B hfit] using hNV)
    (by simpa only [packedInterval_length B hfit] using h165) h166
    (by simpa only [packedInterval_length B hfit] using h139)
    value hvs hvt hvb hva hvu hvi (by simpa only [packedInterval_length B hfit] using hvc)
    haS hbS hwide hbound hV hmeta
  simpa only [packedInterval_length B hfit,guardedCouplingRowWords_packed _ _ _ _ _ _ _ _ _ _ _ _ hfit] using he

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
