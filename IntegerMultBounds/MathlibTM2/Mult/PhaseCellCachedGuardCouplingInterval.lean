module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCountedRestoredCouplingIntervalStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedRestoredCouplingInterval
public import IntegerMultBounds.MathlibTM2.Host.ReplayCache
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedBinaryRecoveryGuardInterval
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRestoreIntervalCouplingPass
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedFinishCouplingCoefficientInterval

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Fast.TableVM
variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 168 Q A U}

noncomputable def cachedGuardCouplingInterval (hQ : SS.states ≤ Q) (cache : Fin 168) : Pr P₀ 168 Q A U :=
  .seq (replayCache cache 136 0 1) (countedRestoredCouplingInterval hQ)

theorem cachedGuardCouplingInterval_exec_within (hQ : SS.states ≤ Q) (cache : Fin 168)
    (hreg : [cache,136,0,1].Nodup) {P q w s t u band a b origin : ℕ} [NeZero s]
    (boundary : Bool) (hA : 96 ≤ A) (hw5 : 5 ≤ w) (hqw : q+4 ≤ w)
    (hst : s < t)
    (C : ZMod s → GaussianInt) (source rhs : List GaussianInt)
    (hlen : rhs.length ≤ source.length)
    (hwindow : ∀ j < rhs.length, (source.drop j).take (2*band+1) = spatialCouplingInputWords boundary t band a b (origin+j) C) (hfit : origin+rhs.length ≤ s)
    (tail pageTail rhsTail raw : List (Fin (A+4)))
    (K : ℕ) (hpush : mnProgPush (rmulOne (P := Empty) (Q := Q) (A := A) (U := U)
      mul mul_injective (by decide) hQ cr) ≤ K) (v : HS 168 Q A U) (S : Stacks 168 A)
    (hready : RetainedCouplingReady P q w s t u band a b raw (embStk groupReg (embStk intervalPageReg S)))
    (hsource : S.R 141 = cstream A w source++tail)
    (hrows : (S.R 140).length = 2*band+1)
    (hpage : S.R 138 = cstream A w (couplingCoefficientPageInterval P q s t u band a b origin rhs.length)++pageTail)
    (hrhs : S.R 93 = cstream A w rhs++rhsTail)
    (h143 : S.R 143 = [])
    (hxs : ∀ j < rhs.length, ∀ x ∈ couplingInputWords boundary t band a b (origin+j) C, Fits w x)
    (has : ∀ j < rhs.length, ∀ z ∈ couplingCoefficientWords P q s t u band (origin+j), Fits w z ∧ z.im = 0)
    (V : ℕ) (hNV : rhs.length < 2^V) (h165 : S.R 165 = binSyms V rhs.length) (h166 : S.R 166 = [])
    (h139 : (S.R 139).length = (couplingCoefficientPageInterval P q s t u band a b origin rhs.length).length)
    (hmaskCache : S.R cache = recoveryGuardIntervalSymbols true A s t (2*band) a b origin rhs.length) :
    ∃ v' m, v'.user = v.user ∧
      m ≤ (6*rhs.length+6)+(6*rhs.length+11*V+6+(retainedPageSpatialIntervalLoopCost boundary q w s t band a b origin rhs.length+
        (22*rhs.length+22*V+22+transferCountedLineCost rhs.length w+
          transferCountedLineCost (couplingCoefficientPageInterval P q s t u band a b origin rhs.length).length w))) ∧
      ∀ depth, ExecWithin body
        (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
          (2*(6*rhs.length+6)+(3*(6*rhs.length+11*V+6)+((realWeightWorkspace K w (2*band+1)+13000*(band+1)*(w+1))+3*(22*rhs.length+22*V+22+transferCountedLineCost rhs.length w+transferCountedLineCost (couplingCoefficientPageInterval P q s t u band a b origin rhs.length).length w)))))
        depth (cachedGuardCouplingInterval hQ cache) (mk v S) m
        (mk v' {S with R := (Function.update (Function.update S.R 93 rhsTail) 113
          (cstream A w (guardedCouplingRowWords P q t u band a b boundary C origin rhs).reverse++S.R 113))}) := by
  have h0 : S.R 0 = [] := hready.low 0 (by decide)
  have h1 : S.R 1 = [] := hready.low 1 (by decide)
  obtain ⟨v₁,hu₁,he₁⟩ := replayCache_exec_within (body := body) cache 136 0 1 hreg v S h0 h1
  let G : Stacks 168 A := {S with R := (Function.update S.R 136
    (recoveryGuardIntervalSymbols true A s t (2*band) a b origin rhs.length++S.R 136))}
  have hcopy (depth : ℕ) : ExecWithin body
      (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+2*(6*rhs.length+6)) depth
      (replayCache cache 136 0 1) (mk v S) (6*rhs.length+6) (mk v₁ G) := by
    simpa only [hmaskCache,recoveryGuardIntervalSymbols_length] using he₁ depth
  have hreadyG : RetainedCouplingReady P q w s t u band a b raw
      (embStk groupReg (embStk intervalPageReg G)) := by
    rw [show embStk groupReg (embStk intervalPageReg G) = embStk groupReg (embStk intervalPageReg S)
      from intervalPageCore_updateR S 136 (by decide) _]
    exact hready
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := countedRestoredCouplingInterval_exec_within (body := body)
    hQ boundary hA hw5 hqw hst C source rhs hlen hwindow hfit tail pageTail (S.R 136) rhsTail raw K hpush v₁ G hreadyG
    (by simpa [G] using hsource) (by simpa [G] using hrows) (by simpa [G] using hpage)
    (by change recoveryGuardIntervalSymbols true A s t (2*band) a b origin rhs.length++S.R 136 = _
        rw [recoveryGuardIntervalSymbols_coupling _ _ _ _ _ _ _ _ hfit]; rfl)
    (by simpa [G] using hrhs) (by simpa [G] using h143)
    hxs has V hNV (by simpa [G] using h165) (by simpa [G] using h166) (by simpa [G] using h139)
  refine ⟨v₂,(6*rhs.length+6)+m₂,hu₂.trans hu₁,Nat.add_le_add_left hm₂ _,?_⟩
  intro depth
  refine (mn_seq_within_add (a := 2*(6*rhs.length+6))
    (b := 3*(6*rhs.length+11*V+6)+((realWeightWorkspace K w (2*band+1)+13000*(band+1)*(w+1))+3*(22*rhs.length+22*V+22+transferCountedLineCost rhs.length w+transferCountedLineCost (couplingCoefficientPageInterval P q s t u band a b origin rhs.length).length w))) (hcopy depth) (he₂ depth)).cast rfl ?_
  apply congrArg (mk v₂)
  refine Stacks.ext rfl rfl rfl ?_
  funext r
  by_cases h1 : r = 136 <;> by_cases h2 : r = 93 <;> by_cases h3 : r = 113 <;>
    by_cases h4 : r = 143 <;> simp [G,h1,h2,h3,h4,h143]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
