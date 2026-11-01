module

public import IntegerMultBounds.MathlibTM2.Host.ReplayCache
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellMaskGatheredCouplingRibbon
public import IntegerMultBounds.MathlibTM2.Host.ClosedProgramStock
public import IntegerMultBounds.MathlibTM2.StackStockComposition

/-! Replay a shared ribbon mask instead of recomputing geometry for each replica. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 168 Q A U}

def cachedGatheredRibbon (cache : Fin 168) : Pr P 168 Q A U :=
  .seq (replayCache cache 158 0 1) maskGatheredCouplingRibbon

def cachedGatheredRibbonCost (N w : ℕ) := 6*N+6+maskCouplingSourceCost N w

theorem cachedGatheredRibbon_exec_within (cache : Fin 168)
    (hreg : [cache,158,0,1].Nodup) (hcache : cache ≠ 141)
    (hA : 4 ≤ A) (flags : List Bool) (xs : List GaussianInt)
    (w : ℕ) (hlen : xs.length = flags.length) (tail : List (Fin (A+4)))
    (v : HS 168 Q A U) (S : Stacks 168 A)
    (hc : S.R cache = flags.map (fun flag => pairSym A flag flag))
    (hs : (S.R 166).length = flags.length) (hw : (S.R 94).length = w)
    (hsrc : S.R 160 = cstream A w xs++tail)
    (h0 : S.R 0 = []) (h1 : S.R 1 = []) (h158 : S.R 158 = [])
    (h108 : S.R 108 = []) (h104 : S.R 104 = []) (h105 : S.R 105 = [])
    (h135 : S.R 135 = []) (h167 : S.R 167 = []) (h143 : S.R 143 = []) :
    let c := mnProgPush (maskCouplingSource (P := Empty) (Q := Q) (A := A) (U := U))
    ∃ v' m, v'.user = v.user ∧ m ≤ cachedGatheredRibbonCost flags.length w ∧
      (∀ depth, ExecWithin body
        (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
          (2*(6*flags.length+6)+c*maskCouplingSourceCost flags.length w))
        depth (cachedGatheredRibbon cache) (mk v S) m
        (mk v' {S with R := Function.update S.R 141 (cstream A w (maskedLine flags xs)++S.R 141)})) ∧
      ({S with R := Function.update S.R 141 (cstream A w (maskedLine flags xs)++S.R 141)} : Stacks 168 A).R cache = S.R cache := by
  dsimp only
  obtain ⟨v₁,hu₁,he₁⟩ := replayCache_exec_within (body := body) cache 158 0 1 hreg v S h0 h1
  let B : Stacks 168 A := {S with R := Function.update S.R 158 (flags.map (fun flag => pairSym A flag flag))}
  have hcopy (depth : ℕ) : ExecWithin body
      (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+2*(6*flags.length+6)) depth
      (replayCache cache 158 0 1) (mk v S) (6*flags.length+6) (mk v₁ B) := by
    simpa only [hc,List.length_map,h158,List.append_nil] using he₁ depth
  obtain ⟨v₂,m,hu₂,hm,he₂⟩ := maskGatheredCouplingRibbon_exec (body := body) hA flags xs w hlen tail v₁ B
    (by simpa [B] using hs) (by simpa [B] using hw) (by simpa [B] using hsrc) (by simp [B])
    (by simpa [B] using h108) (by simpa [B] using h104) (by simpa [B] using h105)
    (by simpa [B] using h135) (by simpa [B] using h167) (by simpa [B] using h143)
  have hfinal : {B with R := Function.update (Function.update B.R 158 []) 141 (cstream A w (maskedLine flags xs)++B.R 141)} =
      {S with R := Function.update S.R 141 (cstream A w (maskedLine flags xs)++S.R 141)} := by
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases h158k : k = 158 <;> by_cases h141k : k = 141 <;> simp_all [B]
  refine ⟨v₂,6*flags.length+6+m,hu₂.trans hu₁,Nat.add_le_add_left hm _,?_,?_⟩
  · intro depth
    have ht₂ := mn_native_exec_within he₂ _
      (embProg_native ribbonMaskReg Empty.elim _ (WordCmd.empty_native _)) depth
      (mnSize (mk v₁ B)+depth+
        mnProgPush (maskCouplingSource (P := Empty) (Q := Q) (A := A) (U := U))*maskCouplingSourceCost flags.length w)
      (Nat.add_le_add_left (Nat.mul_le_mul_left _ hm) _)
    exact (mn_seq_within_add (hcopy depth) ht₂).cast rfl (congrArg (mk v₂) hfinal)
  · simp only [Function.update_of_ne hcache]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
