module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPublishCyclicBandColumn
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCollectRetireCyclicColumnStock
public import IntegerMultBounds.MathlibTM2.Host.OrderedMoveStock

/-! Publish the collected band without allocating an additional output copy. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 151 Q A U}

theorem publishCyclicBandColumn_exec_within {s : ℕ} [NeZero s] (B : Finset (ZMod s)) (q V band a b n : ℕ)
    (cap depth : ℕ)
    (hcost : ∀ j < min B.card (n+(24*band+1)+1)-(n-(24*band+1)),
      cyclicColumnEntryStepCost q V s a b (n-(24*band+1)+j)
        (bFoldAt s B (n-(24*band+1)+j)).val ≤ cap)
    (hA : 4 ≤ A) (hwide : s+s ≤ 2^V) (ha : a ≤ s) (hb : b ≤ s) (hn : n < B.card)
    (C D original : ZMod s → GaussianInt) (pageTail outputTail inputTail : List (Fin (A+4)))
    (v : HS 151 Q A U) (S : Stacks 151 A)
    (hindex : (S.R 0).length = n) (hwidth : (S.R 115).length = V)
    (hband : (S.R 124).length = band) (hrows : (S.R 116).length = B.card)
    (hpage : S.R 109 = cstream A V ((bFoldOrder s B).map
      (fun k : ZMod s => (⟨(k.val : ℤ),0⟩ : GaussianInt)))++pageTail)
    (hq : (S.R 119).length = q) (hs : (S.R 121).length = s)
    (haSrc : (S.R 144).length = a) (hbSrc : (S.R 145).length = b)
    (hsource : S.R 132 = cstream A (2*q+8) (chirpLine s D)++(cstream A (2*q+8) (chirpLine s C)++outputTail))
    (hinput : S.R 110 = cstream A (2*q+8) (chirpLine s original)++inputTail)
    (hfresh : ∀ k ∈ [(94 : Fin 151),106,131,134,135,136,137,138,139,140], S.R k = [])
    (h150 : S.R 150 = [])
    (hblank : ∀ k : Fin 151, k.val < 31 → k ≠ 0 → S.R k = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ collectRetireCyclicColumnCost B q V band a b n+
        (4*((foldedBandRows B (24*band+1) n).length*(2*q+8))+4) ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
        (preparedCyclicBandCollectionWorkspace cap q band B.card n+8*retireCyclicColumnStreamsCost q s))
        depth publishCyclicBandColumn (mk v S) m
        (mk v' {S with R := (Function.update (Function.update (Function.update S.R 0 [])
          110 inputTail) 132
          (cstream A (2*q+8) ((foldedBandRows B (24*band+1) n).reverse.map
            (fun i => if a ≤ i.val ∧ i.val < b then C i else D i))++outputTail))}) := by
  obtain ⟨v₁,m₁,hv₁,hm₁,he₁⟩ := collectRetireCyclicColumn_exec_within (body := body) B q V band a b n cap depth hcost
    hA hwide ha hb hn C D original pageTail outputTail inputTail v S hindex hwidth hband hrows hpage
    hq hs haSrc hbSrc hsource hinput hfresh hblank
  let words := cstream A (2*q+8) ((foldedBandRows B (24*band+1) n).reverse.map
    (fun i => if a ≤ i.val ∧ i.val < b then C i else D i))
  let F : Stacks 151 A := {S with R := (Function.update (Function.update (Function.update (Function.update S.R 0 [])
    110 inputTail) 132 outputTail) 150 (words++S.R 150))}
  obtain ⟨v₂,hv₂,he₂⟩ := moveRightOrdered_exec (body := body) 150 131 132 (by decide) (by decide) (by decide) v₁ F
    (by simpa [F] using hfresh 131 (by simp))
  have ht₂ := moveRightOrdered_within 150 131 132 he₂ depth
    (mnSize (mk v S)+depth+
      (preparedCyclicBandCollectionWorkspace cap q band B.card n+8*retireCyclicColumnStreamsCost q s))
    he₁.final
  have hlen : (F.R 150).length = (foldedBandRows B (24*band+1) n).length*(2*q+8) := by
    simp [F,words,h150]
  refine ⟨v₂,m₁+(4*((foldedBandRows B (24*band+1) n).length*(2*q+8))+4),hv₂.trans hv₁,
    Nat.add_le_add_right hm₁ _,(ExecWithin.seq he₁ ht₂).cast (by rw [hlen]) ?_⟩
  apply congrArg (mk v₂)
  ext1
  · rfl
  · rfl
  · rfl
  · funext k
    by_cases h150' : k = 150
    · subst k; simp [h150]
    by_cases h132 : k = 132 <;> simp [F,words,h150',h150,h132,Function.update_apply]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
