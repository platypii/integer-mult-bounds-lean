module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedCyclicBandCollection
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetireCyclicColumnStreams

/-! Collect a cyclic band column and release all three owned ambient streams. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 151 Q A U}

def collectRetireCyclicColumn : Pr P 151 Q A U :=
  .seq preparedCyclicBandCollection retireCyclicColumnStreams

noncomputable def collectRetireCyclicColumnCost {s : ℕ} [NeZero s] (B : Finset (ZMod s))
    (q V band a b n : ℕ) : ℕ :=
  preparedCyclicBandCollectionCost B q V band a b n+retireCyclicColumnStreamsCost q s

theorem collectRetireCyclicColumn_exec {s : ℕ} [NeZero s] (B : Finset (ZMod s)) (q V band a b n : ℕ)
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
    (hblank : ∀ k : Fin 151, k.val < 31 → k ≠ 0 → S.R k = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ collectRetireCyclicColumnCost B q V band a b n ∧
      Exec body collectRetireCyclicColumn (mk v S) m
        (mk v' {S with R := (Function.update (Function.update (Function.update (Function.update S.R 0 [])
          110 inputTail) 132 outputTail) 150
          (cstream A (2*q+8) ((foldedBandRows B (24*band+1) n).reverse.map
            (fun i => if a ≤ i.val ∧ i.val < b then C i else D i))++S.R 150))}) := by
  obtain ⟨v₁,m₁,hv₁,hm₁,he₁⟩ := preparedCyclicBandCollection_exec (body := body) B q V band a b n
    hA hwide ha hb hn C D pageTail outputTail v S hindex hwidth hband hrows hpage hq hs haSrc hbSrc hsource
    (by intro k hk; exact hfresh k (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hk ⊢; tauto)) hblank
  let output := cstream A (2*q+8) ((foldedBandRows B (24*band+1) n).reverse.map
    (fun i => if a ≤ i.val ∧ i.val < b then C i else D i))++S.R 150
  let F : Stacks 151 A := {S with R := Function.update (Function.update S.R 0 []) 150 output}
  obtain ⟨v₂,m₂,hv₂,hm₂,he₂⟩ := retireCyclicColumnStreams_exec (body := body) q s
    (cstream A (2*q+8) (chirpLine s D)) (cstream A (2*q+8) (chirpLine s C))
    (cstream A (2*q+8) (chirpLine s original)) outputTail inputTail
    (by simp) (by simp) (by simp) v₁ F (by simpa [F] using hq) (by simpa [F] using hs)
    (by simpa [F] using hsource) (by simpa [F] using hinput)
    (by intro k hk
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl <;> simpa [F] using hfresh _ (by simp))
  refine ⟨v₂,m₁+m₂,hv₂.trans hv₁,Nat.add_le_add hm₁ hm₂,(Exec.seq he₁ he₂).cast rfl ?_⟩
  apply congrArg (mk v₂)
  ext1
  · rfl
  · rfl
  · rfl
  · funext k
    by_cases h0 : k = 0 <;> by_cases h110 : k = 110 <;> by_cases h132 : k = 132 <;> by_cases h150 : k = 150 <;>
      simp [F,output,h0,h110,h132,h150]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
