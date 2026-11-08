module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellResidentCyclicBoundaryOrder
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCountWords

/-! Count the joint boundary directly from its generated original-coordinate page. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 154 Q A U}

def countedCyclicBoundaryOrder : Pr P 154 Q A U :=
  .seq residentCyclicBoundaryOrder (countWords 115 109 116 106 108)

theorem countedCyclicBoundaryOrder_exec {V s t band a n : ℕ} [NeZero s]
    (hst : s < t) (ha : a < s) (hn : n ≤ s) (hband : band ≤ s) (hVpos : 0 < V)
    (hwide : 8*(t+1)^2+2*band+8 < 2^V)
    (v : HS 154 Q A U) (S : Stacks 154 A)
    (hsSrc : (S.R 121).length = s) (htSrc : (S.R 122).length = t) (hbandSrc : (S.R 124).length = band)
    (haSrc : (S.R 144).length = a) (hleftEnd : (S.R 145).length = a+min n (s-a))
    (hrightEnd : (S.R 146).length = n-min n (s-a)) (h138 : S.R 138 = [])
    (hwidth : (S.R 115).length = V) (h106 : S.R 106 = []) (h108 : S.R 108 = [])
    (h109 : S.R 109 = []) (h116 : S.R 116 = [])
    (hlow : ∀ k : Fin 154, k.val < 31 → S.R k = []) :
    let N := (cyclicPrincipalBoundary s t band a n).card
    ∃ v' m, v'.user = v.user ∧ m ≤ residentCyclicBoundaryOrderCost V s t band a n+N*(6*V+6)+4 ∧
      Exec body countedCyclicBoundaryOrder (mk v S) m
        (mk v' {S with R := (Function.update (Function.update S.R 109
          (cstream A V (cyclicBoundaryIndexWords s t band a n))) 116 (List.replicate N tick))}) := by
  dsimp only
  let xs := cyclicBoundaryIndexWords s t band a n
  let N := (cyclicPrincipalBoundary s t band a n).card
  obtain ⟨v₁,m₁,hv₁,hm₁,he₁⟩ := residentCyclicBoundaryOrder_exec (body := body) hst ha hn hband hwide
    v S hsSrc htSrc hbandSrc haSrc hleftEnd hrightEnd h138 hwidth h106 h108 hlow
  let F : Stacks 154 A := {S with R := Function.update S.R 109 (cstream A V xs)}
  have he₁' : Exec body residentCyclicBoundaryOrder (mk v S) m₁ (mk v₁ F) := by simpa [F,xs,h109] using he₁
  let words := xs.map (csyms A V)
  have hflat : words.flatten = cstream A V xs := by
    simp only [words,← List.flatMap_def,cstream]
  have hlen : words.length = N := by
    simpa only [words,List.length_map,xs,N] using cyclicBoundaryIndexWords_length hst band a n ha hn
  obtain ⟨v₂,hv₂,he₂⟩ := countWords_exec (body := body)
    (width := 115) (src := 109) (dst := 116) (saved := 106) (tmp := 108) (by decide)
    V hVpos words (by intro ys hy; obtain ⟨z,_,rfl⟩ := List.mem_map.mp hy; simp)
    v₁ F (by simpa [F] using hwidth) (by simpa [F] using hflat.symm)
    (by simpa [F] using h106) (by simpa [F] using h108)
  refine ⟨v₂,m₁+(N*(6*V+6)+4),hv₂.trans hv₁,
    (by change m₁+(N*(6*V+6)+4) ≤ residentCyclicBoundaryOrderCost V s t band a n+N*(6*V+6)+4; omega),
    (Exec.seq he₁' he₂).cast (by rw [hlen]) ?_⟩
  apply congrArg (mk v₂)
  simp [F,hlen,h116,xs,N]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
