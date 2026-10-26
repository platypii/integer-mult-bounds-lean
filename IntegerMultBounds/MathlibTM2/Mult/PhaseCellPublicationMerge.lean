module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPublicationField

/-! Consume aligned interior and boundary lines, selecting and real-projecting each word. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 144 Q A U}

def publicationMerge : Pr P₀ 144 Q A U :=
  .seq (publicationSelectLoop 143 94 109 137 132 140 134 135)
    (moveR 140 132 realPartSymbol)

def publicationMergeCost (s w : ℕ) : ℕ := s*(12*w+15)+4

theorem publicationMerge_exec {s t band a b w : ℕ} [NeZero s]
    (hA : 4 ≤ A) (hst : s < t) (hbs : b ≤ s)
    (D C : ZMod s → GaussianInt) (tail : List (Fin (A+4)))
    (v : HS 144 Q A U) (S : Stacks 144 A)
    (hcount : (S.R 143).length = s) (hwidth : (S.R 94).length = w)
    (hmask : S.R 109 = publicationMaskSymbols A s t band a b)
    (hD : S.R 137 = cstream A w (chirpLine s D))
    (hC : S.R 132 = cstream A w (chirpLine s C)++tail)
    (h140 : S.R 140 = []) (h134 : S.R 134 = []) (h135 : S.R 135 = []) :
    let G := fun i => realPartWord (publicationField t band a b D C i)
    ∃ v' n, v'.user = v.user ∧ n ≤ publicationMergeCost s w ∧
      Exec body publicationMerge (mk v S) n
        (mk v' {S with R := (Function.update (Function.update (Function.update (Function.update
          S.R 109 []) 137 []) 143 []) 132 (cstream A w (chirpLine s G)++tail))}) := by
  dsimp only
  let flags := publicationFlags s t band a b
  let xs := (chirpLine s D).map (csyms A w)
  let ys := (chirpLine s C).map (csyms A w)
  let G := publicationField t band a b D C
  let words := cstream A w (chirpLine s G)
  have hlenX : xs.length = flags.length := by simp [xs,flags]
  have hlenY : ys.length = flags.length := by simp [ys,flags]
  have hwords : (publicationWords flags xs ys).flatten = words := by
    rw [publicationWords_chirpLine hst hbs]
    simp [words,G,cstream,List.flatMap_def]
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := publicationSelectLoop_exec (body := body)
    (count := 143) (width := 94) (mask := 109) (x := 137) (y := 132)
    (dst := 140) (trash := 134) (tmp := 135) (by decide) hA flags xs ys w hlenX hlenY
    (by intro z hz; obtain ⟨x,_,rfl⟩ := List.mem_map.mp hz; simp)
    (by intro z hz; obtain ⟨x,_,rfl⟩ := List.mem_map.mp hz; simp)
    [] tail v S (by simpa [flags] using hcount) hwidth
    (by simpa [flags,publicationMaskSymbols_eq_flags] using hmask)
    (by simpa [xs,cstream,List.flatMap_def] using hD) (by simpa [ys,cstream,List.flatMap_def] using hC) h134 h135
  let S₁ : Stacks 144 A := {S with R := (Function.update (Function.update (Function.update (Function.update
    (Function.update S.R 109 []) 137 []) 132 tail) 140 words.reverse) 143 [])}
  have he₁' : Exec body (publicationSelectLoop 143 94 109 137 132 140 134 135) (mk v S) n₁ (mk v₁ S₁) := by
    simpa [S₁,hwords,h140] using he₁
  obtain ⟨v₂,hu₂,he₂⟩ := moveR_exec body 140 132 (by decide) realPartSymbol v₁ S₁
  have hlen : words.length = s*w := by simp [words]
  have hreal : (chirpLine s G).map realPartWord = chirpLine s (fun i => realPartWord (G i)) := by
    simp [chirpLine,List.map_map,Function.comp_def]
  refine ⟨v₂,n₁+(2*(s*w)+2),hu₂.trans hu₁,?_,(Exec.seq he₁' he₂).cast ?_ ?_⟩
  · dsimp only [publicationMergeCost] at *
    simp only [flags,publicationFlags_length] at hn₁
    nlinarith only [hn₁]
  · simp [S₁,hlen]
  · apply congrArg (mk v₂)
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases h109 : k = 109 <;> by_cases h137 : k = 137 <;>
      by_cases h140' : k = 140 <;> by_cases h143 : k = 143 <;> by_cases h132 : k = 132 <;>
      simp [S₁,movedR,h109,h137,h140',h143,h132,h140,words,G,
        realPartSymbol_cstream hA,hreal,List.map_reverse]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
