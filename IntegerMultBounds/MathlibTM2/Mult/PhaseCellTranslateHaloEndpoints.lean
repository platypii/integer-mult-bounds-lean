module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellTranslateBinaryWords

/-! Four endpoint words share one displacement on the generated-core ABI.
The new origin at 155 is installed separately by the ordered-header step. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 272 Q A U}

def translateHaloEndpoints : Pr P 272 Q A U :=
  translateBinaryWords 104 269 270 271 106 [149,151,156,164]

def translatedHaloEndpoints (V y L band : ℕ) (S : Stacks 272 A) : Stacks 272 A :=
  writeRight [(149,binSyms V y),(151,binSyms V (y+L)),
    (156,binSyms V (y+L)),(164,binSyms V (y+(L+2*band)))] S

theorem translateHaloEndpoints_exec {V x y L band : ℕ} (hxy : x ≤ y)
    (hfit : y+(L+2*band) < 2^V) (v : HS 272 Q A U) (S : Stacks 272 A)
    (h149 : S.R 149 = binSyms V x) (h151 : S.R 151 = binSyms V (x+L))
    (h156 : S.R 156 = binSyms V (x+L)) (h164 : S.R 164 = binSyms V (x+(L+2*band)))
    (hdelta : S.R 104 = binSyms V (y-x))
    (hfresh : ∀ k ∈ ([269,270,271] : List (Fin 272)), S.R k = []) :
    ∃ v', v'.user = v.user ∧
      Exec body translateHaloEndpoints (mk v S) (32*V+33)
        (mk v' (translatedHaloEndpoints V y L band S)) := by
  let words : List (Fin 272 × ℕ) := [(149,x),(151,x+L),(156,x+L),(164,x+(L+2*band))]
  have hreg : ∀ k ∈ words.map Prod.fst,
      [k,104,269,270,271,106].Nodup := by
    intro k hk
    simp only [words,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl <;> decide
  obtain ⟨v',hu,he⟩ := translateBinaryWords_exec (body := body)
    (delta := 104) (work := 269) (saved := 270) (tmp := 271) (carry := 106)
    words (by change ([149,151,156,164] : List (Fin 272)).Nodup; decide) hreg (by omega : y-x < 2^V)
    (by
      intro w hw
      simp only [words,List.mem_cons,List.not_mem_nil,or_false] at hw
      rcases hw with rfl | rfl | rfl | rfl <;> dsimp <;> omega)
    v S (by
      intro w hw
      simp only [words,List.mem_cons,List.not_mem_nil,or_false] at hw
      rcases hw with rfl | rfl | rfl | rfl
      · exact h149
      · exact h151
      · exact h156
      · exact h164)
    hdelta (hfresh 269 (by decide)) (hfresh 270 (by decide)) (hfresh 271 (by decide))
  refine ⟨v',hu,?_⟩
  have h0 : x+(y-x) = y := by omega
  have h1 : (x+L)+(y-x) = y+L := by omega
  have h2 : (x+(L+2*band))+(y-x) = y+(L+2*band) := by omega
  have hcost : words.length*(8*V+8)+1 = 32*V+33 := by
    change 4*(8*V+8)+1 = 32*V+33
    omega
  simpa only [words,List.map_cons,List.map_nil,
    translateHaloEndpoints,translatedHaloEndpoints,h0,h1,h2] using he.cast hcost rfl

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
