module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGenerateLiftedCoefficientWidth
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHaloLookupFromHeaders
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHaloLookupWidth
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCouplingIndexFromHeaders

/-! A closed signed-offset masked input query: generate workspace and wrapped
address, test original halo membership, gather, and release every temporary. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellRationalArgs
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def closedCouplingLookup (negative boundary : Bool) : Pr P₀ 117 Q A U :=
  .seq generateLiftedCoefficientWidth (.seq (couplingIndexFromHeaders negative)
    (.seq (haloLookupFromHeaders boundary) (clearWords [108,115])))

def closedCouplingLookupCost (negative : Bool) (P q w s t u band a b i d : ℕ) : ℕ :=
  let V := liftedCoefficientWidth P q w s t u band
  let k := couplingIndex negative s band i d
  generateLiftedCoefficientWidthCost P q w s t u band+
    couplingIndexFromHeadersCost negative V s band i d+
    haloLookupFromHeadersCost V w s t band a b k+(2*(k+V)+5)

theorem closedCouplingLookup_exec {P q w s t u band a b i d : ℕ} [NeZero s]
    (negative boundary : Bool) (hA : 4 ≤ A)
    (hst : s < t) (haS : a ≤ s) (hbS : b ≤ s) (hbandS : band ≤ s) (hi : i < s) (hd : d ≤ band)
    (C : ZMod s → GaussianInt) (tail : List (Fin (A+4)))
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hPsrc : (S.R 114).length = P) (hqsrc : (S.R 112).length = q) (husrc : (S.R 99).length = u)
    (hsSrc : (S.R 97).length = s) (htSrc : (S.R 98).length = t)
    (hbandSrc : (S.R 100).length = band) (hiSrc : (S.R 107).length = i) (hdSrc : (S.R 105).length = d)
    (haSrc : (S.R 101).length = a) (hbSrc : (S.R 103).length = b)
    (hwsrc : (S.R 94).length = w) (h115 : S.R 115 = []) (h104 : S.R 104 = [])
    (h109 : S.R 109 = []) (h106 : S.R 106 = []) (h108 : S.R 108 = [])
    (hblank : ∀ r : Fin 117, r.val < 31 → S.R r = [])
    (hsrc : S.R 92 = cstream A w (chirpLine s C)++tail) :
    let T := if boundary then haloBoundary s t band a b else haloInterior s t band a b
    let j := (i : ZMod s)+(couplingOffset negative d : ZMod s)
    let z := if j ∈ T then C j else 0
    ∃ v' m, v'.user = v.user ∧ m ≤ closedCouplingLookupCost negative P q w s t u band a b i d ∧
      Exec body (closedCouplingLookup negative boundary) (mk v S) m
        (mk v' {S with R := Function.update S.R 110 (csyms A w z++S.R 110)}) := by
  dsimp only
  let V := liftedCoefficientWidth P q w s t u band
  let k := couplingIndex negative s band i d
  have hf := liftedCoefficientWidth_fits negative P q w s t u band i d hi hd
  have hsV : s < 2^V := by have hh := hf.twiceModulus; change 2*s < 2^V at hh; omega
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := generateLiftedCoefficientWidth_exec (body := body)
    P q w s t u band v S hPsrc hqsrc hwsrc hsSrc htSrc husrc hbandSrc h115 h104 (by
      intro r hr
      have hlo : r.val < 31 := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide
      exact hblank r hlo)
  let S₁ : Stacks 117 A := {S with R := Function.update S.R 115 (List.replicate V tick)}
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := couplingIndexFromHeaders_exec (body := body)
    (V := V) (s := s) (band := band) (i := i) (d := d) negative hA (NeZero.pos s) hi hd hsV hf.coordinates v₁ S₁
    (by simpa [S₁] using hsSrc)
    (by simpa [S₁] using hbandSrc)
    (by simpa [S₁] using hiSrc)
    (by simpa [S₁] using hdSrc)
    (by simp [S₁]) (by simpa [S₁] using h106) (by simpa [S₁] using h108) (by
      intro r hr
      have hne : r ≠ 115 := by intro he; subst r; norm_num at hr
      simpa [S₁,hne] using hblank r hr)
  let S₂ : Stacks 117 A := {S₁ with R := Function.update S₁.R 108 (List.replicate k tick)}
  obtain ⟨v₃,n₃,hu₃,hn₃,he₃⟩ := haloLookupFromHeaders_exec (body := body)
    (V := V) (w := w) (s := s) (t := t) (band := band) (a := a) (b := b) (k := k) boundary
    hst haS hbS hbandS (couplingIndex_lt negative (NeZero.pos s)) (haloLookupWidth_fits P q w s t u band)
    C tail v₂ S₂
    (by simpa [S₂,S₁] using hsSrc)
    (by simpa [S₂,S₁] using htSrc)
    (by simpa [S₂,S₁] using hbandSrc)
    (by simp [S₂])
    (by simpa [S₂,S₁] using haSrc)
    (by simpa [S₂,S₁] using hbSrc)
    (by simp [S₂,S₁])
    (by simpa [S₂,S₁] using hwsrc)
    (by simpa [S₂,S₁] using h109)
    (by simpa [S₂,S₁] using h106)
    (by intro r hr
        have h108' : r ≠ 108 := by intro he; subst r; norm_num at hr
        have h115' : r ≠ 115 := by intro he; subst r; norm_num at hr
        simpa [S₂,S₁,h108',h115'] using hblank r hr)
    (by simpa [S₂,S₁] using hsrc)
  let T := if boundary then haloBoundary s t band a b else haloInterior s t band a b
  let j : ZMod s := (i : ZMod s)+(couplingOffset negative d : ZMod s)
  let word := csyms A w (if j ∈ T then C j else 0)
  let S₃ : Stacks 117 A := {S₂ with R := Function.update S₂.R 110 (word++S₂.R 110)}
  have he₃' : Exec body (haloLookupFromHeaders boundary) (mk v₂ S₂) n₃ (mk v₃ S₃) := by
    simpa only [k,word,j,T,couplingIndex_cast negative hd] using he₃
  obtain ⟨v₄,hu₄,he₄⟩ := clearWords_exec (body := body) [(108 : Fin 117),115] (by decide) v₃ S₃
  have he₄' : Exec body (clearWords [108,115]) (mk v₃ S₃) (2*(k+V)+5)
      (mk v₄ {S with R := Function.update S.R 110 (word++S.R 110)}) := by
    convert he₄ using 1
    · simp [S₃,S₂,S₁]
    · apply congrArg (mk v₄)
      refine Stacks.ext ?_ ?_ ?_ ?_
      · rfl
      · rfl
      · rfl
      · funext r
        by_cases h108' : r = 108
        · subst r; simp [h108]
        by_cases h115' : r = 115
        · subst r; simp [h115]
        by_cases h110 : r = 110
        · subst r; simp [S₃,S₂,S₁]
        simp [S₃,S₂,S₁,h108',h115',h110]
  refine ⟨v₄,n₁+(n₂+(n₃+(2*(k+V)+5))),hu₄.trans (hu₃.trans (hu₂.trans hu₁)),?_,
    Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃' he₄'))⟩
  change n₁+(n₂+(n₃+(2*(k+V)+5))) ≤
    generateLiftedCoefficientWidthCost P q w s t u band+
      couplingIndexFromHeadersCost negative V s band i d+
      haloLookupFromHeadersCost V w s t band a b k+(2*(k+V)+5)
  omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
