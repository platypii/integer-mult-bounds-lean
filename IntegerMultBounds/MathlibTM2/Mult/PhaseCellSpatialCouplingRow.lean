module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPrepareSpatialCouplingOperands
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellProtectedCouplingRow

/-! Complete coupling-row execution from a positioned spatial source and ordinary headers. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellRationalArgs
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry IntegerMultBounds.NLogN.PhaseCellMatrix

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

noncomputable def spatialCouplingRow (hQ : SS.states ≤ Q) : Pr P₀ 117 Q A U :=
  .seq prepareSpatialCouplingOperands (protectedCouplingRow hQ)

def spatialCouplingRowCost (P q w s t u band i : ℕ) : ℕ :=
  prepareSpatialCouplingOperandsCost P q w s t u band i+
    generatedReadyRowCost (2*band+1) q w band+4*(s+t+u)+12

theorem spatialCouplingRowCost_eq (P q w s t u band i : ℕ) :
    spatialCouplingRowCost P q w s t u band i =
      generateCouplingCoefficientsCost P q w s t u band i +
      generatedReadyRowCost (2*band+1) q w band +
      64*band*w+50*band+16*w+4*(s+t+u)+64 := by
  unfold spatialCouplingRowCost prepareSpatialCouplingOperandsCost
    prepareSpatialCouplingCoefficientsCost generateSpatialCouplingCoefficientsCost copyCountedLineCost
  ring

theorem spatialCouplingRow_exec (hQ : SS.states ≤ Q) {P q w s t u band a b i : ℕ} [NeZero s]
    (boundary : Bool) (hA : 96 ≤ A) (hw5 : 5 ≤ w) (hqw : q+4 ≤ w)
    (hst : s < t) (hi : i < s) (hP : 13 ≤ P)
    (C : ZMod s → GaussianInt) (tail : List (Fin (A+4)))
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hPsrc : (S.R 114).length = P) (hqsrc : (S.R 112).length = q) (husrc : (S.R 99).length = u)
    (hsSrc : (S.R 97).length = s) (htSrc : (S.R 98).length = t)
    (hbandSrc : (S.R 100).length = band) (hiSrc : (S.R 107).length = i) (h105 : S.R 105 = [])
    (hwsrc : (S.R 94).length = w) (h115 : S.R 115 = []) (h104 : S.R 104 = [])
    (h109 : S.R 109 = []) (h106 : S.R 106 = []) (h108 : S.R 108 = [])
    (hblank : ∀ r : Fin 117, r.val < 63 → S.R r = [])
    (hsrc : S.R 92 = cstream A w ((cyclicPaddedLine (fun j : ZMod s =>
      if j ∈ (if boundary then haloBoundary s t band a b else haloInterior s t band a b)
      then C j else 0) band).drop i)++tail) (h116 : S.R 116 = []) (h102 : S.R 102 = [])
    (rhs : GaussianInt) (rhsTail : List (Fin (A+4)))
    (hrhs : S.R 93 = csyms A w rhs++rhsTail) (hc : CClean mul S)
    (hcr : ∀ r : CR, S.R (cr r) = [])
    (hleft : ∀ k ∈ [(97 : Fin 117),98,99,100], S.L k = []) (h96 : S.R 96 = [])
    (hxs : ∀ x ∈ couplingInputWords boundary t band a b i C, Fits w x)
    (has : ∀ z ∈ couplingCoefficientWords P q s t u band i, Fits w z ∧ z.im = 0) :
    ∃ v' m, v'.user = v.user ∧ m ≤ spatialCouplingRowCost P q w s t u band i ∧
      Exec body (spatialCouplingRow hQ) (mk v S) m
        (mk v' {S with R := (Function.update S.R 113
          (csyms A w (rhs-(List.zipWith (fun x z => tdivN q (x*z))
            (couplingInputWords boundary t band a b i C)
            (couplingCoefficientWords P q s t u band i)).sum)++S.R 113))}) := by
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := prepareSpatialCouplingOperands_exec (body := body)
    boundary hst hi hP C tail v S hPsrc hqsrc husrc hsSrc htSrc
    hbandSrc hiSrc h105 hwsrc h115 h104 h109 h106 h108 hblank hsrc h116 h102
  let xs := spatialCouplingInputWords boundary t band a b i C
  let as := spatialCouplingCoefficientWords P q s t u band i
  let S₁ : Stacks 117 A := {S with R := (Function.update (Function.update (Function.update S.R
    111 (cstream A w as++S.R 111)) 102 (List.replicate (2*band+1) tick))
    110 (cstream A w xs++S.R 110))}
  have hoff (r : Fin 117) (hr : r ≠ 111 ∧ r ≠ 102 ∧ r ≠ 110) : S₁.R r = S.R r := by
    simp [S₁,hr.1,hr.2.1,hr.2.2]
  have hcrOff (r : CR) : S₁.R (cr r) = S.R (cr r) := by
    apply hoff
    have hr := (cr_range r).2.1
    constructor
    · intro he; have hv := congrArg Fin.val he; omega
    constructor <;> intro he <;> have hv := congrArg Fin.val he <;> omega
  have hc₁ : CClean mul S₁ := by
    intro i
    have hi := i.isLt
    have hn : mul i ≠ (111 : Fin 117) ∧ mul i ≠ 102 ∧ mul i ≠ 110 := by
      simp only [mul,ne_eq,Fin.ext_iff]
      omega
    exact ⟨(hc i).1,by rw [hoff (mul i) hn]; exact (hc i).2⟩
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := protectedCouplingRow_exec (body := body) (L := 2*band+1) hQ hA hw5 hqw xs as rhs
    (by simp [xs,spatialCouplingInputWords]) (by simp [as])
    (by intro x hx; exact hxs x ((spatialCouplingInputWords_perm boundary t band a b i C).mem_iff.mp hx))
    (by intro z hz; exact has z ((spatialCouplingCoefficientWords_perm P q s t u band i).mem_iff.mp hz)) v₁ S₁ (S.R 110) (S.R 111) rhsTail
    (by simp [S₁]) (by simpa [S₁] using hwsrc) (by simpa [S₁] using hqsrc)
    (by simp [S₁]) (by simp [S₁]) (by simpa [S₁] using hrhs) hc₁
    (by intro r; rw [hcrOff r]; exact hcr r) hleft
    (by intro k hk hgeom
        simp only [integerRowWork,List.mem_cons,List.not_mem_nil,or_false] at hk
        rcases hk with h | h | h | h | h | h | h | h | h | h | h | h | h
        · subst k; rw [hcrOff]; exact hcr _
        · subst k; rw [hcrOff]; exact hcr _
        · subst k; rw [hcrOff]; exact hcr _
        · subst k; rw [hcrOff]; exact hcr _
        · subst k; rw [hcrOff]; exact hcr _
        · subst k; rw [hcrOff]; exact hcr _
        · subst k; simpa [S₁] using h96
        · subst k; simp at hgeom
        · subst k; simp at hgeom
        · subst k; simp at hgeom
        · subst k; simpa [S₁] using h104
        · subst k; simpa [S₁] using h105
        · subst k; simpa [S₁] using h106)
    (by simpa [S₁] using h109)
  refine ⟨v₂,m₁+m₂,hu₂.trans hu₁,?_,(Exec.seq he₁ he₂).cast rfl ?_⟩
  · have hm₂' : m₂ ≤ generatedReadyRowCost (2*band+1) q w band+4*(s+t+u)+12 := by
      simpa [S₁,hbandSrc,hsSrc,htSrc,husrc] using hm₂
    dsimp only [spatialCouplingRowCost]
    omega
  · have hdot : (List.zipWith (fun x z => tdivN q (x*z)) xs as).sum =
        (List.zipWith (fun x z => tdivN q (x*z))
          (couplingInputWords boundary t band a b i C) (couplingCoefficientWords P q s t u band i)).sum := by
      have h := couplingRowWord_spatial P q t u band a b i boundary C (0 : GaussianInt)
      simpa [couplingRowWord,xs,as] using h
    apply congrArg (mk v₂)
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases h110 : k = 110 <;> by_cases h111 : k = 111 <;> by_cases hk102 : k = 102 <;>
      simp [S₁,h110,h111,hk102,h102,hdot,Function.update_apply]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
