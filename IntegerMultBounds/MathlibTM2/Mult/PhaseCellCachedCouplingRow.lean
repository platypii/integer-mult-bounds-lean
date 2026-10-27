module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCachedCouplingOperands
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRawCouplingRow

/-! Complete coupling-row execution from raw ambient input and ordinary headers. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellRationalArgs
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 118 Q A U}

noncomputable def cachedProtectedCouplingRow (hQ : SS.states ≤ Q) : Pr P₀ 118 Q A U :=
  embProg cachedCouplingCoreReg Empty.elim (protectedCouplingRow (P₀ := Empty) hQ)

noncomputable def cachedCouplingRow (hQ : SS.states ≤ Q) (boundary : Bool) : Pr P₀ 118 Q A U :=
  .seq (cachedCouplingOperands boundary) (cachedProtectedCouplingRow hQ)

def cachedCouplingRowCost (P q w s t u band a b i : ℕ) : ℕ :=
  prepareCouplingOperandsCost P q w s t u band a b i+
    generatedReadyRowCost (2*band+1) q w band+4*(s+t+u)+12

theorem cachedCouplingRow_exec (hQ : SS.states ≤ Q) {P q w s t u band a b i : ℕ} [NeZero s]
    (boundary : Bool) (hA : 96 ≤ A) (hw5 : 5 ≤ w) (hqw : q+4 ≤ w)
    (hst : s < t) (haS : a ≤ s) (hbS : b ≤ s) (hbandS : band ≤ s) (hi : i < s) (hP : 13 ≤ P)
    (C : ZMod s → GaussianInt) (tail : List (Fin (A+4)))
    (v : HS 118 Q A U) (S : Stacks 118 A)
    (hPsrc : (S.R 114).length = P) (hqsrc : (S.R 112).length = q) (husrc : (S.R 99).length = u)
    (hsSrc : (S.R 97).length = s) (htSrc : (S.R 98).length = t)
    (hbandSrc : (S.R 100).length = band) (hiSrc : (S.R 107).length = i) (h105 : S.R 105 = [])
    (haSrc : (S.R 101).length = a) (hbSrc : (S.R 103).length = b)
    (hwsrc : (S.R 94).length = w) (h115 : S.R 115 = []) (h104 : S.R 104 = [])
    (h109 : S.R 109 = []) (h106 : S.R 106 = []) (h108 : S.R 108 = [])
    (hblank : ∀ r : Fin 117, r.val < 63 → (embStk cachedCouplingCoreReg S).R r = [])
    (hsrc : S.R 117 = cstream A w (chirpLine s C)++tail) (h116 : S.R 116 = []) (h102 : S.R 102 = [])
    (rhs : GaussianInt) (rhsTail : List (Fin (A+4)))
    (hrhs : S.R 93 = csyms A w rhs++rhsTail) (hc : CClean mul (embStk cachedCouplingCoreReg S))
    (hcr : ∀ r : CR, (embStk cachedCouplingCoreReg S).R (cr r) = [])
    (hleft : ∀ k ∈ [(97 : Fin 117),98,99,100], (embStk cachedCouplingCoreReg S).L k = []) (h96 : S.R 96 = [])
    (hxs : ∀ x ∈ couplingInputWords boundary t band a b i C, Fits w x)
    (has : ∀ z ∈ couplingCoefficientWords P q s t u band i, Fits w z ∧ z.im = 0) :
    ∃ v' m, v'.user = v.user ∧ m ≤ cachedCouplingRowCost P q w s t u band a b i ∧
      Exec body (cachedCouplingRow hQ boundary) (mk v S) m
        (mk v' {S with R := (Function.update S.R 113
          (csyms A w (rhs-(List.zipWith (fun x z => tdivN q (x*z))
            (couplingInputWords boundary t band a b i C)
            (couplingCoefficientWords P q s t u band i)).sum)++S.R 113))}) := by
  have hlookupBlank : ∀ r : Fin 117, r.val < 63 → (embStk cachedCouplingLookupReg S).R r = [] := by
    intro r hr
    have hn : r ≠ 92 := by intro he; subst r; norm_num at hr
    simpa only [embStk,Function.comp_def,cachedCouplingLookupReg,hn,ite_false] using hblank r hr
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := cachedCouplingOperands_exec (body := body)
    boundary (by omega) hst haS hbS hbandS hi hP C tail v S hPsrc hqsrc husrc hsSrc htSrc
    hbandSrc hiSrc h105 haSrc hbSrc hwsrc h115 h104 h109 h106 h108 hlookupBlank hsrc h116 h102
  let M : Stacks 118 A := {S with R := (Function.update (Function.update (Function.update S.R
    111 (cstream A w (couplingCoefficientWords P q s t u band i)++S.R 111))
    102 (List.replicate (2*band+1) tick))
    110 (cstream A w (couplingInputWords boundary t band a b i C)++S.R 110))}
  let T := embStk cachedCouplingCoreReg S
  let xs := couplingInputWords boundary t band a b i C
  let as := couplingCoefficientWords P q s t u band i
  let S₁ : Stacks 117 A := {T with R := (Function.update (Function.update (Function.update T.R
    111 (cstream A w as++T.R 111)) 102 (List.replicate (2*band+1) tick))
    110 (cstream A w xs++T.R 110))}
  have hoff (r : Fin 117) (hr : r ≠ 111 ∧ r ≠ 102 ∧ r ≠ 110) : S₁.R r = T.R r := by
    simp [S₁,hr.1,hr.2.1,hr.2.2]
  have hcrOff (r : CR) : S₁.R (cr r) = T.R (cr r) := by
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
  have hview : embStk cachedCouplingCoreReg M = S₁ := by
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases h110 : k = 110
    · subst k; rfl
    by_cases h111 : k = 111
    · subst k; rfl
    by_cases h102 : k = 102
    · subst k; rfl
    have hn110 : cachedCouplingCoreReg k ≠ 110 := cachedCouplingCoreReg_injective.ne h110
    have hn111 : cachedCouplingCoreReg k ≠ 111 := cachedCouplingCoreReg_injective.ne h111
    have hn102 : cachedCouplingCoreReg k ≠ 102 := cachedCouplingCoreReg_injective.ne h102
    simp only [M,S₁,T,embStk,Function.comp_def,Function.update_of_ne h110,Function.update_of_ne h111,
      Function.update_of_ne h102,Function.update_of_ne hn110,Function.update_of_ne hn111,Function.update_of_ne hn102]
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := protectedCouplingRow_exec (body := fun p : Empty => nomatch p) (L := 2*band+1) hQ hA hw5 hqw xs as rhs
    (by simp [xs]) (by simp [as]) hxs has (embDn cachedCouplingCoreReg v₁) S₁ (T.R 110) (T.R 111) rhsTail
    (by simp [S₁]) (by simpa [S₁,T,embStk,cachedCouplingCoreReg] using hwsrc) (by simpa [S₁,T,embStk,cachedCouplingCoreReg] using hqsrc)
    (by simp [S₁]) (by simp [S₁]) (by simpa [S₁,T,embStk,cachedCouplingCoreReg] using hrhs) hc₁
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
        · subst k; simpa [S₁,T,embStk,cachedCouplingCoreReg] using h96
        · subst k; simp at hgeom
        · subst k; simp at hgeom
        · subst k; simp at hgeom
        · subst k; simpa [S₁,T,embStk,cachedCouplingCoreReg] using h104
        · subst k; simpa [S₁,T,embStk,cachedCouplingCoreReg] using h105
        · subst k; simpa [S₁,T,embStk,cachedCouplingCoreReg] using h106)
    (by simpa [S₁,T,embStk,cachedCouplingCoreReg] using h109)
  have hm₂' : m₂ ≤ generatedReadyRowCost (2*band+1) q w band+4*(s+t+u)+12 := by
    simpa [S₁,hbandSrc,hsSrc,htSrc,husrc,T,embStk,cachedCouplingCoreReg] using hm₂
  have hresult :
      {S₁ with R := (Function.update (Function.update (Function.update (Function.update S₁.R
        113 (csyms A w (rhs-(List.zipWith (fun x z => tdivN q (x*z)) xs as).sum)++S₁.R 113))
          110 (T.R 110)) 111 (T.R 111)) 102 [])} =
      {T with R := (Function.update T.R 113
        (csyms A w (rhs-(List.zipWith (fun x z => tdivN q (x*z)) xs as).sum)++T.R 113))} := by
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases h110 : k = 110 <;> by_cases h111 : k = 111 <;> by_cases hk102 : k = 102 <;>
      simp [S₁,h110,h111,hk102,h102,xs,as,Function.update_apply,T,embStk,cachedCouplingCoreReg]
  have he₂' := he₂.cast rfl (congrArg (mk v₂) hresult)
  obtain ⟨v₃,hv₃,hu₃,he₃⟩ := exec_emb_ovr (ι := Empty.elim) (body' := body)
    cachedCouplingCoreReg_injective (fun p => nomatch p) he₂' v₁ rfl M hview
  refine ⟨v₃,m₁+m₂,hu₃.trans (hu₂.trans hu₁),?_,(Exec.seq he₁ he₃).cast rfl ?_⟩
  · simpa only [cachedCouplingRowCost,Nat.add_assoc] using Nat.add_le_add hm₁ hm₂'
  · apply congrArg (mk v₃)
    let output := csyms A w (rhs-(List.zipWith (fun x z => tdivN q (x*z)) xs as).sum)++T.R 113
    let T' : Stacks 117 A := {T with R := Function.update T.R 113 output}
    have hp := embStk_ovr cachedCouplingCoreReg_injective T' M
    refine Stacks.ext rfl rfl ?_ ?_
    · funext k
      by_cases hk : k.val < 117
      · let j : Fin 117 := ⟨k.val,hk⟩
        have hj : cachedCouplingCoreReg j = k := Fin.ext rfl
        rw [← hj]
        exact congrArg (fun X : Stacks 117 A => X.L j) hp
      · have he : k = 117 := Fin.ext (by have hi := k.isLt; omega)
        subst k
        exact (embOvr_off (e := cachedCouplingCoreReg) T'.get M cachedCouplingCoreReg_off).1
    · funext k
      by_cases hk : k.val < 117
      · let j : Fin 117 := ⟨k.val,hk⟩
        have hj : cachedCouplingCoreReg j = k := Fin.ext rfl
        have hh := congrArg (fun X : Stacks 117 A => X.R j) hp
        rw [← hj]
        change (embOvr cachedCouplingCoreReg T'.get M).R (cachedCouplingCoreReg j) =
          Function.update S.R 113 output (cachedCouplingCoreReg j)
        by_cases hj113 : j = 113
        · rw [hj113] at hh ⊢
          exact hh
        · have hn : cachedCouplingCoreReg j ≠ 113 := cachedCouplingCoreReg_injective.ne hj113
          simpa only [T',T,Function.update_of_ne hj113,Function.update_of_ne hn,embStk,Function.comp_def] using hh
      · have he : k = 117 := Fin.ext (by have hi := k.isLt; omega)
        subst k
        exact (embOvr_off (e := cachedCouplingCoreReg) T'.get M cachedCouplingCoreReg_off).2

theorem cachedCouplingRowCost_saving (P q w s t u band a b i : ℕ) :
    rawCouplingRowCost P q w s t u band a b i =
      cachedCouplingRowCost P q w s t u band a b i+(18*s*w+9*s+18) := by
  dsimp only [rawCouplingRowCost,rawCouplingOperandsCost,cachedCouplingRowCost]
  ring

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
