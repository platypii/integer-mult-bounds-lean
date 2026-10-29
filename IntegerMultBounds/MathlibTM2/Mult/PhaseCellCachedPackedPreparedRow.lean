module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCouplingRowValue
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCachedPackedCouplingCount
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCachedPackedCouplingInputs
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCachedPackedProtectedCouplingRow

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

def packedCouplingInputState {A s : ℕ} [NeZero s] (boundary : Bool) (t band a b i w : ℕ)
    (F : ZMod s → GaussianInt) (S : Stacks 118 A) : Stacks 118 A :=
  {S with R := (Function.update S.R 110 (cstream A w (couplingInputWords boundary t band a b i F)++S.R 110))}

def packedCouplingRowState {A s : ℕ} [NeZero s] (boundary : Bool) (t band a b i w : ℕ)
    (F : ZMod s → GaussianInt) (S : Stacks 118 A) : Stacks 118 A :=
  let M := packedCouplingInputState boundary t band a b i w F S
  {M with R := Function.update M.R 102 (List.replicate (2*band+1) tick)}

noncomputable def cachedPackedPreparedRow {P U : Type} {Q A : ℕ} (hQ : SS.states ≤ Q)
    (boundary : Bool) : Pr P 118 Q A U :=
  .seq (cachedPackedCouplingInputs boundary)
    (.seq cachedPackedCouplingCount (cachedPackedProtectedCouplingRow hQ))

theorem cachedPackedPreparedRow_exec {P U : Type} {Q A V s t band a b i : ℕ} [NeZero s]
    {body : P → Pr P 118 Q A U} (boundary : Bool) (value : Fin 117 → ℕ)
    (hs : value 97 = s) (ht : value 98 = t) (hband : value 100 = band)
    (hi : value 107 = i) (hd' : value 105 = 0) (ha : value 101 = a) (hb : value 103 = b)
    (hst : s < t) (hab : a ≤ b) (hbS : b ≤ s) (hfit : i+band*s+band < 2^V)
    (hwide : 8*(t+1)^2+2*band+8 < 2^V)
    (hbound : ∀ i, value (packedLookupBankSource i) < 2^V)
    (v : HS 118 Q A U) (S : Stacks 118 A) (hV : ((embStk cachedCouplingLookupReg S).R 115).length = V)
    (hmeta : ∀ i, (embStk cachedCouplingLookupReg S).R (packedLookupBankSource i) = binSyms V (value (packedLookupBankSource i)))
    (hblank : ∀ r, (embStk cachedCouplingLookupReg S).R (originReg r) = []) (w : ℕ) (F : ZMod s → GaussianInt)
    (tail : List (Fin (A+4))) (hwidth : ((embStk cachedCouplingLookupReg S).R 94).length = w)
    (hsrc : (embStk cachedCouplingLookupReg S).R 92 = cstream A w (packedInterval a (b-a) F)++tail)
    (hlow : ∀ r : Fin 117, r.val < 31 → (embStk cachedCouplingLookupReg S).R r = [])
    (h108 : (embStk cachedCouplingLookupReg S).R 108 = []) (h109 : (embStk cachedCouplingLookupReg S).R 109 = []) (h116 : (embStk cachedCouplingLookupReg S).R 116 = [])
    (hz : (embStk cachedCouplingLookupReg S).R 106 = binSyms V 0)

    (hQ : SS.states ≤ Q) (hA : 96 ≤ A) (q : ℕ) (hw5 : 5 ≤ w) (hqw : q+4 ≤ w)
    (as : List GaussianInt) (rhs : GaussianInt) (tailA tailR : List (Fin (A+4)))
    (halen : as.length = 2*band+1)
    (hxs : ∀ x ∈ couplingInputWords boundary t band a b i F, Fits w x)
    (has : ∀ z ∈ as, Fits w z ∧ z.im = 0)
    (h102 : S.R 102 = [])
    (hwR : ((embStk cachedCouplingCoreReg (packedCouplingRowState boundary t band a b i w F S)).R 94).length = w) (hq : ((embStk cachedCouplingCoreReg (packedCouplingRowState boundary t band a b i w F S)).R 112).length = q)
    (hcoeff : (embStk cachedCouplingCoreReg (packedCouplingRowState boundary t band a b i w F S)).R 111 = cstream A w as++tailA)
    (hrhs : (embStk cachedCouplingCoreReg (packedCouplingRowState boundary t band a b i w F S)).R 93 = csyms A w rhs++tailR) (hc : CClean mul (embStk cachedCouplingCoreReg (packedCouplingRowState boundary t band a b i w F S)))
    (hcoreBlank : ∀ r : CR, (embStk cachedCouplingCoreReg (packedCouplingRowState boundary t band a b i w F S)).R (cr r) = [])
    (hleft : ∀ k ∈ [(97 : Fin 117),98,99,100], (embStk cachedCouplingCoreReg (packedCouplingRowState boundary t band a b i w F S)).L k = [])
    (hwork : ∀ k ∈ integerRowWork, k ∉ [(97 : Fin 117),98,99,105,106] → (embStk cachedCouplingCoreReg (packedCouplingRowState boundary t band a b i w F S)).R k = [])
    (hcore109 : (embStk cachedCouplingCoreReg (packedCouplingRowState boundary t band a b i w F S)).R 109 = [])
    (hmetaLeft : ∀ r ∈ [(105 : Fin 117),106], (embStk cachedCouplingCoreReg (packedCouplingRowState boundary t band a b i w F S)).L r = []) :
    ∃ v' n, v'.user = v.user ∧
      n ≤ (12*band+22*V+13)+((136*V+137+(33*tblC V V+6*(b-a+1)+84*V+76+((b-a)*(12*w+11)+10*w+30)))+2*(6*band+11*V+6+(band*(14*V+15+(136*V+137+(33*tblC V V+6*(b-a+1)+84*V+76+((b-a)*(12*w+11)+10*w+30)))+3)+2+(6*V+6))) +
        (generatedReadyRowCost (2*band+1) q w (S.R 100).length+
          4*((S.R 97).length+(S.R 98).length+(S.R 99).length)+12+
          4*(S.R 105).length+4+4*(S.R 106).length+4)) ∧
      Exec body (cachedPackedPreparedRow hQ boundary) (mk v S) n
        (mk v' {S with R := (Function.update (Function.update (Function.update (Function.update S.R
          113 (csyms A w (rhs-(List.zipWith (fun x z => tdivN q (x*z))
            (couplingInputWords boundary t band a b i F) as).sum)++S.R 113))
          110 (S.R 110)) 111 tailA) 102 [])}) := by
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := cachedPackedCouplingInputs_exec (body := body) boundary value
    hs ht hband hi hd' ha hb hst hab hbS hfit hwide hbound v S hV hmeta hblank w F tail
    hwidth hsrc hlow h108 h109 h116 hz
  have hbV : band < 2^V := by simpa [packedLookupBankSource,hband] using hbound 2
  have hbmeta : S.R 100 = binSyms V band := by
    simpa [packedLookupBankSource,hband,embStk,cachedCouplingLookupReg,cachedCouplingCoreReg] using hmeta 2
  have hsmall (r : Fin 118) (hr : r.val < 3) : S.R r = [] := by
    let k : Fin 117 := ⟨r.val,by omega⟩
    have hk := hlow k (by dsimp [k]; omega)
    have hne : k ≠ 92 := by intro he; have hv := congrArg Fin.val he; dsimp [k] at hv; omega
    simpa [embStk,cachedCouplingLookupReg,hne,cachedCouplingCoreReg,k] using hk
  obtain ⟨vc,nc,huc,hnc,hec⟩ := cachedPackedCouplingCount_exec (body := body) V band hbV v₁
    (packedCouplingInputState boundary t band a b i w F S)
    (by simpa [packedCouplingInputState] using hbmeta)
    (by simpa [packedCouplingInputState] using h102)
    (by simpa [packedCouplingInputState] using hsmall 0 (by decide))
    (by simpa [packedCouplingInputState] using hsmall 1 (by decide))
    (by simpa [packedCouplingInputState] using hsmall 2 (by decide))
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := cachedPackedProtectedCouplingRow_exec (body := body)
    hQ hA hw5 hqw (couplingInputWords boundary t band a b i F) as rhs
    (by simp) halen hxs has vc (packedCouplingRowState boundary t band a b i w F S)
    (S.R 110) tailA tailR (by simp [packedCouplingRowState,embStk,cachedCouplingCoreReg]) hwR hq (by rfl) hcoeff hrhs hc hcoreBlank hleft hwork hcore109 hmetaLeft
  refine ⟨v₂,n₁+(nc+n₂),hu₂.trans (huc.trans hu₁),?_,(Exec.seq he₁ (Exec.seq hec he₂)).cast rfl ?_⟩
  · have hn₂' := hn₂
    simp [packedCouplingRowState,packedCouplingInputState] at hn₂'
    omega
  · apply congrArg (mk v₂)
    refine Stacks.ext rfl rfl rfl ?_
    funext r
    by_cases h1 : r = 110 <;> by_cases h2 : r = 113 <;>
      by_cases h3 : r = 111 <;> by_cases h4 : r = 102 <;>
      simp [packedCouplingRowState,packedCouplingInputState,h1,h2,h3,h4]

theorem cachedPackedCouplingRowWord_exec {P U : Type} {Q A V s t band a b i : ℕ} [NeZero s]
    {body : P → Pr P 118 Q A U} (boundary : Bool) (value : Fin 117 → ℕ)
    (hs : value 97 = s) (ht : value 98 = t) (hband : value 100 = band)
    (hi : value 107 = i) (hd' : value 105 = 0) (ha : value 101 = a) (hb : value 103 = b)
    (hst : s < t) (hab : a ≤ b) (hbS : b ≤ s) (hfit : i+band*s+band < 2^V)
    (hwide : 8*(t+1)^2+2*band+8 < 2^V)
    (hbound : ∀ i, value (packedLookupBankSource i) < 2^V)
    (v : HS 118 Q A U) (S : Stacks 118 A) (hV : ((embStk cachedCouplingLookupReg S).R 115).length = V)
    (hmeta : ∀ i, (embStk cachedCouplingLookupReg S).R (packedLookupBankSource i) = binSyms V (value (packedLookupBankSource i)))
    (hblank : ∀ r, (embStk cachedCouplingLookupReg S).R (originReg r) = []) (w : ℕ) (F : ZMod s → GaussianInt)
    (tail : List (Fin (A+4))) (hwidth : ((embStk cachedCouplingLookupReg S).R 94).length = w)
    (hsrc : (embStk cachedCouplingLookupReg S).R 92 = cstream A w (packedInterval a (b-a) F)++tail)
    (hlow : ∀ r : Fin 117, r.val < 31 → (embStk cachedCouplingLookupReg S).R r = [])
    (h108 : (embStk cachedCouplingLookupReg S).R 108 = []) (h109 : (embStk cachedCouplingLookupReg S).R 109 = []) (h116 : (embStk cachedCouplingLookupReg S).R 116 = [])
    (hz : (embStk cachedCouplingLookupReg S).R 106 = binSyms V 0)

    (hQ : SS.states ≤ Q) (hA : 96 ≤ A) (q : ℕ) (hw5 : 5 ≤ w) (hqw : q+4 ≤ w)
    (precision u : ℕ) (rhs : GaussianInt) (tailA tailR : List (Fin (A+4)))
    (hxs : ∀ x ∈ couplingInputWords boundary t band a b i F, Fits w x)
    (has : ∀ z ∈ (couplingCoefficientWords precision q s t u band i), Fits w z ∧ z.im = 0)
    (h102 : S.R 102 = [])
    (hwR : ((embStk cachedCouplingCoreReg (packedCouplingRowState boundary t band a b i w F S)).R 94).length = w) (hq : ((embStk cachedCouplingCoreReg (packedCouplingRowState boundary t band a b i w F S)).R 112).length = q)
    (hcoeff : (embStk cachedCouplingCoreReg (packedCouplingRowState boundary t band a b i w F S)).R 111 = cstream A w (couplingCoefficientWords precision q s t u band i)++tailA)
    (hrhs : (embStk cachedCouplingCoreReg (packedCouplingRowState boundary t band a b i w F S)).R 93 = csyms A w rhs++tailR) (hc : CClean mul (embStk cachedCouplingCoreReg (packedCouplingRowState boundary t band a b i w F S)))
    (hcoreBlank : ∀ r : CR, (embStk cachedCouplingCoreReg (packedCouplingRowState boundary t band a b i w F S)).R (cr r) = [])
    (hleft : ∀ k ∈ [(97 : Fin 117),98,99,100], (embStk cachedCouplingCoreReg (packedCouplingRowState boundary t band a b i w F S)).L k = [])
    (hwork : ∀ k ∈ integerRowWork, k ∉ [(97 : Fin 117),98,99,105,106] → (embStk cachedCouplingCoreReg (packedCouplingRowState boundary t band a b i w F S)).R k = [])
    (hcore109 : (embStk cachedCouplingCoreReg (packedCouplingRowState boundary t band a b i w F S)).R 109 = [])
    (hmetaLeft : ∀ r ∈ [(105 : Fin 117),106], (embStk cachedCouplingCoreReg (packedCouplingRowState boundary t band a b i w F S)).L r = []) :
    ∃ v' n, v'.user = v.user ∧
      n ≤ (12*band+22*V+13)+((136*V+137+(33*tblC V V+6*(b-a+1)+84*V+76+((b-a)*(12*w+11)+10*w+30)))+2*(6*band+11*V+6+(band*(14*V+15+(136*V+137+(33*tblC V V+6*(b-a+1)+84*V+76+((b-a)*(12*w+11)+10*w+30)))+3)+2+(6*V+6))) +
        (generatedReadyRowCost (2*band+1) q w (S.R 100).length+
          4*((S.R 97).length+(S.R 98).length+(S.R 99).length)+12+
          4*(S.R 105).length+4+4*(S.R 106).length+4)) ∧
      Exec body (cachedPackedPreparedRow hQ boundary) (mk v S) n
        (mk v' {S with R := (Function.update (Function.update (Function.update (Function.update S.R
          113 (csyms A w (couplingRowWord precision q t u band a b i boundary F rhs)++S.R 113))
          110 (S.R 110)) 111 tailA) 102 [])}) := by
  simpa only [couplingRowWord] using cachedPackedPreparedRow_exec (body := body) boundary value
    hs ht hband hi hd' ha hb hst hab hbS hfit hwide hbound v S hV hmeta hblank w F tail
    hwidth hsrc hlow h108 h109 h116 hz hQ hA q hw5 hqw
    (couplingCoefficientWords precision q s t u band i) rhs tailA tailR (by simp) hxs has h102
    hwR hq hcoeff hrhs hc hcoreBlank hleft hwork hcore109 hmetaLeft

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
