module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellLiftedDirectCoefficient
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCoefficientLoad

/-! Load ordinary unary parameters, construct the lifted direct coefficient,
and release every private table register. Only the coefficient output changes. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellRationalArgs

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def liftedCoefficientHeaders : List (Fin 117 × Fin 48) :=
  [(114,19),(112,44),(97,34),(98,35),(99,36),(107,37),(100,41),(108,42)]

def liftedCoefficientHeaderState (P q s t u band i d : ℕ) : TblSt 48 A :=
  ⟨Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update (fun _ => 0) 19 P) 44 q) 34 s)
      35 t) 36 u) 37 i) 41 band) 42 d,[]⟩

def liftedCoefficientFromHeaders (negative : Bool) : Pr P₀ 117 Q A U :=
  .seq initializeCoefficientBank (.seq (loadCoefficientList liftedCoefficientHeaders)
    (coefficientTableHost (liftedDirectCoefficientCode negative)))

def liftedCoefficientFromHeadersCost (P q V w s t u band i d : ℕ) : ℕ :=
  (292*V+4*w+393)+((P+q+s+t+u+i+band+d)*(4*V+10)+48*V+81)+
    ((464*P+4*q+545)*tblC V w+2*w+126*V+129)

theorem liftedCoefficientFromHeaders_exec {V w q P s t u band i d : ℕ}
    (negative : Bool)
    (hs0 : 0 < s) (hst : s < t) (hP : 13 ≤ P) (hd : d ≤ band)
    (hfit : i+band*s+d < 2^V)
    (hjV : 2*t*liftedSource s band i+s < 2^V)
    (hkV : 2*t*liftedTarget negative s band i d+s < 2^V) (hsV : 2*s < 2^V)
    (hnjV : s*nearestNatural s t (liftedSource s band i) < 2^V)
    (hnkV : s*nearestNatural s t (liftedTarget negative s band i d) < 2^V)
    (hdjV : latticeDistance s t (liftedSource s band i) (liftedTarget negative s band i d)^2 < 2^V)
    (hdkV : latticeDistance s t (liftedTarget negative s band i d) (liftedTarget negative s band i d)^2 < 2^V)
    (hsqV : s^2 < 2^V) (hV : 13*P+8 ≤ V)
    (haV : latticeNumerator s t u (liftedSource s band i) (liftedTarget negative s band i d)*
      2^(5*P+2) < 2^V) (hqV : q+P+2 ≤ V)
    (htV : t < 2^V) (huV : u < 2^V) (hw : w ≤ V)
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hPsrc : (S.R 114).length = P) (hqsrc : (S.R 112).length = q)
    (hsSrc : (S.R 97).length = s) (htSrc : (S.R 98).length = t)
    (huSrc : (S.R 99).length = u) (hbSrc : (S.R 100).length = band)
    (hiSrc : (S.R 107).length = i) (hdSrc : (S.R 108).length = d)
    (hVsrc : (S.R 115).length = V) (hwsrc : (S.R 94).length = w) (h106 : S.R 106 = [])
    (hblank : ∀ r : Fin 117, r.val < 63 → S.R r = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ liftedCoefficientFromHeadersCost P q V w s t u band i d ∧
      Exec body (liftedCoefficientFromHeaders negative) (mk v S) m
        (mk v' {S with R := (Function.update S.R 110
          (csyms A w (rationalWord q (PhaseCellCrossCell.direct P s t u
            (liftedSource s band i) (liftedTarget negative s band i d)))++S.R 110))}) := by
  let initial : TblSt 48 A := ⟨fun _ => 0,[]⟩
  let st := liftedCoefficientHeaderState (A := A) P q s t u band i d
  obtain ⟨v₁,hu₁,he₁,hh₁⟩ := initializeCoefficientBank_exec (body := body) V w v S
    hVsrc hwsrc h106 (fun r => hblank _ (coefficientReg_range r))
  let S₁ : Stacks 117 A := {S with R := chirpBankLoadR coefficientReg (fun _ => 106) V w (fun _ => 0) S.R}
  have hoff₁ (r : Fin 117) (hr : 63 ≤ r.val) : S₁.R r = S.R r := by
    apply chirpBankLoad_off
    intro k he
    have hh := coefficientReg_range k
    have hv := congrArg Fin.val he
    omega
  let value := fun r : Fin 117 => (S.R r).length
  have hsep : ∀ r ∈ liftedCoefficientHeaders, ∀ k, coefficientReg k ≠ r.1 := by
    intro r hr k he
    have hv : 63 ≤ r.1.val := by
      simp only [liftedCoefficientHeaders,List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have hh := coefficientReg_range k
    have hv := congrArg Fin.val he
    omega
  obtain ⟨v₂,S₂,m₂,hu₂,hm₂,he₂,hh₂,hf₂⟩ := loadCoefficientList_exec (body := body)
    liftedCoefficientHeaders hsep V w value initial v₁ S₁
    (by intro r hr
        have hv : 63 ≤ r.1.val := by
          simp only [liftedCoefficientHeaders,List.mem_cons,List.not_mem_nil,or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
        exact congrArg List.length (hoff₁ r.1 hv)) hh₁
  have hstate : loadedCoefficientState value liftedCoefficientHeaders initial = st := by
    simp [loadedCoefficientState,liftedCoefficientHeaders,initial,st,liftedCoefficientHeaderState,
      value,hPsrc,hqsrc,hsSrc,htSrc,huSrc,hbSrc,hiSrc,hdSrc]
  rw [hstate] at hh₂
  have hstV : ∀ r, st.val r < 2^V := by
    have hPV : P < 2^V := (show P ≤ V by omega).trans_lt Nat.lt_two_pow_self
    have hqbound : q < 2^V := (show q ≤ V by omega).trans_lt Nat.lt_two_pow_self
    have hiV : i < 2^V := by omega
    have hdV : d < 2^V := by omega
    have hbV : band < 2^V := by
      have hh : band ≤ band*s := by nlinarith only [hs0]
      omega
    intro r
    simp only [st,liftedCoefficientHeaderState,Function.update_apply]
    split_ifs <;> first | assumption | omega
  have hc := liftedDirectCoefficientCode_do (w := w) negative st
    (by simp [st,liftedCoefficientHeaderState]) (by simp [st,liftedCoefficientHeaderState])
    (by simp [st,liftedCoefficientHeaderState]) (by simp [st,liftedCoefficientHeaderState])
    (by simp [st,liftedCoefficientHeaderState]) (by simp [st,liftedCoefficientHeaderState])
    (by simp [st,liftedCoefficientHeaderState]) (by simp [st,liftedCoefficientHeaderState])
    hs0 hst hP hd hfit hjV hkV hsV hnjV hnkV hdjV hdkV hsqV hV haV hqV
  obtain ⟨v₃,m₃,hu₃,hm₃,he₃⟩ := coefficientTableHost_exec (body := body)
    (liftedDirectCoefficientCode negative) st
    (csyms A w (rationalWord q (PhaseCellCrossCell.direct P s t u
      (liftedSource s band i) (liftedTarget negative s band i d)))) hc hstV rfl
    (List.replicate V tick) (List.replicate w tick) (by simp) (by simp) hw v₂ S₂ hh₂
  have hoff₂ (r : Fin 117) (hr : 63 ≤ r.val) : S₂.R r = S.R r :=
    (hf₂.2.2.2 r (fun k he => by have hh := coefficientReg_range k; have hv := congrArg Fin.val he; omega)).trans
      (hoff₁ r hr)
  have hcost : loadCoefficientListCost V value liftedCoefficientHeaders =
      (P+q+s+t+u+i+band+d)*(4*V+10)+48*V+81 := by
    simp [loadCoefficientListCost,liftedCoefficientHeaders,value,hPsrc,hqsrc,hsSrc,htSrc,
      huSrc,hbSrc,hiSrc,hdSrc]; ring
  rw [hcost] at hm₂
  refine ⟨v₃,(292*V+4*w+393)+(m₂+m₃),hu₃.trans (hu₂.trans hu₁),?_,
    (Exec.seq he₁ (Exec.seq he₂ he₃)).cast rfl ?_⟩
  · dsimp only [liftedCoefficientFromHeadersCost]
    have hm₃' : m₃ ≤ (464*P+4*q+545)*tblC V w+2*w+126*V+129 := by simpa [csyms] using hm₃
    omega
  · congr 1
    refine Stacks.ext hf₂.1 hf₂.2.1 hf₂.2.2.1 ?_
    funext r
    by_cases hr : r.val < 63
    · have hr110 : r ≠ 110 := by intro he; subst r; norm_num at hr
      simp [hr,hr110,hblank r hr]
    · have hv : 63 ≤ r.val := by omega
      by_cases hr110 : r = 110
      · subst r; simp [hoff₂ 110 (by decide)]
      · simp [hr,hr110,hoff₂ r hv]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
