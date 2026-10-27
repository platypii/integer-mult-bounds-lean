module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRowCoefficientLoad

/-! Load ordinary unary parameters, execute a proved coefficient program,
and release every private table register. Only the coefficient output changes. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def rowCoefficientHeaders : List (Fin 117 × Fin 50) :=
  [(114,19),(112,44),(97,34),(98,35),(99,36),(107,37),(100,49)]

def rowCoefficientHeaderState (P q s t u band i : ℕ) : TblSt 50 A :=
  ⟨Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update (fun _ => 0) 19 P) 44 q) 34 s)
      35 t) 36 u) 37 i) 49 band,[]⟩

def rowCoefficientFromHeaders (code : TblCode 50) : Pr P₀ 117 Q A U :=
  .seq initializeRowCoefficientBank (.seq (loadRowCoefficientList rowCoefficientHeaders)
    (rowCoefficientHost code))

def rowCoefficientFromHeadersCost (K P q V w s t u band i N : ℕ) : ℕ :=
  (304*V+4*w+409)+((P+q+s+t+u+i+band)*(4*V+10)+42*V+71)+
    (K*tblC V w+2*(N*w)+130*V+133)

theorem rowCoefficientFromHeaders_exec {V w q P s t u band i K : ℕ}
    (code : TblCode 50) (words : List GaussianInt)
    (hc : TblDo A V w code (rowCoefficientHeaderState P q s t u band i)
      (fun st' => st'.acc = (cstream A w words).reverse) K)
    (hstV : ∀ r, (rowCoefficientHeaderState (A := A) P q s t u band i).val r < 2^V)
    (hw : w ≤ V)
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hPsrc : (S.R 114).length = P) (hqsrc : (S.R 112).length = q)
    (hsSrc : (S.R 97).length = s) (htSrc : (S.R 98).length = t)
    (huSrc : (S.R 99).length = u) (hbSrc : (S.R 100).length = band)
    (hiSrc : (S.R 107).length = i)
    (hVsrc : (S.R 115).length = V) (hwsrc : (S.R 94).length = w) (h106 : S.R 106 = [])
    (hblank : ∀ r ∈ rowCoefficientPorts, S.R r = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ rowCoefficientFromHeadersCost K P q V w s t u band i words.length ∧
      Exec body (rowCoefficientFromHeaders code) (mk v S) m
        (mk v' {S with R := (Function.update S.R 111
          (cstream A w words++S.R 111))}) := by
  let initial : TblSt 50 A := ⟨fun _ => 0,[]⟩
  let st := rowCoefficientHeaderState (A := A) P q s t u band i
  obtain ⟨v₁,hu₁,he₁,hh₁⟩ := initializeRowCoefficientBank_exec (body := body) V w v S
    hVsrc hwsrc h106 (fun r => hblank _ (by simpa only [mem_rowCoefficientPorts] using rowCoefficientReg_range r))
  let S₁ : Stacks 117 A := {S with R := chirpBankLoadR rowCoefficientReg (fun _ => 106) V w (fun _ => 0) S.R}
  have hoff₁ (r : Fin 117) (hr : r ∉ rowCoefficientPorts) : S₁.R r = S.R r := by
    apply chirpBankLoad_off
    exact fun k => (rowCoefficientReg_off r hr k).symm
  let value := fun r : Fin 117 => (S.R r).length
  have hheaders (r : Fin 117 × Fin 50) (hr : r ∈ rowCoefficientHeaders) : r.1 ∉ rowCoefficientPorts := by
    simp only [rowCoefficientHeaders,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  have hsep : ∀ r ∈ rowCoefficientHeaders, ∀ k, rowCoefficientReg k ≠ r.1 := by
    intro r hr
    exact rowCoefficientReg_off r.1 (hheaders r hr)
  obtain ⟨v₂,S₂,m₂,hu₂,hm₂,he₂,hh₂,hf₂⟩ := loadRowCoefficientList_exec (body := body)
    rowCoefficientHeaders hsep V w value initial v₁ S₁
    (by intro r hr; exact congrArg List.length (hoff₁ r.1 (hheaders r hr))) hh₁
  have hstate : loadedRowCoefficientState value rowCoefficientHeaders initial = st := by
    simp [loadedRowCoefficientState,rowCoefficientHeaders,initial,st,rowCoefficientHeaderState,
      value,hPsrc,hqsrc,hsSrc,htSrc,huSrc,hbSrc,hiSrc]
  rw [hstate] at hh₂
  obtain ⟨v₃,m₃,hu₃,hm₃,he₃⟩ := rowCoefficientHost_exec (body := body)
    code st (cstream A w words)
    (by simpa only [st,rowCoefficientHeaderState,List.append_nil] using hc) hstV rfl
    (List.replicate V tick) (List.replicate w tick) (by simp) (by simp) hw v₂ S₂ hh₂
  have hoff₂ (r : Fin 117) (hr : r ∉ rowCoefficientPorts) : S₂.R r = S.R r :=
    (hf₂.2.2.2 r (rowCoefficientReg_off r hr)).trans (hoff₁ r hr)
  have hcost : loadRowCoefficientListCost V value rowCoefficientHeaders =
      (P+q+s+t+u+i+band)*(4*V+10)+42*V+71 := by
    simp [loadRowCoefficientListCost,rowCoefficientHeaders,value,hPsrc,hqsrc,hsSrc,htSrc,
      huSrc,hbSrc,hiSrc]; ring
  rw [hcost] at hm₂
  refine ⟨v₃,(304*V+4*w+409)+(m₂+m₃),hu₃.trans (hu₂.trans hu₁),?_,
    (Exec.seq he₁ (Exec.seq he₂ he₃)).cast rfl ?_⟩
  · dsimp only [rowCoefficientFromHeadersCost]
    have hm₃' : m₃ ≤ K*tblC V w+2*(words.length*w)+130*V+133 := by simpa using hm₃
    omega
  · congr 1
    refine Stacks.ext hf₂.1 hf₂.2.1 hf₂.2.2.1 ?_
    funext r
    by_cases hr : r ∈ rowCoefficientPorts
    · have hr111 : r ≠ 111 := by intro he; subst r; simp at hr
      simp [hr,hr111,hblank r hr]
    · by_cases hr111 : r = 111
      · subst r; simp [hoff₂ 111 (by simp)]
      · simp [hr,hr111,hoff₂ r hr]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
