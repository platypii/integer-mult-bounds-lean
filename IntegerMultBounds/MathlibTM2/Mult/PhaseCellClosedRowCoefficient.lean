module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRowCoefficientFromHeaders
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedCoefficientRow
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGenerateLiftedCoefficientWidth
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCoefficientHeaderWidth

/-! Generate the full ordered coefficient row from ordinary headers and release its workspace. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellRationalArgs

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def closedRowCoefficient : Pr P₀ 117 Q A U :=
  .seq generateLiftedCoefficientWidth (.seq (rowCoefficientFromHeaders coefficientRowCode) (uclear 115))

def closedRowCoefficientCost (P q w s t u band i : ℕ) : ℕ :=
  let V := liftedCoefficientWidth P q w s t u band
  generateLiftedCoefficientWidthCost P q w s t u band+
    rowCoefficientFromHeadersCost (154*P+4*q+2*band*(930*P+370)+423)
      P q V w s t u band i (2*band+1)+2*V+2

theorem rowCoefficientHeaderState_fits (P q w s t u band i : ℕ) (hi : i < s) :
    ∀ r, (rowCoefficientHeaderState (A := A) P q s t u band i).val r <
      2^(liftedCoefficientWidth P q w s t u band) := by
  let V := liftedCoefficientWidth P q w s t u band
  have h := liftedCoefficientHeaderState_fits (A := A) P q w s t u band i 0 hi (Nat.zero_le band)
  have hP : P < 2^V := by simpa [liftedCoefficientHeaderState] using h 19
  have hq : q < 2^V := by simpa [liftedCoefficientHeaderState] using h 44
  have hs : s < 2^V := by simpa [liftedCoefficientHeaderState] using h 34
  have ht : t < 2^V := by simpa [liftedCoefficientHeaderState] using h 35
  have hu : u < 2^V := by simpa [liftedCoefficientHeaderState] using h 36
  have hb : band < 2^V := by simpa [liftedCoefficientHeaderState] using h 41
  have hi' : i < 2^V := by simpa [liftedCoefficientHeaderState] using h 37
  intro r
  change _ < 2^V
  simp only [rowCoefficientHeaderState,Function.update_apply]
  split_ifs <;> omega

theorem closedRowCoefficient_exec {P q w s t u band i : ℕ}
    (hs0 : 0 < s) (hst : s < t) (hP : 13 ≤ P) (hi : i < s)
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hPsrc : (S.R 114).length = P) (hqsrc : (S.R 112).length = q)
    (hsSrc : (S.R 97).length = s) (htSrc : (S.R 98).length = t)
    (huSrc : (S.R 99).length = u) (hbSrc : (S.R 100).length = band)
    (hiSrc : (S.R 107).length = i) (hV : S.R 115 = []) (h104 : S.R 104 = [])
    (hwsrc : (S.R 94).length = w) (h106 : S.R 106 = [])
    (hblank : ∀ r ∈ rowCoefficientPorts, S.R r = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ closedRowCoefficientCost P q w s t u band i ∧
      Exec body closedRowCoefficient (mk v S) m
        (mk v' {S with R := (Function.update S.R 111
          (cstream A w (spatialCouplingCoefficientWords P q s t u band i)++S.R 111))}) := by
  let V := liftedCoefficientWidth P q w s t u band
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := generateLiftedCoefficientWidth_exec (body := body)
    P q w s t u band v S hPsrc hqsrc hwsrc hsSrc htSrc huSrc hbSrc hV h104
    (by intro k hk
        have hk63 : k.val < 63 := by
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
          rcases hk with rfl | rfl | rfl | rfl | rfl <;> decide
        exact hblank k (by simp [hk63]))
  let S₁ : Stacks 117 A := {S with R := Function.update S.R 115 (List.replicate V tick)}
  let st := rowCoefficientHeaderState (A := A) P q s t u band i
  have hc := coefficientRowCode_do (w := w) (P := P) (q := q) (s := s) (t := t)
    (u := u) (band := band) (i := i) st
    (by simp [st,rowCoefficientHeaderState]) (by simp [st,rowCoefficientHeaderState])
    (by simp [st,rowCoefficientHeaderState]) (by simp [st,rowCoefficientHeaderState])
    (by simp [st,rowCoefficientHeaderState]) (by simp [st,rowCoefficientHeaderState])
    (by simp [st,rowCoefficientHeaderState]) hs0 hst hP hi
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := rowCoefficientFromHeaders_exec (body := body) (V := V) (w := w) coefficientRowCode
    (spatialCouplingCoefficientWords P q s t u band i)
    (by simpa only [st,rowCoefficientHeaderState,List.append_nil] using hc) (rowCoefficientHeaderState_fits P q w s t u band i hi)
    (liftedCoefficientWidth_fits false P q w s t u band i 0 hi (Nat.zero_le band)).wordWidth v₁ S₁
    (by simpa [S₁] using hPsrc) (by simpa [S₁] using hqsrc)
    (by simpa [S₁] using hsSrc) (by simpa [S₁] using htSrc)
    (by simpa [S₁] using huSrc) (by simpa [S₁] using hbSrc) (by simpa [S₁] using hiSrc)
    (by simp [S₁]) (by simpa [S₁] using hwsrc) (by simpa [S₁] using h106)
    (by intro k hk
        have hn : k ≠ 115 := by intro he; subst k; simp at hk
        simpa [S₁,hn] using hblank k hk)
  let S₂ : Stacks 117 A := {S₁ with R := (Function.update S₁.R 111
    (cstream A w (spatialCouplingCoefficientWords P q s t u band i)++S₁.R 111))}
  obtain ⟨v₃,hu₃,he₃⟩ := uclear_exec (body := body) 115 v₂ S₂
  refine ⟨v₃,m₁+(m₂+(2*V+2)),hu₃.trans (hu₂.trans hu₁),?_,
    (Exec.seq he₁ (Exec.seq he₂ he₃)).cast (by simp [S₂,S₁]) ?_⟩
  · have hm₂' : m₂ ≤ rowCoefficientFromHeadersCost (154*P+4*q+2*band*(930*P+370)+423)
        P q V w s t u band i (2*band+1) := by simpa using hm₂
    dsimp only [closedRowCoefficientCost]
    dsimp only [V] at hm₂' ⊢
    omega
  · apply congrArg (mk v₃)
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases h115 : k = 115 <;> by_cases h111 : k = 111 <;> simp [S₂,S₁,h115,h111,hV]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
