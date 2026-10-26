module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGenerateLiftedCoefficientWidth
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCoefficientHeaderWidth

/-! Select and generate the complete coefficient workspace, execute from
ordinary headers and release that width. No workspace inequalities are inputs. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellRationalArgs

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def closedCoefficient (code : TblCode 48) : Pr P₀ 117 Q A U :=
  .seq generateLiftedCoefficientWidth (.seq (coefficientFromHeaders code) (uclear 115))

def closedCoefficientCost (K P q w s t u band i d : ℕ) : ℕ :=
  let V := liftedCoefficientWidth P q w s t u band
  generateLiftedCoefficientWidthCost P q w s t u band+
    coefficientFromHeadersCost K P q V w s t u band i d+(2*V+2)

theorem closedCoefficient_exec {w q P s t u band i d K : ℕ}
    (code : TblCode 48) (z : GaussianInt)
    (hc : TblDo A (liftedCoefficientWidth P q w s t u band) w code
      (liftedCoefficientHeaderState P q s t u band i d)
      (fun st' => st'.acc = (csyms A w z).reverse) K)
    (hd : d ≤ band) (hi : i < s)
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hPsrc : (S.R 114).length = P) (hqsrc : (S.R 112).length = q)
    (hsSrc : (S.R 97).length = s) (htSrc : (S.R 98).length = t)
    (huSrc : (S.R 99).length = u) (hbSrc : (S.R 100).length = band)
    (hiSrc : (S.R 107).length = i) (hdSrc : (S.R 108).length = d)
    (h115 : S.R 115 = []) (h104 : S.R 104 = []) (hwsrc : (S.R 94).length = w) (h106 : S.R 106 = [])
    (hblank : ∀ r : Fin 117, r.val < 63 → S.R r = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ closedCoefficientCost K P q w s t u band i d ∧
      Exec body (closedCoefficient code) (mk v S) m
        (mk v' {S with R := (Function.update S.R 110
          (csyms A w z++S.R 110))}) := by
  let V := liftedCoefficientWidth P q w s t u band
  have hf := liftedCoefficientWidth_fits false P q w s t u band i d hi hd
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := generateLiftedCoefficientWidth_exec (body := body)
    P q w s t u band v S hPsrc hqsrc hwsrc hsSrc htSrc huSrc hbSrc h115 h104 (by
      intro k hk
      have hv : k.val < 63 := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl <;> decide
      exact hblank k hv)
  let S₁ : Stacks 117 A := {S with R := Function.update S.R 115 (List.replicate V tick)}
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := coefficientFromHeaders_exec (body := body) code z hc
    (liftedCoefficientHeaderState_fits P q w s t u band i d hi hd) hf.wordWidth v₁ S₁
    (by simpa [S₁] using hPsrc) (by simpa [S₁] using hqsrc)
    (by simpa [S₁] using hsSrc) (by simpa [S₁] using htSrc)
    (by simpa [S₁] using huSrc) (by simpa [S₁] using hbSrc)
    (by simpa [S₁] using hiSrc) (by simpa [S₁] using hdSrc)
    (by simp [S₁,V]) (by simpa [S₁] using hwsrc) (by simpa [S₁] using h106) (by
      intro k hk
      have hne : k ≠ 115 := by intro he; subst k; norm_num at hk
      simpa [S₁,hne] using hblank k hk)
  let word := csyms A w z
  let S₂ : Stacks 117 A := {S₁ with R := Function.update S₁.R 110 (word++S₁.R 110)}
  obtain ⟨v₃,hu₃,he₃⟩ := uclear_exec body 115 v₂ S₂
  have he₃' : Exec body (uclear 115) (mk v₂ S₂) (2*V+2)
      (mk v₃ {S with R := Function.update S.R 110 (word++S.R 110)}) := by
    convert he₃ using 1
    · simp [S₂,S₁]
    · congr 1
      ext1
      · rfl
      · rfl
      · rfl
      · funext k
        by_cases h115' : k = 115
        · subst k; simp [h115]
        by_cases h110 : k = 110
        · subst k; simp [S₂,S₁]
        simp [S₂,S₁,h115',h110]
  refine ⟨v₃,n₁+(n₂+(2*V+2)),hu₃.trans (hu₂.trans hu₁),?_,Exec.seq he₁ (Exec.seq he₂ he₃')⟩
  dsimp only [closedCoefficientCost,V]
  omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
