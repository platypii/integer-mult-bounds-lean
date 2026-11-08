module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellResidentBoundaryOrderPiece
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicBoundaryPageData

/-! Enumerate both physical boundary pieces into one original-coordinate cyclic stream. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 154 Q A U}

def residentCyclicBoundaryOrder : Pr P 154 Q A U :=
  .seq (residentBoundaryOrderPiece false) (residentBoundaryOrderPiece true)

def residentCyclicBoundaryOrderCost (V s t band a n : ℕ) : ℕ :=
  boundaryOrderFromHeadersCost V s t band a (a+min n (s-a))+
    boundaryOrderFromHeadersCost V s t band 0 (n-min n (s-a))

theorem residentCyclicBoundaryOrder_exec {V s t band a n : ℕ} [NeZero s]
    (hst : s < t) (ha : a < s) (hn : n ≤ s) (hband : band ≤ s)
    (hwide : 8*(t+1)^2+2*band+8 < 2^V)
    (v : HS 154 Q A U) (S : Stacks 154 A)
    (hsSrc : (S.R 121).length = s) (htSrc : (S.R 122).length = t) (hbandSrc : (S.R 124).length = band)
    (haSrc : (S.R 144).length = a) (hleftEnd : (S.R 145).length = a+min n (s-a))
    (hrightEnd : (S.R 146).length = n-min n (s-a)) (h138 : S.R 138 = [])
    (hwidth : (S.R 115).length = V) (h106 : S.R 106 = []) (h108 : S.R 108 = [])
    (hlow : ∀ k : Fin 154, k.val < 31 → S.R k = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ residentCyclicBoundaryOrderCost V s t band a n ∧
      Exec body residentCyclicBoundaryOrder (mk v S) m
        (mk v' {S with R := (Function.update S.R 109
          (cstream A V (cyclicBoundaryIndexWords s t band a n)++S.R 109))}) := by
  obtain ⟨v₁,m₁,hv₁,hm₁,he₁⟩ := residentBoundaryOrderPiece_exec (body := body) (V := V) (s := s) (t := t) (band := band) (a := a) (b := a+min n (s-a)) false hst ha.le (by omega) hband hwide
    v S hsSrc htSrc hbandSrc haSrc hleftEnd hwidth h106 h108 hlow
  let left := boundaryOrderSymbols A V s t band a (a+min n (s-a))
  let right := boundaryOrderSymbols A V s t band 0 (n-min n (s-a))
  let F : Stacks 154 A := {S with R := Function.update S.R 109 (left++S.R 109)}
  obtain ⟨v₂,m₂,hv₂,hm₂,he₂⟩ := residentBoundaryOrderPiece_exec (body := body) (V := V) (s := s) (t := t) (band := band) (a := 0) (b := n-min n (s-a)) true hst (by omega) (by omega) hband hwide
    v₁ F (by simpa [F] using hsSrc) (by simpa [F] using htSrc) (by simpa [F] using hbandSrc)
    (by simp [F,h138]) (by simpa [F] using hrightEnd) (by simpa [F] using hwidth)
    (by simpa [F] using h106) (by simpa [F] using h108)
    (by intro k hk; simpa [F,show k ≠ 109 by intro h; subst k; norm_num at hk] using hlow k hk)
  have hwords : right++left = cstream A V (cyclicBoundaryIndexWords s t band a n) :=
    cyclicBoundaryOrderSymbols_cstream A V s t band a n
  refine ⟨v₂,m₁+m₂,hv₂.trans hv₁,Nat.add_le_add hm₁ hm₂,(Exec.seq he₁ he₂).cast rfl ?_⟩
  apply congrArg (mk v₂)
  ext1
  · rfl
  · rfl
  · rfl
  · funext k
    by_cases hk : k = 109
    · subst k
      change right++(left++S.R 109) = cstream A V (cyclicBoundaryIndexWords s t band a n)++S.R 109
      rw [← List.append_assoc,hwords]
    · simp [F,hk]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
