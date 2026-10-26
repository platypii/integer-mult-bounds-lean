module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryOrderCode
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellOriginRelease
public import IntegerMultBounds.MathlibTM2.Fast.TableBounds

/-! Execute boundary enumeration and release its geometry workspace. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv

theorem boundaryOrderSymbols_length_le (A w s t band a b : ℕ) :
    (boundaryOrderSymbols A w s t band a b).length ≤ s*w := by
  have h : ∀ ks : List ℕ, (ks.flatMap (fun k =>
      if IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry.haloMaskAt true s t band a b k
      then tblPairs A w k 0 else [])).length ≤ ks.length*w := by
    intro ks
    induction ks with
    | nil => simp
    | cons k ks ih =>
      simp only [List.flatMap_cons,List.length_append,List.length_cons]
      split_ifs <;> simp only [length_tblPairs,List.length_nil] <;> nlinarith only [ih]
  simpa [boundaryOrderSymbols] using h (List.range s)

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def boundaryOrderHost : Pr P₀ 117 Q A U :=
  .seq (tblHost originReg boundaryOrderCode 109) releaseOriginBank

def boundaryOrderHostCost (V s : ℕ) : ℕ := (31*s+3)*tblC V V+2*s*V+62*V+65

theorem boundaryOrderHost_exec {V s t band a b : ℕ} (st : TblSt 16 A)
    (hs : st.val 0 = s) (ht : st.val 1 = t) (hband : st.val 2 = band)
    (ha : st.val 4 = a) (hb : st.val 5 = b) (hacc : st.acc = [])
    (hs0 : 0 < s) (hst : s < t) (haS : a ≤ s) (hbS : b ≤ s) (hbandS : band ≤ s)
    (hwide : 8*(t+1)^2+2*band+8 < 2^V) (hbound : ∀ r, st.val r < 2^V)
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hS : tblHolds originReg S (tblRho V (List.replicate V tick) (List.replicate V tick) st)) :
    ∃ v' m, v'.user = v.user ∧ m ≤ boundaryOrderHostCost V s ∧
      Exec body boundaryOrderHost (mk v S) m
        (mk v' {S with R := fun r => if r.val < 31 then [] else if r = 109 then
          boundaryOrderSymbols A V s t band a b++S.R r else S.R r}) := by
  have hc := boundaryOrderCode_do (A := A) (V := V) (w := V) st hs ht hband ha hb
    hs0 hst haS hbS hbandS hwide
  have hoff : ∀ r, originReg r ≠ (109 : Fin 117) := by
    intro r he
    have hr := originReg_range r
    rw [he] at hr
    omega
  obtain ⟨v₁,S₁,n₁,st',hp,hu₁,hn₁,he₁,hout,hh₁,hinp,houtS,hL,hframe⟩ :=
    tblHost_runs (body := body) originReg_injective hoff (List.replicate V tick)
      (List.replicate V tick) (by simp) (by simp) le_rfl (hc.bounded hbound) hbound v S hS
  have hacc' : st'.acc = (boundaryOrderSymbols A V s t band a b).reverse := by
    simpa [boundaryOrderSymbols,hacc] using hp.1
  have hlen : st'.acc.length ≤ s*V := by
    rw [hacc',List.length_reverse]
    exact boundaryOrderSymbols_length_le _ _ _ _ _ _ _
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := releaseOriginBank_exec (body := body) V st'.val v₁ S₁ hh₁
  refine ⟨v₂,n₁+n₂,hu₂.trans hu₁,?_,(Exec.seq he₁ he₂).cast rfl ?_⟩
  · dsimp [boundaryOrderHostCost]
    nlinarith only [hn₁,hn₂,hlen]
  · apply congrArg (mk v₂)
    refine Stacks.ext hinp houtS hL ?_
    funext r
    by_cases hr : r.val < 31
    · simp [hr]
    · by_cases h109 : r = 109
      · subst r
        simpa [hacc'] using hout
      · have hoffr : ∀ x, originReg x ≠ r := by
          intro x he
          have hx := originReg_range x
          rw [he] at hx
          omega
        simpa [hr,h109] using hframe r h109 hoffr

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
