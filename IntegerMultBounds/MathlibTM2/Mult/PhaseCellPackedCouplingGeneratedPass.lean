module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedCouplingOffsetPass

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

/-- Generate the loop count from binary metadata, then gather and restore the offset. -/
def packedCouplingGeneratedPass {P U : Type} {Q A : ℕ} (negative boundary : Bool) : Pr P 117 Q A U :=
  .seq (toUnary 100 116 0 1 2) (packedCouplingOffsetPass negative boundary)

theorem packedCouplingGeneratedPass_exec {P U : Type} {Q A V s t band a b i : ℕ} [NeZero s]
    {body : P → Pr P 117 Q A U} (negative boundary : Bool) (value : Fin 117 → ℕ)
    (hs : value 97 = s) (ht : value 98 = t) (hband : value 100 = band)
    (hi : value 107 = i) (hd' : value 105 = 0) (ha : value 101 = a) (hb : value 103 = b)
    (hst : s < t) (hab : a ≤ b) (hbS : b ≤ s) (hfit : i+band*s+band < 2^V)
    (hwide : 8*(t+1)^2+2*band+8 < 2^V)
    (hbound : ∀ i, value (packedLookupBankSource i) < 2^V)
    (v : HS 117 Q A U) (S : Stacks 117 A) (hV : (S.R 115).length = V)
    (hmeta : ∀ i, S.R (packedLookupBankSource i) = binSyms V (value (packedLookupBankSource i)))
    (hblank : ∀ r, S.R (originReg r) = []) (w : ℕ) (F : ZMod s → GaussianInt)
    (tail : List (Fin (A+4))) (hwidth : (S.R 94).length = w)
    (hsrc : S.R 92 = cstream A w (packedInterval a (b-a) F)++tail)
    (hlow : ∀ r : Fin 117, r.val < 31 → S.R r = [])
    (h108 : S.R 108 = []) (h109 : S.R 109 = []) (h116 : S.R 116 = [])
    (hz : S.R 106 = binSyms V 0) :
    ∃ v' n, v'.user = v.user ∧
      n ≤ 6*band+11*V+6+(band*(14*V+15+(136*V+137+(33*tblC V V+6*(b-a+1)+84*V+76+((b-a)*(12*w+11)+10*w+30)))+3)+2+(6*V+6)) ∧
      Exec body (packedCouplingGeneratedPass negative boundary) (mk v S) n
        (mk v' {S with R := Function.update (Function.update S.R 110
          (cstream A w (couplingInputOffsetWords negative boundary t band a b i band F)++S.R 110)) 116 []}) := by
  have hbV : band < 2^V := by simpa [packedLookupBankSource,hband] using hbound 2
  have hbmeta : S.R 100 = binSyms V band := by simpa [packedLookupBankSource,hband] using hmeta 2
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := toUnary_exec_linear (body := body) (a := 100) (z := 116)
    (w := 0) (t := 1) (t₂ := 2) (by decide) hbV v S hbmeta
    (hlow 0 (by decide)) (hlow 1 (by decide)) (hlow 2 (by decide))
  let S₁ : Stacks 117 A := {S with R := Function.update S.R 116 (List.replicate band tick)}
  have he₁' : Exec body (toUnary 100 116 0 1 2) (mk v S) n₁ (mk v₁ S₁) := by
    simpa only [h116,List.append_nil] using he₁
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := packedCouplingOffsetPass_exec (body := body) negative boundary value
    hs ht hband hi hd' ha hb hst hab hbS hfit hwide hbound v₁ S₁
    (by simpa [S₁] using hV)
    (by intro k
        have hk : packedLookupBankSource k ≠ 116 := by
          simp only [packedLookupBankSource]; split_ifs <;> decide
        simpa only [S₁,Function.update_of_ne hk] using hmeta k)
    (by intro r; have hr := originReg_range r
        have hne : originReg r ≠ 116 := by intro he; rw [he] at hr; omega
        simpa only [S₁,Function.update_of_ne hne] using hblank r)
    w F tail (by simpa [S₁] using hwidth) (by simpa [S₁] using hsrc)
    (by intro r hr
        have hne : r ≠ 116 := by intro he; subst r; norm_num at hr
        simpa only [S₁,Function.update_of_ne hne] using hlow r hr)
    (by simpa [S₁] using h108) (by simpa [S₁] using h109)
    (by simp [S₁]) (by simpa [S₁] using hz)
  refine ⟨v₂,n₁+n₂,hu₂.trans hu₁,by omega,(Exec.seq he₁' he₂).cast rfl ?_⟩
  apply congrArg (mk v₂)
  refine Stacks.ext rfl rfl rfl ?_
  funext r
  by_cases h1 : r = 110 <;> by_cases h2 : r = 116 <;> simp [S₁,h1,h2]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
