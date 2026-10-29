module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedCouplingGeneratedPass
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCouplingInputWords

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

def generatePackedCouplingInputs {P U : Type} {Q A : ℕ} (boundary : Bool) : Pr P 117 Q A U :=
  .seq (.seq loadPackedLookupBank
    (.seq (packedLookupCountersFor (guardedPackedCouplingLookupCode false boundary)) packedHaloRead))
    (.seq (packedCouplingGeneratedPass false boundary) (packedCouplingGeneratedPass true boundary))

theorem generatePackedCouplingInputs_exec {P U : Type} {Q A V s t band a b i : ℕ} [NeZero s]
    {body : P → Pr P 117 Q A U} (boundary : Bool) (value : Fin 117 → ℕ)
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
      n ≤ (136*V+137+(33*tblC V V+6*(b-a+1)+84*V+76+((b-a)*(12*w+11)+10*w+30)))+2*(6*band+11*V+6+(band*(14*V+15+(136*V+137+(33*tblC V V+6*(b-a+1)+84*V+76+((b-a)*(12*w+11)+10*w+30)))+3)+2+(6*V+6))) ∧
      Exec body (generatePackedCouplingInputs boundary) (mk v S) n
        (mk v' {S with R := (Function.update S.R 110
          (cstream A w (couplingInputWords boundary t band a b i F)++S.R 110))}) := by
  let C := 6*band+11*V+6+(band*(14*V+15+(136*V+137+(33*tblC V V+6*(b-a+1)+84*V+76+((b-a)*(12*w+11)+10*w+30)))+3)+2+(6*V+6))
  let B (xs : List (Fin (A+4))) : Stacks 117 A := {S with R := Function.update S.R 110 (xs++S.R 110)}
  have hpass (negative : Bool) (xs : List (Fin (A+4))) (vi : HS 117 Q A U) :
      ∃ vf n, vf.user = vi.user ∧ n ≤ C ∧
        Exec body (packedCouplingGeneratedPass negative boundary) (mk vi (B xs)) n
          (mk vf (B (cstream A w (couplingInputOffsetWords negative boundary t band a b i band F)++xs))) := by
    obtain ⟨vf,n,hu,hn,he⟩ := packedCouplingGeneratedPass_exec (body := body) negative boundary value
      hs ht hband hi hd' ha hb hst hab hbS hfit hwide hbound vi (B xs)
      (by simpa [B] using hV)
      (by intro k
          have hk : packedLookupBankSource k ≠ 110 := by
            simp only [packedLookupBankSource]; split_ifs <;> decide
          simpa only [B,Function.update_of_ne hk] using hmeta k)
      (by intro r; have hr := originReg_range r
          have hne : originReg r ≠ 110 := by intro he; rw [he] at hr; omega
          simpa only [B,Function.update_of_ne hne] using hblank r)
      w F tail (by simpa [B] using hwidth) (by simpa [B] using hsrc)
      (by intro r hr
          have hne : r ≠ 110 := by intro he; subst r; norm_num at hr
          simpa only [B,Function.update_of_ne hne] using hlow r hr)
      (by simpa [B] using h108) (by simpa [B] using h109)
      (by simpa [B] using h116) (by simpa [B] using hz)
    refine ⟨vf,n,hu,hn,he.cast rfl ?_⟩
    apply congrArg (mk vf)
    refine Stacks.ext rfl rfl rfl ?_
    funext r
    by_cases h1 : r = 110 <;> by_cases h2 : r = 116 <;> simp_all [B,List.append_assoc]
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := binaryGuardedPackedCouplingLookup_state_exec (body := body)
    false boundary value hs ht hband hi hd' ha hb hst hab hbS (Nat.zero_le band)
    (by omega) hwide hbound v S hV hmeta hblank w F tail hwidth hsrc h108 h109
  let zero := csyms A w (maskedCouplingInputWord false boundary t band a b i 0 F)
  have he₁' : Exec body (.seq loadPackedLookupBank (.seq (packedLookupCountersFor (guardedPackedCouplingLookupCode false boundary)) packedHaloRead)) (mk v S) n₁ (mk v₁ (B zero)) := by
    convert he₁ using 1
    apply congrArg (mk v₁)
    refine Stacks.ext rfl rfl rfl ?_
    funext r
    by_cases hr : r.val < 31
    · have hne : r ≠ 110 := by intro he; subst r; norm_num at hr
      simp [B,hne,hr,hlow r hr]
    · by_cases hne : r = 110 <;> simp [B,zero,hr,hne]
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := hpass false zero v₁
  obtain ⟨v₃,n₃,hu₃,hn₃,he₃⟩ := hpass true
    (cstream A w (couplingInputOffsetWords false boundary t band a b i band F)++zero) v₂
  refine ⟨v₃,n₁+(n₂+n₃),hu₃.trans (hu₂.trans hu₁),by dsimp only [C] at hn₂ hn₃; omega,
    (Exec.seq he₁' (Exec.seq he₂ he₃)).cast rfl ?_⟩
  apply congrArg (mk v₃)
  simp [B,zero,couplingInputWords_split,cstream,List.append_assoc]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
