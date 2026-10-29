module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedCouplingOffsetStep

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

def packedCouplingOffsetLoop {P U : Type} {Q A : ℕ} (negative boundary : Bool) : Pr P 117 Q A U :=
  countedLoop 116 (packedCouplingOffsetStep negative boundary)

theorem packedCouplingOffsetLoop_exec {P U : Type} {Q A V s t band a b i : ℕ} [NeZero s]
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
    (h108 : S.R 108 = []) (h109 : S.R 109 = []) (hcount : (S.R 116).length = band) :
    ∃ v' n, v'.user = v.user ∧
      n ≤ band*(14*V+15+(136*V+137+(33*tblC V V+6*(b-a+1)+84*V+76+((b-a)*(12*w+11)+10*w+30)))+3)+2 ∧
      Exec body (packedCouplingOffsetLoop negative boundary) (mk v S) n
        (mk v' {S with R := Function.update (Function.update (Function.update S.R
          105 (binSyms V band)) 110
          (cstream A w (couplingInputOffsetWords negative boundary t band a b i band F)++S.R 110)) 116 []}) := by
  let B (j : ℕ) (cs : List (Fin (A+4))) : Stacks 117 A :=
    {S with R := Function.update (Function.update (Function.update S.R 105 (binSyms V j))
      110 (cstream A w (couplingInputOffsetWords negative boundary t band a b i j F)++S.R 110)) 116 cs}
  let Inv (j : ℕ) (Si : Stacks 117 A) : Prop := ∃ cs, Si = B j cs
  have hstable : ∀ j Si xs, Inv j Si → Inv j {Si with R := Function.update Si.R 116 xs} := by
    rintro j Si xs ⟨cs,rfl⟩
    refine ⟨xs,?_⟩
    refine Stacks.ext (by rfl) (by rfl) (by rfl) ?_
    funext r
    by_cases hr : r = 116 <;> simp [B,hr]
  have hstep : ∀ j < band, ∀ (vi : HS 117 Q A U) Si, Inv j Si →
      ∃ vf Sf m, vf.user = vi.user ∧
        m ≤ 14*V+15+(136*V+137+(33*tblC V V+6*(b-a+1)+84*V+76+((b-a)*(12*w+11)+10*w+30))) ∧
        Exec body (packedCouplingOffsetStep negative boundary) (mk vi Si) m (mk vf Sf) ∧
        Sf.R 116 = Si.R 116 ∧ Inv (j+1) Sf := by
    rintro j hj vi Si ⟨cs,rfl⟩
    let valuej := Function.update value 105 j
    have hboundj : ∀ k, valuej (packedLookupBankSource k) < 2^V := by
      intro k
      by_cases hk : packedLookupBankSource k = 105
      · simp only [valuej,hk,Function.update_self]; omega
      · simpa only [valuej,Function.update_of_ne hk] using hbound k
    have hmetaj : ∀ k, (B j cs).R (packedLookupBankSource k) = binSyms V (valuej (packedLookupBankSource k)) := by
      intro k
      have hr : packedLookupBankSource k ≠ 110 ∧ packedLookupBankSource k ≠ 116 := by
        simp only [packedLookupBankSource]; split_ifs <;> decide
      by_cases hk : packedLookupBankSource k = 105
      · simp [B,valuej,hk]
      · simpa only [B,valuej,Function.update_of_ne hr.1,Function.update_of_ne hr.2,Function.update_of_ne hk] using hmeta k
    obtain ⟨vf,m,hu,hm,he⟩ := packedCouplingOffsetStep_exec (body := body) (d := j) negative boundary valuej
      (by simpa [valuej] using hs) (by simpa [valuej] using ht)
      (by simpa [valuej] using hband) (by simpa [valuej] using hi) (by simp [valuej])
      (by simpa [valuej] using ha) (by simpa [valuej] using hb)
      hst hab hbS (by omega) (by omega) hwide hboundj vi (B j cs)
      (by simpa [B] using hV) hmetaj
      (by intro r; have hr := originReg_range r
          have h105 : originReg r ≠ 105 := by intro he; rw [he] at hr; omega
          have h110 : originReg r ≠ 110 := by intro he; rw [he] at hr; omega
          have h116 : originReg r ≠ 116 := by intro he; rw [he] at hr; omega
          simpa only [B,Function.update_of_ne h105,Function.update_of_ne h110,Function.update_of_ne h116] using hblank r)
      w F tail (by simpa [B] using hwidth) (by simpa [B] using hsrc)
      (by intro r hr
          have h105 : r ≠ 105 := by intro he; subst r; norm_num at hr
          have h110 : r ≠ 110 := by intro he; subst r; norm_num at hr
          have h116 : r ≠ 116 := by intro he; subst r; norm_num at hr
          simpa only [B,Function.update_of_ne h105,Function.update_of_ne h110,Function.update_of_ne h116] using hlow r hr)
      (by simpa [B] using h108) (by simpa [B] using h109)
    have hstate : {B j cs with R := (fun r => if r.val < 31 then [] else if r = 110 then
          csyms A w (maskedCouplingInputWord negative boundary t band a b i (j+1) F)++(B j cs).R 110
          else if r = 105 then binSyms V (j+1) else (B j cs).R r)} = B (j+1) cs := by
      refine Stacks.ext (by rfl) (by rfl) (by rfl) ?_
      funext r
      by_cases hr : r.val < 31
      · have h105 : r ≠ 105 := by intro he; subst r; norm_num at hr
        have h110 : r ≠ 110 := by intro he; subst r; norm_num at hr
        have h116 : r ≠ 116 := by intro he; subst r; norm_num at hr
        simpa [B,hr,h105,h110,h116] using (hlow r hr).symm
      · by_cases h110 : r = 110
        · subst r
          simp [B,couplingInputOffsetWords,List.range_succ,cstream,List.reverse_append,← List.append_assoc]
        · by_cases h105 : r = 105
          · subst r; simp [B]
          · by_cases h116 : r = 116 <;> simp [B,hr,h110,h105,h116]
    refine ⟨vf,B (j+1) cs,m,hu,hm,he.cast rfl (congrArg (mk vf) hstate),by simp [B],⟨cs,rfl⟩⟩
  have hInv : Inv 0 S := by
    refine ⟨S.R 116,?_⟩
    have h105 : S.R 105 = binSyms V 0 := by simpa [packedLookupBankSource,hd'] using hmeta 8
    refine Stacks.ext (by rfl) (by rfl) (by rfl) ?_
    funext r
    by_cases h1 : r = 105 <;> by_cases h2 : r = 110 <;> by_cases h3 : r = 116 <;>
      simp_all [B,couplingInputOffsetWords,cstream]
  obtain ⟨v',S',m,hu,hm,he,hc,hI⟩ := countedLoop_exec (body := body) 116
    (packedCouplingOffsetStep negative boundary) band _ Inv hstable hstep v S hcount hInv
  obtain ⟨cs,rfl⟩ := hI
  have hcs : cs = [] := by simpa [B] using hc
  subst cs
  exact ⟨v',m,hu,hm,he⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
