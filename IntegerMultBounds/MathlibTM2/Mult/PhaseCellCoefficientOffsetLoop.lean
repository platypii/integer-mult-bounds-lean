module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellAppendSelectedCoefficient
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCountedLoop

/-! One runtime-counted pass generates every positive or negative band offset.
The physical coefficient stream is reversed by prefix emission, with aliases retained. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellRationalArgs

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def signedCoefficientWord (negative : Bool) (P q s t u band i d : ℕ) : GaussianInt :=
  rationalWord q (PhaseCellCrossCell.entry P s t u band i ((i : ℤ)+couplingOffset negative d))

def offsetCoefficientWords (negative : Bool) (P q s t u band i count : ℕ) : List GaussianInt :=
  (List.range count).reverse.map (fun n => signedCoefficientWord negative P q s t u band i (n+1))

def coefficientOffsetStep (negative : Bool) : Pr P₀ 117 Q A U :=
  .seq (.act (.push (.rt 108) (fun _ => tick) .done)) (appendSelectedCoefficient negative)

def coefficientOffsetLoop (negative : Bool) : Pr P₀ 117 Q A U :=
  countedLoop 116 (coefficientOffsetStep negative)

def coefficientOffsetLoopCost (P q w s t u band i : ℕ) : ℕ :=
  band*(appendSelectedCoefficientCost P q w s t u band i band+4)+2

theorem coefficientOffsetLoop_exec {w q P s t u band i : ℕ} (negative : Bool)
    (hs0 : 0 < s) (hst : s < t) (hP : 13 ≤ P) (hi : i < s)
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hPsrc : (S.R 114).length = P) (hqsrc : (S.R 112).length = q)
    (hsSrc : (S.R 97).length = s) (htSrc : (S.R 98).length = t)
    (huSrc : (S.R 99).length = u) (hbSrc : (S.R 100).length = band)
    (hiSrc : (S.R 107).length = i) (h108 : S.R 108 = [])
    (h115 : S.R 115 = []) (h104 : S.R 104 = []) (hwsrc : (S.R 94).length = w) (h106 : S.R 106 = [])
    (hblank : ∀ r : Fin 117, r.val < 63 → S.R r = [])
    (hcount : (S.R 116).length = band) :
    ∃ v' m, v'.user = v.user ∧ m ≤ coefficientOffsetLoopCost P q w s t u band i ∧
      Exec body (coefficientOffsetLoop negative) (mk v S) m
        (mk v' {S with R := Function.update (Function.update (Function.update S.R
          108 (List.replicate band tick)) 111
          (cstream A w (offsetCoefficientWords negative P q s t u band i band)++S.R 111)) 116 []}) := by
  let B (j : ℕ) (cs : List (Fin (A+4))) : Stacks 117 A :=
    {S with R := Function.update (Function.update (Function.update S.R 108 (List.replicate j tick))
      111 (cstream A w (offsetCoefficientWords negative P q s t u band i j)++S.R 111)) 116 cs}
  let Inv (j : ℕ) (Si : Stacks 117 A) : Prop := ∃ cs, Si = B j cs
  have hstable : ∀ j Si xs, Inv j Si → Inv j {Si with R := Function.update Si.R 116 xs} := by
    rintro j Si xs ⟨cs,rfl⟩
    refine ⟨xs,?_⟩
    refine Stacks.ext ?_ ?_ ?_ ?_
    · rfl
    · rfl
    · rfl
    · funext r
      by_cases hr : r = 116 <;> simp [B,hr]
  have hstep : ∀ j < band, ∀ (vi : HS 117 Q A U) Si, Inv j Si →
      ∃ vf Sf m, vf.user = vi.user ∧ m ≤ appendSelectedCoefficientCost P q w s t u band i band+1 ∧
        Exec body (coefficientOffsetStep negative) (mk vi Si) m (mk vf Sf) ∧
        Sf.R 116 = Si.R 116 ∧ Inv (j+1) Sf := by
    rintro j hj vi Si ⟨cs,rfl⟩
    let Sj : Stacks 117 A := {B j cs with R := Function.update (B j cs).R 108 (tick::(B j cs).R 108)}
    have hpush : Exec body (.act (.push (.rt 108) (fun _ => tick) .done))
        (mk vi (B j cs)) 1 (mk vi Sj) := by
      simpa [Sj,Action.run,update_rt] using
        (Exec.act (body := body) (.push (.rt 108) (fun _ => tick) .done) (mk vi (B j cs)))
    obtain ⟨vf,m,hu,hm,he⟩ := appendSelectedCoefficient_exec (body := body) (w := w) (q := q) (P := P) (s := s)
      (t := t) (u := u) (band := band) (i := i) (d := j+1) negative hs0 hst hP (by omega) hi vi Sj
      (by simpa [Sj,B] using hPsrc)
      (by simpa [Sj,B] using hqsrc)
      (by simpa [Sj,B] using hsSrc)
      (by simpa [Sj,B] using htSrc)
      (by simpa [Sj,B] using huSrc)
      (by simpa [Sj,B] using hbSrc)
      (by simpa [Sj,B] using hiSrc)
      (by simp [Sj,B]) (by simpa [Sj,B] using h115) (by simpa [Sj,B] using h104)
      (by simpa [Sj,B] using hwsrc) (by simpa [Sj,B] using h106) (by
        intro r hr
        have h108' : r ≠ 108 := by intro he; subst r; norm_num at hr
        have h111' : r ≠ 111 := by intro he; subst r; norm_num at hr
        have h116' : r ≠ 116 := by intro he; subst r; norm_num at hr
        simpa [Sj,B,h108',h111',h116'] using hblank r hr)
    let word := signedCoefficientWord negative P q s t u band i (j+1)
    have hstate : {Sj with R := Function.update Sj.R 111 (csyms A w word++Sj.R 111)} = B (j+1) cs := by
      refine Stacks.ext ?_ ?_ ?_ ?_
      · rfl
      · rfl
      · rfl
      · funext r
        by_cases h108' : r = 108
        · subst r
          simp [Sj,B,List.replicate_succ]
        by_cases h111' : r = 111
        · subst r
          simp [Sj,B,offsetCoefficientWords,List.range_succ,cstream,List.flatMap_append,
            List.reverse_append,← List.append_assoc,word]
        by_cases h116' : r = 116
        · subst r; simp [Sj,B]
        simp [Sj,B,h108',h111',h116']
    refine ⟨vf,B (j+1) cs,1+m,hu,?_,?_,by simp [B],⟨cs,rfl⟩⟩
    · have hh := appendSelectedCoefficientCost_mono P q w s t u band i (show j+1 ≤ band by omega)
      omega
    · exact (Exec.seq hpush he).cast rfl (congrArg (mk vf) hstate)
  have hInv : Inv 0 S := by
    refine ⟨S.R 116,?_⟩
    refine Stacks.ext ?_ ?_ ?_ ?_
    · rfl
    · rfl
    · rfl
    · funext r
      by_cases h108' : r = 108 <;> by_cases h111' : r = 111 <;> by_cases h116' : r = 116 <;>
        simp [B,h108',h111',h116',h108,offsetCoefficientWords,cstream]
  obtain ⟨v',S',m,hu,hm,he,hc,hI⟩ := countedLoop_exec (body := body) 116
    (coefficientOffsetStep negative) band (appendSelectedCoefficientCost P q w s t u band i band+1)
    Inv hstable hstep v S hcount hInv
  obtain ⟨cs,rfl⟩ := hI
  have hcs : cs = [] := by simpa [B] using hc
  subst cs
  exact ⟨v',m,hu,by simpa [coefficientOffsetLoopCost,Nat.add_assoc] using hm,he⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
