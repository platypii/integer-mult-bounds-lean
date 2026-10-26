module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCouplingLookupCost
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCountedLoop

/-! One runtime-counted pass gathers every positive or negative band offset.
The masked input stream is reversed by prefix emission, with aliases retained. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellRationalArgs
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def maskedCouplingInputWord {s : ℕ} [NeZero s] (negative boundary : Bool)
    (t band a b i d : ℕ) (C : ZMod s → GaussianInt) : GaussianInt :=
  let T := if boundary then haloBoundary s t band a b else haloInterior s t band a b
  let j : ZMod s := (i : ZMod s)+(couplingOffset negative d : ZMod s)
  if j ∈ T then C j else 0

def couplingInputOffsetWords {s : ℕ} [NeZero s] (negative boundary : Bool)
    (t band a b i count : ℕ) (C : ZMod s → GaussianInt) : List GaussianInt :=
  (List.range count).reverse.map (fun n => maskedCouplingInputWord negative boundary t band a b i (n+1) C)

def couplingInputOffsetStep (negative boundary : Bool) : Pr P₀ 117 Q A U :=
  .seq (.act (.push (.rt 105) (fun _ => tick) .done)) (closedCouplingLookup negative boundary)

def couplingInputOffsetLoop (negative boundary : Bool) : Pr P₀ 117 Q A U :=
  countedLoop 116 (couplingInputOffsetStep negative boundary)

def couplingInputOffsetLoopCost (P q w s t u band a b i : ℕ) : ℕ :=
  band*(couplingLookupRowCost P q w s t u band a b i+4)+2

theorem couplingInputOffsetLoop_exec {P q w s t u band a b i : ℕ} [NeZero s]
    (negative boundary : Bool) (hA : 4 ≤ A)
    (hst : s < t) (haS : a ≤ s) (hbS : b ≤ s) (hbandS : band ≤ s) (hi : i < s)
    (C : ZMod s → GaussianInt) (tail : List (Fin (A+4)))
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hPsrc : (S.R 114).length = P) (hqsrc : (S.R 112).length = q) (husrc : (S.R 99).length = u)
    (hsSrc : (S.R 97).length = s) (htSrc : (S.R 98).length = t)
    (hbandSrc : (S.R 100).length = band) (hiSrc : (S.R 107).length = i) (h105 : S.R 105 = [])
    (haSrc : (S.R 101).length = a) (hbSrc : (S.R 103).length = b)
    (hwsrc : (S.R 94).length = w) (h115 : S.R 115 = []) (h104 : S.R 104 = [])
    (h109 : S.R 109 = []) (h106 : S.R 106 = []) (h108 : S.R 108 = [])
    (hblank : ∀ r : Fin 117, r.val < 31 → S.R r = [])
    (hsrc : S.R 92 = cstream A w (chirpLine s C)++tail) (hcount : (S.R 116).length = band) :
    ∃ v' m, v'.user = v.user ∧ m ≤ couplingInputOffsetLoopCost P q w s t u band a b i ∧
      Exec body (couplingInputOffsetLoop negative boundary) (mk v S) m
        (mk v' {S with R := Function.update (Function.update (Function.update S.R
          105 (List.replicate band tick)) 110
          (cstream A w (couplingInputOffsetWords negative boundary t band a b i band C)++S.R 110)) 116 []}) := by
  let B (j : ℕ) (cs : List (Fin (A+4))) : Stacks 117 A :=
    {S with R := Function.update (Function.update (Function.update S.R 105 (List.replicate j tick))
      110 (cstream A w (couplingInputOffsetWords negative boundary t band a b i j C)++S.R 110)) 116 cs}
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
      ∃ vf Sf m, vf.user = vi.user ∧ m ≤ couplingLookupRowCost P q w s t u band a b i+1 ∧
        Exec body (couplingInputOffsetStep negative boundary) (mk vi Si) m (mk vf Sf) ∧
        Sf.R 116 = Si.R 116 ∧ Inv (j+1) Sf := by
    rintro j hj vi Si ⟨cs,rfl⟩
    let Sj : Stacks 117 A := {B j cs with R := Function.update (B j cs).R 105 (tick::(B j cs).R 105)}
    have hpush : Exec body (.act (.push (.rt 105) (fun _ => tick) .done))
        (mk vi (B j cs)) 1 (mk vi Sj) := by
      simpa [Sj,Action.run,update_rt] using
        (Exec.act (body := body) (.push (.rt 105) (fun _ => tick) .done) (mk vi (B j cs)))
    obtain ⟨vf,m,hu,hm,he⟩ := closedCouplingLookup_exec (body := body) (P := P) (q := q) (w := w)
      (s := s) (t := t) (u := u) (band := band) (a := a) (b := b) (i := i) (d := j+1)
      negative boundary hA hst haS hbS hbandS hi (by omega) C tail vi Sj
      (by simpa [Sj,B] using hPsrc)
      (by simpa [Sj,B] using hqsrc)
      (by simpa [Sj,B] using husrc)
      (by simpa [Sj,B] using hsSrc)
      (by simpa [Sj,B] using htSrc)
      (by simpa [Sj,B] using hbandSrc)
      (by simpa [Sj,B] using hiSrc)
      (by simp [Sj,B])
      (by simpa [Sj,B] using haSrc)
      (by simpa [Sj,B] using hbSrc)
      (by simpa [Sj,B] using hwsrc)
      (by simpa [Sj,B] using h115)
      (by simpa [Sj,B] using h104)
      (by simpa [Sj,B] using h109)
      (by simpa [Sj,B] using h106)
      (by simpa [Sj,B] using h108)
      (by intro r hr
          have h105' : r ≠ 105 := by intro he; subst r; norm_num at hr
          have h110 : r ≠ 110 := by intro he; subst r; norm_num at hr
          have h116' : r ≠ 116 := by intro he; subst r; norm_num at hr
          simpa [Sj,B,h105',h110,h116'] using hblank r hr)
      (by simpa [Sj,B] using hsrc)
    let word := maskedCouplingInputWord negative boundary t band a b i (j+1) C
    have hstate : {Sj with R := Function.update Sj.R 110 (csyms A w word++Sj.R 110)} = B (j+1) cs := by
      refine Stacks.ext ?_ ?_ ?_ ?_
      · rfl
      · rfl
      · rfl
      · funext r
        by_cases h105' : r = 105
        · subst r
          simp [Sj,B,List.replicate_succ]
        by_cases h110' : r = 110
        · subst r
          simp [Sj,B,couplingInputOffsetWords,List.range_succ,cstream,List.flatMap_append,
            List.reverse_append,← List.append_assoc,word,maskedCouplingInputWord]
        by_cases h116' : r = 116
        · subst r; simp [Sj,B]
        simp [Sj,B,h105',h110',h116']
    refine ⟨vf,B (j+1) cs,1+m,hu,?_,?_,by simp [B],⟨cs,rfl⟩⟩
    · have hh := closedCouplingLookupCost_le negative P q w s t u band a b i (j+1)
        (NeZero.pos s) (by omega)
      omega
    · exact (Exec.seq hpush he).cast rfl (congrArg (mk vf) hstate)
  have hInv : Inv 0 S := by
    refine ⟨S.R 116,?_⟩
    refine Stacks.ext ?_ ?_ ?_ ?_
    · rfl
    · rfl
    · rfl
    · funext r
      by_cases h105' : r = 105 <;> by_cases h110' : r = 110 <;> by_cases h116' : r = 116 <;>
        simp [B,h105',h110',h116',h105,couplingInputOffsetWords,cstream]
  obtain ⟨v',S',m,hu,hm,he,hc,hI⟩ := countedLoop_exec (body := body) 116
    (couplingInputOffsetStep negative boundary) band (couplingLookupRowCost P q w s t u band a b i+1)
    Inv hstable hstep v S hcount hInv
  obtain ⟨cs,rfl⟩ := hI
  have hcs : cs = [] := by simpa [B] using hc
  subst cs
  exact ⟨v',m,hu,by simpa [couplingInputOffsetLoopCost,Nat.add_assoc] using hm,he⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
