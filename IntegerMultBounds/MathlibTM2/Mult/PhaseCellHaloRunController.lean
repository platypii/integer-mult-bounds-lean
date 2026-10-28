module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHaloRunHost
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellOriginRelease

/-! Generate run metadata from raw scalar table values and release the table bank. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

/-- Phase-scan constants and the initial cursor are computed, rather than assumed. -/
def haloRunInitializeCode : TblCode 16 :=
  tblBlock 16 [.sub 1 0 6,.add 6 6 6,.zero 7,.inc 7,.sub 1 0 15,.inc 15] (.zero 3)

def haloRunPreparedCode (flags : Bool) : TblCode 16 :=
  haloRunInitializeCode ;; haloRunCode flags

theorem haloRunPreparedCode_do {A W w s t band a b : ℕ} (flags : Bool) (st : TblSt 16 A)
    (hs' : st.val 0 = s) (ht : st.val 1 = t) (hband : st.val 2 = band)
    (hz : st.val 12 = 0) (ha : st.val 13 = a) (hb : st.val 14 = b)
    (has : a ≤ s) (hbs : b ≤ s) (hs : 0 < s) (hst : s < t)
    (hwide : 8*(t+1)^2+2*band+8 < 2^W) :
    TblDo A W w (haloRunPreparedCode flags) st (fun st' =>
      st'.acc = (runPairStream flags A w
        (IntervalRunMask.runs 0 s (haloRunIntervals s t band a b))).reverse++st.acc)
      (40*(t-s+1)+13) := by
  let ready : TblSt 16 A := ⟨Function.update (Function.update (Function.update
    (Function.update st.val 6 (2*(t-s))) 7 1) 15 (t-s+1)) 3 0,st.acc⟩
  have hsmall : 2*t+2 < 2^W := by nlinarith only [hwide]
  have hW : W ≠ 0 := by intro he; subst W; simp at hsmall
  have hi : TblDo A W w haloRunInitializeCode st (fun st' => st' = ready) 7 := by
    apply TblDo.block
    · simp [tblFitsList,TblIns.fits,TblIns.exact,hs',ht,hW]
      omega
    · simp [tblExactList,TblIns.exact,ready,hs',ht,Function.update_idem,two_mul]
  apply (hi.seq (K₂ := 40*(t-s+1)+6) (fun st₁ he => by
    subst he
    exact haloRunCode_do flags ready
      (by simp [ready,hs']) (by simp [ready,hband]) (by simp [ready])
      (by simp [ready]) (by simp [ready]) (by simp [ready,hz])
      (by simp [ready]) (by simp [ready,ha]) (by simp [ready,hb]) has hbs hs hst hwide)).mono
  · intro st' hh; exact hh
  · omega

variable {Q A : ℕ} {U P : Type} {body : P → Pr P 117 Q A U}

def haloRunReleasedController (flags : Bool) (out : Fin 117) : Pr P 117 Q A U :=
  .seq (tblMapHost originReg (haloRunPreparedCode flags) out
    (fun sym => bitSymbol (pairRe sym))) releaseOriginBank

theorem haloRunReleasedController_exec {W w s t band a b : ℕ} (flags : Bool) (out : Fin 117)
    (hout : 31 ≤ out.val) (st : TblSt 16 A)
    (hs' : st.val 0 = s) (ht : st.val 1 = t) (hband : st.val 2 = band)
    (hz : st.val 12 = 0) (ha : st.val 13 = a) (hb : st.val 14 = b)
    (has : a ≤ s) (hbs : b ≤ s) (hs : 0 < s) (hst : s < t)
    (hwide : 8*(t+1)^2+2*band+8 < 2^W) (hw : w ≤ W)
    (hbound : ∀ r, st.val r < 2^W) (hacc : st.acc = [])
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hS : tblHolds originReg S (tblRho W (List.replicate W tick) (List.replicate w tick) st)) :
    ∃ v' m, v'.user = v.user ∧
      m ≤ (40*(t-s+1)+13)*tblC W w+
        2*((2*(haloRunIntervals s t band a b).length+1)*w)+62*W+65 ∧
      Exec body (haloRunReleasedController flags out) (mk v S) m
        (mk v' {S with R := fun r => if r.val < 31 then [] else if r = out then
          ((runPairStream flags A w (IntervalRunMask.runs 0 s (haloRunIntervals s t band a b))).map
            (fun sym => bitSymbol (pairRe sym)))++S.R r else S.R r}) := by
  have hsep : ∀ r, originReg r ≠ out := by
    intro r he
    have := originReg_range r
    rw [he] at this
    omega
  have hcode := haloRunPreparedCode_do (A := A) (W := W) (w := w) flags st
    hs' ht hband hz ha hb has hbs hs hst hwide
  obtain ⟨v₁,S₁,m₁,st',hpost,hu₁,hm₁,he₁,ho₁,hh₁,hi₁,hout₁,hl₁,hf₁⟩ :=
    tblMapHost_runs (body := body) (fun sym => bitSymbol (pairRe sym)) originReg_injective hsep
      (List.replicate W tick) (List.replicate w tick) (by simp) (by simp) hw hcode hbound v S hS
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := releaseOriginBank_width_exec (body := body) W w hw st'.val v₁ S₁ hh₁
  have hm₁' : m₁ ≤ (40*(t-s+1)+13)*tblC W w+
      2*((2*(haloRunIntervals s t band a b).length+1)*w)+2 := by
    simpa [hpost,hacc,runPairStream_length,IntervalRunMask.length_runs] using hm₁
  have ho₁' : S₁.R out =
      ((runPairStream flags A w (IntervalRunMask.runs 0 s (haloRunIntervals s t band a b))).map
        (fun sym => bitSymbol (pairRe sym)))++S.R out := by
    simpa [hpost,hacc,List.map_reverse] using ho₁
  refine ⟨v₂,m₁+m₂,hu₂.trans hu₁,by omega,(Exec.seq he₁ he₂).cast rfl ?_⟩
  apply congrArg (mk v₂)
  refine Stacks.ext hi₁ hout₁ hl₁ ?_
  funext r
  by_cases hr : r.val < 31
  · simp [hr]
  by_cases hro : r = out
  · subst r; simp [hr,ho₁']
  have hsep' : ∀ x, originReg x ≠ r := by
    intro x he
    have := originReg_range x
    rw [he] at this
    omega
  simp [hr,hro,hf₁ r hro hsep']

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
