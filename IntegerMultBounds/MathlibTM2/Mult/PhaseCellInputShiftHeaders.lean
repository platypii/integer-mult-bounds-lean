module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPrepareInputShift
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFamilyInverseCallerWorkspace
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellClearInverseScalars
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRoundHeaderFrame

/-! Generate source-conversion counters while restoring the ordinary inverse scalar bank. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

def inputShiftPort (i : Fin 3) : Fin 303 := ⟨i.val,by omega⟩
def inputShiftHeaderSource : Fin 3 → Fin 25 := ![20,15,16]
def inputShiftHeaderValues (w d : ℕ) : Fin 3 → ℕ := ![w,d,w-d]
def inputShiftHeaderAssignments : List (Fin 25 × Fin 303) :=
  (List.finRange 3).map (fun i => (inputShiftHeaderSource i,inputShiftPort i))

theorem inputShiftPort_injective : Function.Injective inputShiftPort := by
  intro i j he
  exact Fin.ext (congrArg (fun k : Fin 303 => k.val) he)

theorem inputShiftScalar_port (i : Fin 3) (r : TblR 25) : familyInverseScalarReg r ≠ inputShiftPort i := by
  have h := familyInverseScalarReg_core r (⟨i.val,by omega⟩ : Fin 263)
  simpa [inputShiftPort,familyInverseScalarReg,familyInverseCoreReg,show i.val < 224 by omega] using h

theorem inputShiftHeaderCost_eq (W w d : ℕ) (hd : d ≤ w) :
    unaryCopiesCost W (inputShiftHeaderValues w d)
      ((List.finRange 3).map (fun i => (i,inputShiftPort i))) = 12*w+33*W+19 := by
  simp [unaryCopiesCost,inputShiftHeaderValues,List.finRange_succ]
  omega

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 303 Q A U}

def prepareInputShiftHeaders : Pr P 303 Q A U :=
  .seq (tblCompile familyInverseScalarReg tblPrepareInputShift)
    (.seq (tblUnaryCopies familyInverseScalarReg inputShiftHeaderAssignments)
      (tblCompile familyInverseScalarReg tblClearInverseScalars))

theorem prepareInputShiftHeaders_exec {W p u l target s t a b : ℕ} [NeZero s]
    (wl : List (Fin (A+4))) (hwl : wl.length = W) (st : TblSt 25 A)
    (h0 : st.val 0 = p) (h1 : st.val 1 = u) (h2 : st.val 2 = l) (h3 : st.val 3 = target)
    (h4 : st.val 4 = s) (h5 : st.val 5 = t) (h6 : st.val 6 = a) (h7 : st.val 7 = b)
    (hzero : ∀ i : Fin 25, 8 ≤ i.val → st.val i = 0)
    (hst : s < t) (ha : a ≤ s) (hb : b ≤ s) (hband : PhaseCellBand.width p u ≤ s)
    (hbandRoom : 64*(p+1)+u < 2^W)
    (hgeometryRoom : 8*(t+1)^2+2*PhaseCellBand.width p u+8 < 2^W)
    (hprecisionRoom : inversePrecisionRoom p l target (haloBoundary s t (PhaseCellBand.width p u) a b).card
      (PhaseCellBand.width p u) < 2^W) (hfit : ∀ i, st.val i < 2^W)
    (v : HS 303 Q A U) (S : Stacks 303 A) (hS : tblHolds familyInverseScalarReg S (tblRho W wl [] st)) :
    let E := inverseExecutionExponent p l target (haloBoundary s t (PhaseCellBand.width p u) a b).card (PhaseCellBand.width p u)
    let w := 8*E+8
    let d := 4*E-p-1
    ∃ v' S' n, v'.user = v.user ∧
      n ≤ (inverseScalarAtoms p s t u a b+22)*tblC W 0+12*w+33*W+19 ∧
      Exec body prepareInputShiftHeaders (mk v S) n (mk v' S') ∧
      tblHolds familyInverseScalarReg S' (tblRho W wl [] st) ∧
      S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧
      (∀ i, S'.R (inputShiftPort i) = List.replicate (inputShiftHeaderValues w d i) tick++S.R (inputShiftPort i)) ∧
      ∀ k, (∀ i, inputShiftPort i ≠ k) → S'.R k = S.R k := by
  dsimp only
  let E := inverseExecutionExponent p l target (haloBoundary s t (PhaseCellBand.width p u) a b).card (PhaseCellBand.width p u)
  let w := 8*E+8
  let d := 4*E-p-1
  have hd : d ≤ w := by dsimp [d,w,E,inverseExecutionExponent]; omega
  have hc := tblPrepareInputShift_do (e := 0) st h0 h1 h2 h3 h4 h5 h6 h7 hst ha hb hband
    hbandRoom hgeometryRoom hprecisionRoom hfit
  obtain ⟨z,⟨hkeep,hq,hw,hshift,hrest,hacc,hfitZ⟩,hrun⟩ :=
    hc.host (body := body) familyInverseScalarReg_injective wl [] hwl rfl (Nat.zero_le W) hfit
  have hvalue (i : Fin 3) : z.val (inputShiftHeaderSource i) = inputShiftHeaderValues w d i := by
    fin_cases i
    · exact hw
    · exact hshift
    · exact hrest
  obtain ⟨v₁,S₁,n₁,hu₁,hn₁,he₁,hh₁,hframe₁⟩ := hrun v S hS
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := tblUnaryCopies_exec (body := body) familyInverseScalarReg_injective wl [] z hfitZ
    inputShiftHeaderAssignments (by
      intro x hx r
      obtain ⟨i,_,rfl⟩ := List.mem_map.mp hx
      exact inputShiftScalar_port i r) v₁ S₁ hh₁
  let S₂ : Stacks 303 A := {S₁ with R := unaryCopiesR z.val S₁.R inputShiftHeaderAssignments}
  have hh₂ : tblHolds familyInverseScalarReg S₂ (tblRho W wl [] z) := by
    intro r
    rw [show S₂.R (familyInverseScalarReg r) = S₁.R (familyInverseScalarReg r) from
      unaryCopiesR_off z.val S₁.R _ _ (by
        intro x hx
        obtain ⟨i,_,rfl⟩ := List.mem_map.mp hx
        exact (inputShiftScalar_port i r).symm)]
    exact hh₁ r
  have hclear := tblClearInverseScalars_do (W := W) (e := 0) z st
    (fun i hi => hkeep ⟨i.val,hi⟩) hzero hacc
  obtain ⟨initial,heq,hrun₃⟩ := hclear.host (body := body) familyInverseScalarReg_injective wl [] hwl rfl (Nat.zero_le W) hfitZ
  subst initial
  obtain ⟨v₃,S₃,n₃,hu₃,hn₃,he₃,hh₃,hframe₃⟩ := hrun₃ v₂ S₂ hh₂
  have hcost : unaryCopiesCost W z.val inputShiftHeaderAssignments = 12*w+33*W+19 := by
    rw [←inputShiftHeaderCost_eq W w d hd]
    simp only [unaryCopiesCost,inputShiftHeaderAssignments,List.map_map,Function.comp_def,hvalue]
  have hheaders (i : Fin 3) : S₃.R (inputShiftPort i) =
      List.replicate (inputShiftHeaderValues w d i) tick++S.R (inputShiftPort i) := by
    rw [hframe₃.2.2.2 _ (inputShiftScalar_port i)]
    have hnd : (inputShiftHeaderAssignments.map Prod.snd).Nodup := by
      simpa only [inputShiftHeaderAssignments,List.map_map,Function.comp_def] using
        (List.nodup_finRange 3).map inputShiftPort_injective
    have hh := unaryCopiesR_at z.val S₁.R inputShiftHeaderAssignments hnd
      (inputShiftHeaderSource i,inputShiftPort i) (List.mem_map.mpr ⟨i,List.mem_finRange i,rfl⟩)
    change S₂.R (inputShiftPort i) = _ at hh
    rw [hh,hvalue,hframe₁.2.2.2 _ (inputShiftScalar_port i)]
  have hoff : ∀ k, (∀ r, familyInverseScalarReg r ≠ k) →
      (∀ i, inputShiftPort i ≠ k) → S₃.R k = S.R k := by
    intro k hr hp
    rw [hframe₃.2.2.2 k hr]
    exact (unaryCopiesR_off z.val S₁.R _ k (by
      intro x hx
      obtain ⟨i,_,rfl⟩ := List.mem_map.mp hx
      exact hp i)).trans (hframe₁.2.2.2 k hr)
  refine ⟨v₃,S₃,n₁+(n₂+n₃),hu₃.trans (hu₂.trans hu₁),?_,Exec.seq he₁ (Exec.seq he₂ he₃),hh₃,
    hframe₃.1.trans hframe₁.1,hframe₃.2.1.trans hframe₁.2.1,hframe₃.2.2.1.trans hframe₁.2.2.1,hheaders,?_⟩
  · rw [hcost] at hn₂
    dsimp [w,E] at hn₂
    simp only [List.length_nil] at hn₁ hn₃
    nlinarith only [hn₁,hn₂,hn₃]
  · intro k hk
    exact roundHeader_frame familyInverseScalarReg inputShiftPort S S₃ _ hS hh₃ hoff k hk

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
