module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInputShiftWordPass
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupOps

/-! Generate, use and release exact input-conversion controls in the caller bank. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 303 Q A U}

def inputShiftBatch (restore : Bool) : Pr P 303 Q A U :=
  .seq prepareInputShiftHeaders
    (.seq (inputShiftWordPass restore) (clearWords ((List.finRange 3).map inputShiftPort)))

theorem inputShiftBatch_exec (hA : 4 ≤ A) (restore : Bool) {W p u l target s t a b : ℕ} [NeZero s]
    (wl : List (Fin (A+4))) (hwl : wl.length = W) (st : TblSt 25 A)
    (h0 : st.val 0 = p) (h1 : st.val 1 = u) (h2 : st.val 2 = l) (h3 : st.val 3 = target)
    (h4 : st.val 4 = s) (h5 : st.val 5 = t) (h6 : st.val 6 = a) (h7 : st.val 7 = b)
    (hzero : ∀ i : Fin 25, 8 ≤ i.val → st.val i = 0)
    (hst : s < t) (ha : a ≤ s) (hb : b ≤ s) (hband : PhaseCellBand.width p u ≤ s)
    (hbandRoom : 64*(p+1)+u < 2^W)
    (hgeometryRoom : 8*(t+1)^2+2*PhaseCellBand.width p u+8 < 2^W)
    (hprecisionRoom : inversePrecisionRoom p l target (haloBoundary s t (PhaseCellBand.width p u) a b).card
      (PhaseCellBand.width p u) < 2^W) (hfit : ∀ i, st.val i < 2^W)
    (v : HS 303 Q A U) (S : Stacks 303 A) (hS : tblHolds familyInverseScalarReg S (tblRho W wl [] st))
    (xs : List GaussianInt) (hxs : ∀ z ∈ xs, ‖value p z‖ ≤ 1)
    (hsrc : S.R 110 = cstream A (8*inverseExecutionExponent p l target
      (haloBoundary s t (PhaseCellBand.width p u) a b).card (PhaseCellBand.width p u)+8)
      (inputShiftSource restore (4*inverseExecutionExponent p l target
        (haloBoundary s t (PhaseCellBand.width p u) a b).card (PhaseCellBand.width p u)-p-1) xs))
    (hblank : ∀ r ∈ ([0,1,2,3,4,5,6,7,8,9,10] : List (Fin 303)), S.R r = []) :
    let E := inverseExecutionExponent p l target (haloBoundary s t (PhaseCellBand.width p u) a b).card (PhaseCellBand.width p u)
    let w := 8*E+8
    let d := 4*E-p-1
    ∃ v' n, v'.user = v.user ∧
      n ≤ (inverseScalarAtoms p s t u a b+22)*tblC W 0+16*w+33*W+34+xs.length*(20*w+44) ∧
      Exec body (inputShiftBatch restore) (mk v S) n
        (mk v' {S with R := Function.update S.R 110 (cstream A w (inputShiftResult restore d xs))}) := by
  dsimp only
  let E := inverseExecutionExponent p l target (haloBoundary s t (PhaseCellBand.width p u) a b).card (PhaseCellBand.width p u)
  let w := 8*E+8
  let d := 4*E-p-1
  have hwidth : p+1+d+5 ≤ w := by dsimp [w,d,E,inverseExecutionExponent]; omega
  obtain ⟨v₁,S₁,n₁,hu₁,hn₁,he₁,_,hi,ho,hL,hheaders,hoff⟩ :=
    prepareInputShiftHeaders_exec (body := body) wl hwl st h0 h1 h2 h3 h4 h5 h6 h7
      hzero hst ha hb hband hbandRoom hgeometryRoom hprecisionRoom hfit v S hS
  have hports (i : Fin 3) : S.R (inputShiftPort i) = [] := by
    apply hblank
    fin_cases i <;> decide
  have hsep (r : Fin 303) (hr : r ∈ ([3,4,5,6,7,8,9,10,110] : List (Fin 303))) :
      ∀ i, inputShiftPort i ≠ r := by
    intro i he
    have hv := congrArg Fin.val he
    have hil := i.isLt
    simp only [inputShiftPort] at hv
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> norm_num at hv <;> omega
  have hh (i : Fin 3) : S₁.R (inputShiftPort i) = List.replicate (inputShiftHeaderValues w d i) tick := by
    simpa only [hports,List.append_nil] using hheaders i
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := inputShiftWordPass_exec (body := body) hA restore p d w hwidth xs hxs
    v₁ S₁ ((hoff 110 (hsep 110 (by simp))).trans hsrc) hh (by
      intro r hr
      exact (hoff r (hsep r (by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hr ⊢
        rcases hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp))).trans
        (hblank r (by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hr ⊢
        rcases hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp)))
  let S₂ : Stacks 303 A := {S₁ with R := Function.update S₁.R 110 (cstream A w (inputShiftResult restore d xs))}
  let rs := (List.finRange 3).map inputShiftPort
  have hne (i : Fin 3) : inputShiftPort i ≠ (110 : Fin 303) := hsep 110 (by simp) i
  have hh₂ (i : Fin 3) : S₂.R (inputShiftPort i) = List.replicate (inputShiftHeaderValues w d i) tick := by
    change Function.update S₁.R 110 _ (inputShiftPort i) = _
    rw [Function.update_of_ne (hne i),hh]
  have hsum : (rs.map fun r => (S₂.R r).length).sum = 2*w := by
    simp only [rs,List.map_map,Function.comp_def,hh₂,List.length_replicate]
    simp [inputShiftHeaderValues,List.finRange_succ]
    dsimp [w,d,E,inverseExecutionExponent]
    omega
  obtain ⟨v₃,hu₃,he₃⟩ := clearWords_exec (body := body) rs ((List.nodup_finRange 3).map inputShiftPort_injective) v₂ S₂
  have hfinal : {S₂ with R := fun r => if r ∈ rs then [] else S₂.R r} =
      {S with R := Function.update S.R 110 (cstream A w (inputShiftResult restore d xs))} := by
    apply Stacks.ext
    · exact hi
    · exact ho
    · exact hL
    funext r
    by_cases hr : r ∈ rs
    · obtain ⟨i,_,rfl⟩ := List.mem_map.mp hr
      simp only [hr,ite_true,Function.update_of_ne (hne i),hports]
    · have hp : ∀ i, inputShiftPort i ≠ r := by
        intro i he
        exact hr (List.mem_map.mpr ⟨i,List.mem_finRange i,he⟩)
      simp only [hr,ite_false,S₂]
      by_cases he : r = 110
      · subst r; simp only [Function.update_self]
      · simp only [Function.update_of_ne he]
        exact hoff r hp
  have he := (Exec.seq he₁ (Exec.seq he₂ he₃)).cast rfl (congrArg (mk v₃) hfinal)
  refine ⟨v₃,_,hu₃.trans (hu₂.trans hu₁),?_,he⟩
  simp only [hsum,rs,List.length_map,List.length_finRange]
  dsimp [w,E] at hn₂ ⊢
  omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
