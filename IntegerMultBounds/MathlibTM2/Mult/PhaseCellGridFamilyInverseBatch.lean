module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellNormalizedFamilyInverseBatch
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInputShiftSolve
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInputShiftBatchMath
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellNormalizedBatchAccuracy
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFamilyBatchRoundReady
public import IntegerMultBounds.NLogN.SchurBlockSolve

/-! The numerical batch caller executes final scaling and rounding before returning its private results. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.SchurDominance IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 303 Q A U}

noncomputable def gridFamilyInverseBatch (recovery : Bool) (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P 303 Q A U :=
  inputShiftSolve (normalizedFamilyInverseBatch recovery hR hQ)

noncomputable def gridFamilyInverseBatchCost (A W p u l s t a b target count : ℕ) [NeZero s] : ℕ :=
  2*inputShiftBatchCost W p u l target s t a b (count*s)+
    normalizedFamilyInverseBatchCost A W p u l s t a b target count

noncomputable def gridFamilyInverseBatchStockCost (A W p u l s t a b target count : ℕ) [NeZero s] : ℕ :=
  2*inputShiftBatchCost W p u l target s t a b (count*s)+
    normalizedFamilyInverseBatchStockCost A W p u l s t a b target count

theorem gridFamilyInverseBatch_spec (recovery : Bool) (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {p l s t u target a b : ℕ} [NeZero s] {α d : ℝ}
    (hp : 2 ≤ p) (hwidth : 8*p ≤ 2^u) (hα : 0 < α) (hst : s < t) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hband : PhaseCellBand.width p u ≤ s) (ha : a ≤ s) (hb : b ≤ s)
    (hpad : 2*((s/(t-s)+1)-2*PhaseCellBand.width p u) ≤ 2^l+1) :
    let B := haloBoundary s t (PhaseCellBand.width p u) a b
    let bits := boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2 B.card
    let w := executionWidth p l (initialSchurTarget p u bits 2) 2
    ∀ (Fs : List (ZMod s → GaussianInt)), (∀ F ∈ Fs, ∀ i, ‖value p (F i)‖ ≤ 1) →
    ∀ (v : HS 303 Q A U) (S : Stacks 303 A),
    ∀ (wl : List (Fin (A+4))), wl.length = inverseCallerWordWidth p u l target s t →
    tblHolds familyInverseScalarReg S (tblRho (inverseCallerWordWidth p u l target s t) wl [] (inverseInputScalars p u l target s t a b)) →
    (∀ i, S.L (familyInverseCoreReg i) = []) →
    (∀ i, i ≠ 110 → i ≠ 132 → i ≠ 246 → S.R (familyInverseCoreReg i) = []) →
    S.R 110 = cstream A w (Fs.map (chirpLine s)).flatten →
    (S.R (familyInverseCoreReg 246)).length = Fs.length → S.R 132 = [] →
    ∀ (x y : (ZMod s → GaussianInt) → ZMod s → ℝ),
    (∀ F ∈ Fs, Solves (realMatrix s t p u) (haloVertices s a b) (x F) (fun i => ((1/2 : ℂ)*value p (F i)).re)) →
    (∀ F ∈ Fs, Solves (realMatrix s t p u) (haloVertices s a b) (y F) (fun i => ((1/2 : ℂ)*value p (F i)).im)) →
    ∃ v' n, ∃ Zs : List (ZMod s → GaussianInt),
      v'.user = v.user ∧ n ≤ gridFamilyInverseBatchCost A (inverseCallerWordWidth p u l target s t) p u l s t a b target Fs.length ∧
      Exec body (gridFamilyInverseBatch recovery hR hQ) (mk v S) n
        (mk v' {S with R := (Function.update S.R 132 (cstream A (2*p+13) (Zs.map (chirpLine s)).flatten))}) ∧
      List.Forall₂ (fun F Z => PhaseCellInterface.ErrorOn (haloVertices s a b)
        (pairedCellRead p (2*p+13) (cstream A (2*p+13) (chirpLine s Z)))
          (fun i => ((2 : ℂ)^inverseNormalizationShift p)⁻¹*(⟨x F i,y F i⟩ : ℂ))
          (2/(2 : ℝ)^p+(1/(2 : ℝ)^target)/(2 : ℝ)^inverseNormalizationShift p)) Fs Zs ∧
      ∀ C, mnProgPush (gridFamilyInverseBatch (P := P) (U := U) (A := A) recovery hR hQ) ≤ C →
        (∀ f, mnProgPush (body f) ≤ C) → ∀ depth,
        ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
          (C+1)*gridFamilyInverseBatchStockCost A (inverseCallerWordWidth p u l target s t) p u l s t a b target Fs.length)
          depth (gridFamilyInverseBatch recovery hR hQ) (mk v S) n
          (mk v' {S with R := Function.update S.R 132 (cstream A (2*p+13) (Zs.map (chirpLine s)).flatten)}) := by
  dsimp only
  simp only [executionWidth,←inverseExecutionExponent_eq]
  intro Fs hF v S wl hwl hscalar hleft hblank hsource hcount houtput x y hx hy
  let E := inverseExecutionExponent p l target (haloBoundary s t (PhaseCellBand.width p u) a b).card (PhaseCellBand.width p u)
  let w := 8*E+8
  let q := 4*E
  let d := q-p-1
  let xs := (Fs.map (chirpLine s)).flatten
  let shifted : Stacks 303 A := {S with R := Function.update S.R 110 (cstream A w (xs.map (fun z => (2 : GaussianInt)^d*z)))}
  have hq : p+1+d = q := by dsimp [d,q,E,inverseExecutionExponent]; omega
  have hshift (F : ZMod s → GaussianInt) (i : ZMod s) :
      value q (inputShiftField d F i) = (1/2 : ℂ)*value p (F i) := by
    rw [←hq,inputShiftField_value]
  have hscalar₁ : tblHolds familyInverseScalarReg shifted
      (tblRho (inverseCallerWordWidth p u l target s t) wl [] (inverseInputScalars p u l target s t a b)) := by
    intro r
    have hne : familyInverseScalarReg r ≠ (110 : Fin 303) := familyInverseScalarReg_core r 110
    simpa only [shifted,Function.update_of_ne hne] using hscalar r
  have hblank₁ : ∀ i : Fin 263, i ≠ 110 → i ≠ 132 → i ≠ 246 → shifted.R (familyInverseCoreReg i) = [] := by
    intro i hi hj hk
    have hne : familyInverseCoreReg i ≠ (110 : Fin 303) := by
      intro he
      exact hi (familyInverseCoreReg_injective he)
    simpa only [shifted,Function.update_of_ne hne] using hblank i hi hj hk
  have hsmall : ∀ r ∈ ([0,1,2,3,4,5,6,7,8,9,10] : List (Fin 303)), S.R r = [] := by
    intro r hr
    have hlo : r.val ≤ 10 := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
    let i : Fin 263 := ⟨r.val,by omega⟩
    have hne (n : Fin 263) (hn : 10 < n.val) : i ≠ n := by
      intro he
      have hv := congrArg Fin.val he
      dsimp [i] at hv
      omega
    have hh := hblank i (hne 110 (by decide)) (hne 132 (by decide)) (hne 246 (by decide))
    have he : familyInverseCoreReg i = r := by
      apply Fin.ext
      simp [familyInverseCoreReg,i,show r.val < 224 by omega]
    rwa [he] at hh
  let post := fun output => ∃ Zs : List (ZMod s → GaussianInt),
    output = cstream A (2*p+13) (Zs.map (chirpLine s)).flatten ∧
    List.Forall₂ (fun F Z => PhaseCellInterface.ErrorOn (haloVertices s a b)
      (pairedCellRead p (2*p+13) (cstream A (2*p+13) (chirpLine s Z)))
        (fun i => ((2 : ℂ)^inverseNormalizationShift p)⁻¹*(⟨x F i,y F i⟩ : ℂ))
        (2/(2 : ℝ)^p+(1/(2 : ℝ)^target)/(2 : ℝ)^inverseNormalizationShift p)) Fs Zs
  have hsolve : ∀ v₁ : HS 303 Q A U, ∃ v₂ n output, v₂.user = v₁.user ∧
      n ≤ normalizedFamilyInverseBatchCost A (inverseCallerWordWidth p u l target s t) p u l s t a b target Fs.length ∧
      Exec body (normalizedFamilyInverseBatch recovery hR hQ) (mk v₁ shifted) n
        (mk v₂ {shifted with R := Function.update shifted.R 132 output}) ∧ post output ∧
      ∀ C, mnProgPush (normalizedFamilyInverseBatch (P := P) (U := U) (A := A) recovery hR hQ) ≤ C →
        (∀ f, mnProgPush (body f) ≤ C) → ∀ depth,
        ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v₁ shifted)+depth+
          (C+1)*normalizedFamilyInverseBatchStockCost A (inverseCallerWordWidth p u l target s t) p u l s t a b target Fs.length)
          depth (normalizedFamilyInverseBatch recovery hR hQ) (mk v₁ shifted) n
          (mk v₂ {shifted with R := Function.update shifted.R 132 output}) := by
    intro v₁
    have hraw := normalizedFamilyInverseBatch_spec (body := body)
      (p := p) (l := l) (s := s) (t := t) (u := u) (target := target) (a := a) (b := b)
      recovery hR hQ hA hp hwidth hα hst hu hαu hθ hgap hbudget hband ha hb hpad
    simp only [executionWidth,executionPrecision,←inverseExecutionExponent_eq] at hraw
    have hnorm : ∀ F ∈ Fs.map (inputShiftField d), ∀ i, ‖value q (F i)‖ ≤ (2 : ℝ)^2 := by
      intro G hG i
      obtain ⟨F,hFm,rfl⟩ := List.mem_map.mp hG
      rw [hshift,norm_mul]
      have hn : ‖(1/2 : ℂ)‖ = (1/2 : ℝ) := by norm_num
      rw [hn]
      have hh := hF F hFm i
      norm_num
      linarith
    have hsource₁ : shifted.R 110 = cstream A w (((Fs.map (inputShiftField d)).map (chirpLine s)).flatten)++[] := by
      simp only [shifted,Function.update_self,List.append_nil,xs,inputShiftField_flatten]
    have hcount₁ : (shifted.R (familyInverseCoreReg 246)).length = (Fs.map (inputShiftField d)).length := by
      simpa only [shifted,List.length_map,Function.update_of_ne (by decide : familyInverseCoreReg 246 ≠ (110 : Fin 303))] using hcount
    have hx₁ : ∀ F ∈ Fs.map (inputShiftField d), Solves (realMatrix s t p u) (haloVertices s a b)
        (x (inputUnshiftField d F)) (fun i => (value q (F i)).re) := by
      intro G hG
      obtain ⟨F,hFm,rfl⟩ := List.mem_map.mp hG
      simpa only [inputUnshiftField_shift,hshift] using hx F hFm
    have hy₁ : ∀ F ∈ Fs.map (inputShiftField d), Solves (realMatrix s t p u) (haloVertices s a b)
        (y (inputUnshiftField d F)) (fun i => (value q (F i)).im) := by
      intro G hG
      obtain ⟨F,hFm,rfl⟩ := List.mem_map.mp hG
      simpa only [inputUnshiftField_shift,hshift] using hy F hFm
    obtain ⟨v₂,n,Zs,hu₂,hn,he,herror,htrace⟩ := hraw (Fs.map (inputShiftField d)) hnorm v₁ shifted [] wl hwl hscalar₁ hleft hblank₁
      hsource₁ hcount₁ (by simpa only [shifted,Function.update_of_ne (by decide : (132 : Fin 303) ≠ 110)] using houtput)
      (fun F => x (inputUnshiftField d F)) (fun F => y (inputUnshiftField d F)) hx₁ hy₁
    simp only [List.length_map] at hn htrace
    refine ⟨v₂,n,_,hu₂,hn,he,⟨Zs,rfl,?_⟩,htrace⟩
    simpa only [List.forall₂_map_left_iff,inputUnshiftField_shift] using herror
  obtain ⟨v',n,output,hu',hn,he,⟨Zs,hZ,herror⟩,htrace⟩ := inputShiftSolve_exec_trace (body := body) (by omega : 4 ≤ A)
    hst ha hb hband wl hwl xs (inputBatch_unit p Fs hF) v S hscalar hsmall
    (normalizedFamilyInverseBatch recovery hR hQ)
    (normalizedFamilyInverseBatchCost A (inverseCallerWordWidth p u l target s t) p u l s t a b target Fs.length)
    (normalizedFamilyInverseBatchStockCost A (inverseCallerWordWidth p u l target s t) p u l s t a b target Fs.length) post hsource hsolve
  have hlen : xs.length = Fs.length*s := by
    simp [xs,List.length_flatten,List.map_map,Function.comp_def,length_chirpLine]
  rw [hlen] at hn htrace
  rw [hZ] at he htrace
  exact ⟨v',n,Zs,hu',hn,he,herror,htrace⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
