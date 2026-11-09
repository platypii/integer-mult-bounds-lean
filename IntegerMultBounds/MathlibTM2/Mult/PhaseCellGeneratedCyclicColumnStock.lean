module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedCyclicColumn
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicResidualPassesStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellArbitraryOriginalColumnStock

/-! Generate an original column and both guarded residuals with one retained
resource contract for the actual joint cyclic column program. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

@[irreducible] def generatedCyclicColumnWorkspace
    (J ringPush batchPush rowPush p l s t u target a n j : ℕ) : ℕ :=
  arbitraryOriginalColumnWorkspace (P₀ := P₀) (Q := Q) (A := A) (U := U) rowPush p
    (executionPrecision p l (initialSchurTarget p u target 2) 2) s t u j+
  cyclicResidualPassesWorkspace (P₀ := P₀) (Q := Q) (A := A) (U := U)
    J ringPush batchPush rowPush p l s t u target 2 a n

theorem generatedCyclicColumn_spec_within (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {p l s t u target a n : ℕ} [NeZero s] {alpha d : ℝ}
    (hp : 2 ≤ p) (hwidth : 8*p ≤ 2^u) (halpha : 0 < alpha) (hst : s < t) (hu : 1 ≤ u)
    (hsquare : alpha^2 = (u : ℝ)) (htheta : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1)
    (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : alpha^2*d ≤ p)
    (hband : PhaseCellBand.width p u ≤ s) (ha : a < s) (hn : n ≤ s)
    (hpad : 2*((s/(t-s)+1)-2*PhaseCellBand.width p u) ≤ 2^l+1)
    (j : ZMod s) (hj : j ∈ cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n)
    (J ringPush batchPush : ℕ)
    (hpushJ : mnProgPush (rmulOne (P := P₀) (Q := Q) (A := A) (U := U)
      mul mul_injective (by decide) hQ cr) ≤ J)
    (hpushR : mnProgPush (rpProg (P := P₀) (Q := Q) (A := A) (U := U)
      Fixed.ringReg Fixed.hostReg Fixed.layout.ι_inj (by decide) hR) ≤ ringPush)
    (hpushK : mnProgPush (cmulBlock cr
      (rmulOne (P := P₀) (Q := Q) (A := A) (U := U) mul mul_injective (by decide) hQ cr)) ≤ batchPush)
    (rowPush : ℕ) (hrowPush : mnProgPush (rmulOne (P := Empty) (Q := Q) (A := A) (U := U)
      mul mul_injective (by decide) hQ cr) ≤ rowPush)
    (v : HS 148 Q A U) (S : Stacks 148 A) (tail : List (Fin (A+4)))
    (hcoordinate : (S.R 139).length = j.val)
    (haSrc : (S.R 144).length = a) (hleftEnd : (S.R 145).length = a+min n (s-a))
    (hrightEnd : (S.R 146).length = n-min n (s-a))
    (hfresh : ∀ k ∈ [(127 : Fin 148),138,141,142,143,147], S.R k = [])
    (hready : LengthKeyReady (2^15*p) (executionStagePrecision p l (initialSchurTarget p u target 2) 2+1)
      (executionPrecision p l (initialSchurTarget p u target 2) 2) l s t u (PhaseCellBand.width p u) 0 0 tail (embStk componentReg S)) :
    let q := executionPrecision p l (initialSchurTarget p u target 2) 2
    let w := executionWidth p l (initialSchurTarget p u target 2) 2
    let band := PhaseCellBand.width p u
    let B := couplingRowField (2^15*p) q t u band j.val (j.val+1) true (negativeUnitField q j) (fun _ => 0)
    let input := cstream A w (chirpLine s B)++tail
    ∃ v' m, ∃ C D : ZMod s → GaussianInt,
      let output := cstream A w (chirpLine s D)++(cstream A w (chirpLine s C)++S.R 132)
      let S' : Stacks 148 A := {S with R := Function.update (Function.update S.R 110 input) 132 output}
      v'.user = v.user ∧
      m ≤ arbitraryOriginalColumnCost p q s t u j.val+
        (windowedSchurResidualCost p l s t u target 2 a (a+min n (s-a))+
          windowedSchurResidualCost p l s t u target 2 0 (n-min n (s-a))) ∧
      ExecWithin (embTab componentReg (embTab groupReg body))
        (fun d z => mnSize z+d ≤ mnSize (mk v S)+0+
          generatedCyclicColumnWorkspace (P₀ := P₀) (Q := Q) (A := A) (U := U)
            J ringPush batchPush rowPush p l s t u target a n j.val)
        0 (generatedCyclicColumn hR hQ) (mk v S) m (mk v' S') ∧
      (∀ i, (C i).im = 0 ∧ (D i).im = 0) ∧
      (∀ i, ‖value q (C i)‖ ≤ (2 : ℝ)^couplingRowExponent 2 (stableInteriorExponent p 2) (8*p+1) (couplingCountExponent p u) ∧
        ‖value q (D i)‖ ≤ (2 : ℝ)^couplingRowExponent 2 (stableInteriorExponent p 2) (8*p+1) (couplingCountExponent p u)) ∧
      (∀ i ∈ cyclicPrincipalBoundary s t band a n,
        |(if i ∈ haloVertices s a (a+min n (s-a)) then (value q (C i)).re else (value q (D i)).re)-
          (SchurDominance.run (realMatrix s t p u) (cyclicPrincipalVertices s a n)
            (cyclicPrincipalInterior s t band a n).toList).1 i j| ≤ 1/(2 : ℝ)^target) ∧
      LengthKeyReady (2^15*p) (executionStagePrecision p l (initialSchurTarget p u target 2) 2+1)
        q l s t u band 0 0 input (embStk componentReg S') := by
  dsimp only
  let q := executionPrecision p l (initialSchurTarget p u target 2) 2
  let w := executionWidth p l (initialSchurTarget p u target 2) 2
  let band := PhaseCellBand.width p u
  let B := couplingRowField (2^15*p) q t u band j.val (j.val+1) true (negativeUnitField q j) (fun _ => 0)
  let input := cstream A w (chirpLine s B)++tail
  have hw : w = 2*q+8 := by dsimp [w,q,executionWidth,executionPrecision]; omega
  have hwcol : q+couplingRowExponent 0 0 (8*p+1) (couplingCountExponent p u)+2 ≤ 2*q+8 := by
    rw [← hw]
    exact originalColumn_width p u l (initialSchurTarget p u target 2) 2
  obtain ⟨v₁,m₁,hv₁,hm₁,he₁,_,hBnorm,hBerror,hready₁⟩ := arbitraryOriginalColumn_spec_within (body := body)
    hQ hA hp hwidth halpha hst hsquare htheta hgap hbudget hwcol hband j tail rowPush hrowPush v S hready hcoordinate
    (fun k hk => hfresh k (by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl <;> simp))
  let F : Stacks 148 A := {S with R := Function.update S.R 110 input}
  have he₁' : ExecWithin (embTab componentReg (embTab groupReg body))
      (fun d z => mnSize z+d ≤ mnSize (mk v S)+0+
        arbitraryOriginalColumnWorkspace (P₀ := P₀) (Q := Q) (A := A) (U := U) rowPush p q s t u j.val)
      0 (arbitraryOriginalColumn hQ)
      (mk v S) m₁ (mk v₁ F) := by simpa only [← hw] using he₁
  have hreadyF : LengthKeyReady (2^15*p) (executionStagePrecision p l (initialSchurTarget p u target 2) 2+1)
      q l s t u band 0 0 input (embStk componentReg F) := by simpa only [← hw] using hready₁
  have hB (i : ZMod s) : ‖value q (B i)‖ ≤ (2 : ℝ)^2 :=
    (hBnorm i).trans (originalColumn_magnitude_budget p u l target 2)
  have hBfit (i : ZMod s) : Fits w (B i) := fits_of_value_power
    (by rw [hw]; omega) _ (hB i)
  let eta : ℝ := 3*(2*band+1)*(1/(2 : ℝ)^q)
  have hcolumn (i : ZMod s) : |(value q (B i)).re-realMatrix s t p u i j| ≤ eta := by
    have hh : |publishedCellRead q w (0 : ZMod s) input i-realMatrix s t p u i j| ≤ eta := by
      simpa [← hw,input,eta,B,band,q] using hBerror i
    rw [publishedCellRead_encodedField (by omega) (by rw [hw]; omega) B tail hBfit i] at hh
    exact hh
  obtain ⟨v₂,m₂,C,D,R,T,hsolve,hv₂,hm₂,he₂,hreal,hnorm,herror,hready₂⟩ := cyclicResidualPasses_spec_within
    (body := body) (rhsExp := 2) hR hQ hA hp hwidth halpha hst hu hsquare htheta hgap hbudget hband ha hn hpad B hB J ringPush batchPush hpushJ hpushR hpushK rowPush hrowPush v₁ F tail
    (by simpa [F] using haSrc) (by simpa [F] using hleftEnd) (by simpa [F] using hrightEnd)
    (by intro k hk
        have hne : k ≠ 110 := by
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
          rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
        simpa [F,hne] using hfresh k hk) hreadyF
  have hentry := cyclicPrincipal_schur_column_error hst halpha p u a n hp hwidth hsquare htheta hgap hbudget
    _ hsolve j hj (fun k => (value q (B k)).re)
    (fun i => if i ∈ haloVertices s a (a+min n (s-a)) then (value q (C i)).re else (value q (D i)).re)
    eta ((1/(2 : ℝ)^(recoveryTarget p target+2))/(8*(p : ℝ))) (by dsimp [eta]; positivity)
    (fun k _ => hcolumn k) herror
  have ht := (mn_seq_within_add he₁' he₂).mono (J := fun d z => mnSize z+d ≤ mnSize (mk v S)+0+
      generatedCyclicColumnWorkspace (P₀ := P₀) (Q := Q) (A := A) (U := U)
        J ringPush batchPush rowPush p l s t u target a n j.val) (by
    intro d z hz
    unfold generatedCyclicColumnWorkspace
    exact hz)
  refine ⟨v₂,m₁+m₂,C,D,hv₂.trans hv₁,Nat.add_le_add hm₁ hm₂,
    ht.cast rfl ?_,hreal,hnorm,?_,?_⟩
  · simp [F,input,B,band,q,w]
  · intro i hi
    exact (hentry i hi).trans (originalColumn_schur_budget p u l target 2 (by omega))
  · simpa [F,input,B,band,q,w] using hready₂

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
