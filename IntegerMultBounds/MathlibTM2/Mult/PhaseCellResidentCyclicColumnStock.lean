module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellResidentCyclicColumn
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedCyclicColumnStock
public import IntegerMultBounds.MathlibTM2.Host.EmbedRightUpdatesStock

/-! A generated column retains its workspace while the folded boundary page stays resident. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

theorem residentCyclicColumn_spec_within (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
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
    (v : HS 151 Q A U) (S : Stacks 151 A) (tail : List (Fin (A+4)))
    (hcoordinate : (S.R 139).length = j.val)
    (haSrc : (S.R 144).length = a) (hleftEnd : (S.R 145).length = a+min n (s-a))
    (hrightEnd : (S.R 146).length = n-min n (s-a))
    (hfresh : ∀ k ∈ [(127 : Fin 151),138,141,142,143,147], S.R k = [])
    (hready : LengthKeyReady (2^15*p) (executionStagePrecision p l (initialSchurTarget p u target 2) 2+1)
      (executionPrecision p l (initialSchurTarget p u target 2) 2) l s t u (PhaseCellBand.width p u) 0 0 tail (embStk componentReg (embStk boundaryArithmeticReg S))) :
    let q := executionPrecision p l (initialSchurTarget p u target 2) 2
    let w := executionWidth p l (initialSchurTarget p u target 2) 2
    let band := PhaseCellBand.width p u
    let B := couplingRowField (2^15*p) q t u band j.val (j.val+1) true (negativeUnitField q j) (fun _ => 0)
    let input := cstream A w (chirpLine s B)++tail
    ∃ v' m, ∃ C D : ZMod s → GaussianInt,
      let output := cstream A w (chirpLine s D)++(cstream A w (chirpLine s C)++S.R 132)
      let S' : Stacks 151 A := {S with R := Function.update (Function.update S.R 110 input) 132 output}
      v'.user = v.user ∧
      m ≤ arbitraryOriginalColumnCost p q s t u j.val+
        (windowedSchurResidualCost p l s t u target 2 a (a+min n (s-a))+
          windowedSchurResidualCost p l s t u target 2 0 (n-min n (s-a))) ∧
      ExecWithin (embTab boundaryArithmeticReg (embTab componentReg (embTab groupReg body)))
        (fun d z => mnSize z+d ≤ mnSize (mk v S)+0+generatedCyclicColumnWorkspace (P₀ := P₀) (Q := Q) (A := A) (U := U)
            J ringPush batchPush rowPush p l s t u target a n j.val)
        0 (residentCyclicColumn hR hQ) (mk v S) m (mk v' S') ∧
      (∀ i, (C i).im = 0 ∧ (D i).im = 0) ∧
      (∀ i, ‖value q (C i)‖ ≤ (2 : ℝ)^couplingRowExponent 2 (stableInteriorExponent p 2) (8*p+1) (couplingCountExponent p u) ∧
        ‖value q (D i)‖ ≤ (2 : ℝ)^couplingRowExponent 2 (stableInteriorExponent p 2) (8*p+1) (couplingCountExponent p u)) ∧
      (∀ i ∈ cyclicPrincipalBoundary s t band a n,
        |(if i ∈ haloVertices s a (a+min n (s-a)) then (value q (C i)).re else (value q (D i)).re)-
          (SchurDominance.run (realMatrix s t p u) (cyclicPrincipalVertices s a n)
            (cyclicPrincipalInterior s t band a n).toList).1 i j| ≤ 1/(2 : ℝ)^target) ∧
      LengthKeyReady (2^15*p) (executionStagePrecision p l (initialSchurTarget p u target 2) 2+1)
        q l s t u band 0 0 input (embStk componentReg (embStk boundaryArithmeticReg S')) := by
  dsimp only
  obtain ⟨vi,m,C,D,huser,hm,hex,hreal,hnorm,herror,hready'⟩ := generatedCyclicColumn_spec_within (body := body)
    hR hQ hA hp hwidth halpha hst hu hsquare htheta hgap hbudget hband ha hn hpad j hj J ringPush batchPush hpushJ hpushR hpushK rowPush hrowPush
    (embDn boundaryArithmeticReg v) (embStk boundaryArithmeticReg S) tail
    (by simpa [embStk,boundaryArithmeticReg] using hcoordinate)
    (by simpa [embStk,boundaryArithmeticReg] using haSrc)
    (by simpa [embStk,boundaryArithmeticReg] using hleftEnd)
    (by simpa [embStk,boundaryArithmeticReg] using hrightEnd)
    (by intro k hk
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
          simpa [embStk,boundaryArithmeticReg] using hfresh _ (by simp)) hready
  let q := executionPrecision p l (initialSchurTarget p u target 2) 2
  let w := executionWidth p l (initialSchurTarget p u target 2) 2
  let band := PhaseCellBand.width p u
  let B := couplingRowField (2^15*p) q t u band j.val (j.val+1) true (negativeUnitField q j) (fun _ => 0)
  let input := cstream A w (chirpLine s B)++tail
  let output := cstream A w (chirpLine s D)++(cstream A w (chirpLine s C)++S.R 132)
  have he : ExecWithin (embTab componentReg (embTab groupReg body))
      (fun d z => mnSize z+d ≤ mnSize (mk (embDn boundaryArithmeticReg v) (embStk boundaryArithmeticReg S))+0+generatedCyclicColumnWorkspace (P₀ := P₀) (Q := Q) (A := A) (U := U)
            J ringPush batchPush rowPush p l s t u target a n j.val)
      0 (generatedCyclicColumn hR hQ)
      (mk (embDn boundaryArithmeticReg v) (embStk boundaryArithmeticReg S)) m
      (mk vi {(embStk boundaryArithmeticReg S) with R := (Function.update
        (Function.update (embStk boundaryArithmeticReg S).R 110 input) 132 output)}) := by
    simpa [embStk,boundaryArithmeticReg,Function.comp_def,output,input,B,band,q,w] using hex
  obtain ⟨vf,hvf,hef⟩ := exec_emb_twoPorts_within_stock boundaryArithmeticReg boundaryArithmeticReg_injective 110 132
    (generatedCyclicColumn hR hQ) v S vi m 0 (generatedCyclicColumnWorkspace (P₀ := P₀) (Q := Q) (A := A) (U := U)
            J ringPush batchPush rowPush p l s t u target a n j.val) input output huser he
  refine ⟨vf,m,C,D,hvf,hm,hef,hreal,hnorm,herror,?_⟩
  rw [boundaryArithmeticProject_twoPorts]
  simpa [embStk,boundaryArithmeticReg,Function.comp_def,output,input,B,band,q,w] using hready'

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
