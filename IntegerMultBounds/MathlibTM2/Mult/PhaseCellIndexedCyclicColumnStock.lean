module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellIndexedCyclicColumn
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellResidentCyclicColumnStock

/-! Resident coordinate selection and retirement surround one numerical column reserve. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

theorem selectResidentCoordinate_native :
    mnNativePushBound 3 (selectResidentCoordinate (P₀ := P₀) (Q := Q) (A := A) (U := U)) := by
  simp [selectResidentCoordinate,loadResidentCoordinate,residentBoundaryWord,copyIndexedWord,
    copySlice,copyPrefix,copyR,copyStep,unaryProduct,decodeNaturalWord,toUnary,hornerIter,udbl,eachSym,
    transfer,transferAct,ucopy,umulSym,scanP,scanR,drainR,popDo,keepIn,pushN,popPush,uclear,
    moveR,moveStep,whileR,peekR,mnNativePushBound,mnActPush]

@[irreducible] def indexedCyclicColumnWorkspace
    (J ringPush batchPush rowPush p l s t u target a n k : ℕ) [NeZero s] : ℕ :=
  let band := PhaseCellBand.width p u
  let j := bFoldAt s (cyclicPrincipalBoundary s t band a n) k
  3*(k*(12*publicationGeometryWidth t band+11)+27*publicationGeometryWidth t band+6*j.val+36)+
    generatedCyclicColumnWorkspace (P₀ := P₀) (Q := Q) (A := A) (U := U)
      J ringPush batchPush rowPush p l s t u target a n j.val

theorem indexedCyclicColumn_spec_within (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {p l s t u target a n : ℕ} [NeZero s] {alpha d : ℝ}
    (hp : 2 ≤ p) (hwidth : 8*p ≤ 2^u) (halpha : 0 < alpha) (hst : s < t) (hu : 1 ≤ u)
    (hsquare : alpha^2 = (u : ℝ)) (htheta : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1)
    (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : alpha^2*d ≤ p)
    (hband : PhaseCellBand.width p u ≤ s) (ha : a < s) (hn : n ≤ s)
    (hpad : 2*((s/(t-s)+1)-2*PhaseCellBand.width p u) ≤ 2^l+1)
    (k : ℕ) (hk : k < (cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n).card)
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
    (hindex : (S.R 0).length = k) (h139 : S.R 139 = []) (h106 : S.R 106 = [])
    (hpageWidth : (S.R 115).length = publicationGeometryWidth t (PhaseCellBand.width p u))
    (pageTail : List (Fin (A+4)))
    (hpage : S.R 109 = cstream A (publicationGeometryWidth t (PhaseCellBand.width p u))
      ((bFoldOrder s (cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n)).map
        (fun i : ZMod s => (⟨(i.val : ℤ),0⟩ : GaussianInt)))++pageTail)
    (haSrc : (S.R 144).length = a) (hleftEnd : (S.R 145).length = a+min n (s-a))
    (hrightEnd : (S.R 146).length = n-min n (s-a))
    (hfresh : ∀ k ∈ [(127 : Fin 151),138,141,142,143,147], S.R k = [])
    (hready : LengthKeyReady (2^15*p) (executionStagePrecision p l (initialSchurTarget p u target 2) 2+1)
      (executionPrecision p l (initialSchurTarget p u target 2) 2) l s t u (PhaseCellBand.width p u) 0 0 tail (embStk componentReg (embStk boundaryArithmeticReg {S with R := Function.update S.R 0 []}))) :
    let j := bFoldAt s (cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n) k
    let q := executionPrecision p l (initialSchurTarget p u target 2) 2
    let w := executionWidth p l (initialSchurTarget p u target 2) 2
    let band := PhaseCellBand.width p u
    let B := couplingRowField (2^15*p) q t u band j.val (j.val+1) true (negativeUnitField q j) (fun _ => 0)
    let input := cstream A w (chirpLine s B)++tail
    ∃ v' m, ∃ C D : ZMod s → GaussianInt,
      let output := cstream A w (chirpLine s D)++(cstream A w (chirpLine s C)++S.R 132)
      let S' : Stacks 151 A := {S with R := Function.update (Function.update (Function.update S.R 0 []) 110 input) 132 output}
      v'.user = v.user ∧
      m ≤ (k*(12*publicationGeometryWidth t band+11)+27*publicationGeometryWidth t band+6*j.val+36)+
        ((arbitraryOriginalColumnCost p q s t u j.val+
        (windowedSchurResidualCost p l s t u target 2 a (a+min n (s-a))+
          windowedSchurResidualCost p l s t u target 2 0 (n-min n (s-a))))+(2*j.val+2)) ∧
      ExecWithin (embTab boundaryArithmeticReg (embTab componentReg (embTab groupReg body)))
        (fun d z => mnSize z+d ≤ mnSize (mk v S)+0+indexedCyclicColumnWorkspace (P₀ := P₀) (Q := Q) (A := A) (U := U)
            J ringPush batchPush rowPush p l s t u target a n k)
        0 (indexedCyclicColumn hR hQ) (mk v S) m (mk v' S') ∧
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
  let boundary := cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n
  let V := publicationGeometryWidth t (PhaseCellBand.width p u)
  let j := bFoldAt s boundary k
  have hV : s ≤ 2^V := by
    have hh := publicationGeometryWidth_fits t (PhaseCellBand.width p u)
    change s ≤ 2^(publicationGeometryWidth t (PhaseCellBand.width p u))
    nlinarith only [hh,hst]
  have hblank (r : Fin 151) (hr1 : 1 ≤ r.val) (hr7 : r.val < 7) : S.R r = [] := by
    let r₀ : Fin 144 := ⟨r.val,by omega⟩
    have hr117 : r₀.val < 117 := by change r.val < 117; omega
    have hr93 : r₀ ≠ 93 := by
      intro he
      have hh := congrArg (fun k : Fin 144 => k.val) he
      change r.val = 93 at hh
      omega
    have hr110 : r₀ ≠ 110 := by
      intro he
      have hh := congrArg (fun k : Fin 144 => k.val) he
      change r.val = 110 at hh
      omega
    have hh := hready.blank r₀ hr117 hr93 hr110
    have hr0 : r.val ≠ 0 := by omega
    simpa [r₀,embStk,componentReg,boundaryArithmeticReg,Function.update_apply,Fin.ext_iff,hr0,
      show r.val ≠ 109 by omega,show r.val ≠ 115 by omega,show r.val ≠ 116 by omega] using hh
  obtain ⟨v₁,m₁,hv₁,hm₁,he₁,hj,_⟩ := selectResidentCoordinate_exec
    (body := embTab boundaryArithmeticReg (embTab componentReg (embTab groupReg body)))
    boundary V k (by omega) hV hk pageTail v S hindex hpageWidth hpage h106 h139 hblank
  let S₀ : Stacks 151 A := {S with R := Function.update S.R 0 []}
  let S₁ : Stacks 151 A := {S₀ with R := Function.update S₀.R 139 (List.replicate j.val tick)}
  have hready₁ : LengthKeyReady (2^15*p) (executionStagePrecision p l (initialSchurTarget p u target 2) 2+1)
      (executionPrecision p l (initialSchurTarget p u target 2) 2) l s t u (PhaseCellBand.width p u) 0 0 tail
      (embStk componentReg (embStk boundaryArithmeticReg S₁)) := by
    have hcB : boundaryArithmeticReg (139 : Fin 148) = (139 : Fin 151) := by decide
    have hpB := boundaryArithmeticProject_updateR_inner S₀ (139 : Fin 148) (List.replicate j.val tick)
    rw [hcB] at hpB
    have hcC : componentReg (139 : Fin 144) = (139 : Fin 148) := by decide
    have hpC := componentProject_updateR_inner (embStk boundaryArithmeticReg S₀) (139 : Fin 144) (List.replicate j.val tick)
    rw [hcC] at hpC
    dsimp only [S₁]
    rw [hpB,hpC]
    exact hready.update_coordinate _
  obtain ⟨v₂,m₂,C,D,hv₂,hm₂,he₂,hreal,hnorm,herror,_⟩ := residentCyclicColumn_spec_within (body := body)
    hR hQ hA hp hwidth halpha hst hu hsquare htheta hgap hbudget hband ha hn hpad j hj J ringPush batchPush hpushJ hpushR hpushK rowPush hrowPush v₁ S₁ tail
    (by simp [S₁]) (by simpa [S₁,S₀] using haSrc) (by simpa [S₁,S₀] using hleftEnd)
    (by simpa [S₁,S₀] using hrightEnd)
    (by intro r hr
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simpa [S₁,S₀] using hfresh _ (by simp)) hready₁
  let q := executionPrecision p l (initialSchurTarget p u target 2) 2
  let w := executionWidth p l (initialSchurTarget p u target 2) 2
  let band := PhaseCellBand.width p u
  let B := couplingRowField (2^15*p) q t u band j.val (j.val+1) true (negativeUnitField q j) (fun _ => 0)
  let input := cstream A w (chirpLine s B)++tail
  let output := cstream A w (chirpLine s D)++(cstream A w (chirpLine s C)++S.R 132)
  let F : Stacks 151 A := {S₁ with R := Function.update (Function.update S₁.R 110 input) 132 output}
  have he₂' : ExecWithin (embTab boundaryArithmeticReg (embTab componentReg (embTab groupReg body)))
      (fun d z => mnSize z+d ≤ mnSize (mk v₁ S₁)+0+
        generatedCyclicColumnWorkspace (P₀ := P₀) (Q := Q) (A := A) (U := U)
          J ringPush batchPush rowPush p l s t u target a n j.val)
      0 (residentCyclicColumn hR hQ)
      (mk v₁ S₁) m₂ (mk v₂ F) := by simpa [F,S₁,S₀,output,input,B,band,q,w] using he₂
  obtain ⟨v₃,hv₃,he₃⟩ := uclear_exec (embTab boundaryArithmeticReg (embTab componentReg (embTab groupReg body))) 139 v₂ F
  have hlen : (F.R 139).length = j.val := by simp [F,S₁]
  have hfinal : {F with R := Function.update F.R 139 []} =
      {S₀ with R := Function.update (Function.update S₀.R 110 input) 132 output} := by
    ext1
    · rfl
    · rfl
    · rfl
    · funext r
      by_cases h139' : r = 139
      · subst r; simp [S₀,h139]
      simp [F,S₁,S₀,h139',Function.update_apply]
  have ht₁ := mn_native_exec_within he₁ 3 selectResidentCoordinate_native 0
    (mnSize (mk v S)+0+3*(k*(12*V+11)+27*V+6*j.val+36)) (by
      dsimp only [j,V,boundary] at hm₁ ⊢
      omega)
  have ht₃ := mn_native_exec_within he₃ 0 (show mnNativePushBound 0
      (uclear (P := P₀) (Q := Q) (A := A) (U := U) (139 : Fin 151)) from by
        simp [uclear,drainR,popDo,peekR,mnNativePushBound,mnActPush]) 0 _ (Nat.le_refl _)
  have ht := (mn_seq_within_add ht₁ (mn_seq_within_add he₂' ht₃)).mono
    (J := fun d z => mnSize z+d ≤ mnSize (mk v S)+0+indexedCyclicColumnWorkspace (P₀ := P₀) (Q := Q) (A := A) (U := U)
            J ringPush batchPush rowPush p l s t u target a n k) (by
      intro d z hz
      unfold indexedCyclicColumnWorkspace
      dsimp only
      dsimp only [boundary,V,j] at hz
      omega)
  refine ⟨v₃,m₁+(m₂+(2*j.val+2)),C,D,hv₃.trans (hv₂.trans hv₁),Nat.add_le_add hm₁ (Nat.add_le_add_right hm₂ _),
    ht.cast (by rw [hlen]) ?_,hreal,hnorm,herror,?_⟩
  · exact congrArg (mk v₃) hfinal
  · change LengthKeyReady (2^15*p) (executionStagePrecision p l (initialSchurTarget p u target 2) 2+1)
      q l s t u band 0 0 input (embStk componentReg (embStk boundaryArithmeticReg
        {S₀ with R := Function.update (Function.update S₀.R 110 input) 132 output}))
    rw [boundaryArithmeticProject_twoPorts S₀ input output]
    have hsource := hready.update_source input
    have hsource' := hsource.update_output output
    have hc : componentReg (132 : Fin 144) = (132 : Fin 148) := by decide
    have hpC := componentProject_updateR_inner
      {(embStk boundaryArithmeticReg S₀) with R := Function.update (embStk boundaryArithmeticReg S₀).R 110 input}
      (132 : Fin 144) output
    rw [hc] at hpC
    have hc110 : componentReg (110 : Fin 144) = (110 : Fin 148) := by decide
    have hp110 := componentProject_updateR_inner (embStk boundaryArithmeticReg S₀) (110 : Fin 144) input
    rw [hc110] at hp110
    rw [hpC,hp110]
    exact hsource'

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
