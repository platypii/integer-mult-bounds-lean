module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicTableColumn
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetainedIndexedCyclicColumnStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPublishCyclicBandColumnStock

/-! A complete physical table column retains generation and publication resources. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

@[irreducible] def cyclicTableColumnWorkspace
    (J ringPush batchPush rowPush cap p l s t u target a n k : ℕ) [NeZero s] : ℕ :=
  let q := executionPrecision p l (initialSchurTarget p u target 2) 2
  let band := PhaseCellBand.width p u
  let B := cyclicPrincipalBoundary s t band a n
  retainedIndexedCyclicColumnWorkspace (P₀ := P₀) (Q := Q) (A := A) (U := U)
    J ringPush batchPush rowPush p l s t u target a n k+
    (2*(4*k+4)+(preparedCyclicBandCollectionWorkspace cap q band B.card k+
      8*retireCyclicColumnStreamsCost q s))

theorem cyclicTableColumn_spec_within (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
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
    (cap : ℕ)
    (hcollectionCost :
      let q := executionPrecision p l (initialSchurTarget p u target 2) 2
      let band := PhaseCellBand.width p u
      let B := cyclicPrincipalBoundary s t band a n
      ∀ i < min B.card (k+(24*band+1)+1)-(k-(24*band+1)),
        cyclicColumnEntryStepCost q (publicationGeometryWidth t band) s a (a+min n (s-a))
          (k-(24*band+1)+i) (bFoldAt s B (k-(24*band+1)+i)).val ≤ cap)
    (v : HS 154 Q A U) (S : Stacks 154 A) (tail pageTail : List (Fin (A+4)))
    (hindex : (S.R 151).length = k) (h0 : S.R 0 = []) (h139 : S.R 139 = [])
    (hpageWidth : (S.R 115).length = publicationGeometryWidth t (PhaseCellBand.width p u))
    (hrows : (S.R 116).length = (cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n).card)
    (hpage : S.R 109 = cstream A (publicationGeometryWidth t (PhaseCellBand.width p u))
      ((bFoldOrder s (cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n)).map
        (fun i : ZMod s => (⟨(i.val : ℤ),0⟩ : GaussianInt)))++pageTail)
    (haSrc : (S.R 144).length = a) (hleftEnd : (S.R 145).length = a+min n (s-a))
    (hrightEnd : (S.R 146).length = n-min n (s-a))
    (hfresh : ∀ r ∈ [(127 : Fin 154),138,141,142,143,147], S.R r = [])
    (hready : LengthKeyReady (2^15*p) (executionStagePrecision p l (initialSchurTarget p u target 2) 2+1)
      (executionPrecision p l (initialSchurTarget p u target 2) 2) l s t u (PhaseCellBand.width p u) 0 0 tail
      (embStk componentReg (embStk boundaryArithmeticReg (embStk tableReg S)))) :
    let q := executionPrecision p l (initialSchurTarget p u target 2) 2
    let w := executionWidth p l (initialSchurTarget p u target 2) 2
    let band := PhaseCellBand.width p u
    let B := cyclicPrincipalBoundary s t band a n
    let j := bFoldAt s B k
    ∃ v' m, ∃ E : ZMod s → GaussianInt,
      let output := cstream A w ((foldedBandRows B (24*band+1) k).reverse.map E)++S.R 132
      let S' : Stacks 154 A := {S with R := Function.update S.R 132 output}
      v'.user = v.user ∧ m ≤ cyclicTableColumnCost p u l s t a n target k j.val ∧
      ExecWithin (embTab tableReg (embTab boundaryArithmeticReg (embTab componentReg (embTab groupReg body))))
        (fun d z => mnSize z+d ≤ mnSize (mk v S)+0+
          cyclicTableColumnWorkspace (P₀ := P₀) (Q := Q) (A := A) (U := U)
            J ringPush batchPush rowPush cap p l s t u target a n k)
        0 (cyclicTableColumn hR hQ) (mk v S) m (mk v' S') ∧
      (∀ i, (E i).im = 0) ∧
      (∀ i, ‖value q (E i)‖ ≤ (2 : ℝ)^couplingRowExponent 2 (stableInteriorExponent p 2) (8*p+1) (couplingCountExponent p u)) ∧
      (∀ i ∈ B, |(value q (decodeWord (csyms A w (E i)))).re-
        (SchurDominance.run (realMatrix s t p u) (cyclicPrincipalVertices s a n)
          (cyclicPrincipalInterior s t band a n).toList).1 i j| ≤ 1/(2 : ℝ)^target) ∧
      LengthKeyReady (2^15*p) (executionStagePrecision p l (initialSchurTarget p u target 2) 2+1)
        q l s t u band 0 0 tail (embStk componentReg (embStk boundaryArithmeticReg (embStk tableReg S'))) := by
  dsimp only
  let q := executionPrecision p l (initialSchurTarget p u target 2) 2
  let w := executionWidth p l (initialSchurTarget p u target 2) 2
  let band := PhaseCellBand.width p u
  let B := cyclicPrincipalBoundary s t band a n
  let j := bFoldAt s B k
  have hlow (r : Fin 154) (hr : r.val < 117) (h93 : r ≠ 93) (h110 : r ≠ 110)
      (h109 : r ≠ 109) (h115 : r ≠ 115) (h116 : r ≠ 116) : S.R r = [] := by
    let r₀ : Fin 144 := ⟨r.val,by omega⟩
    have hh := hready.blank r₀ (by change r.val < 117; exact hr)
      (by intro he; apply h93; exact Fin.ext (congrArg (fun k : Fin 144 => k.val) he))
      (by intro he; apply h110; exact Fin.ext (congrArg (fun k : Fin 144 => k.val) he))
    have h109v : r.val ≠ 109 := fun he => h109 (Fin.ext he)
    have h115v : r.val ≠ 115 := fun he => h115 (Fin.ext he)
    have h116v : r.val ≠ 116 := fun he => h116 (Fin.ext he)
    simpa [r₀,embStk,componentReg,boundaryArithmeticReg,tableReg,Fin.ext_iff,h109v,h115v,h116v] using hh
  have h135 : S.R 135 = [] := by simpa [embStk,componentReg,boundaryArithmeticReg,tableReg] using hready.fresh 135 (by simp)
  obtain ⟨v₁,m₁,C,D,hv₁,hm₁,he₁,hreal,hnorm,herror,_⟩ := retainedIndexedCyclicColumn_spec_within (body := body)
    hR hQ hA hp hwidth halpha hst hu hsquare htheta hgap hbudget hband ha hn hpad k hk J ringPush batchPush hpushJ hpushR hpushK rowPush hrowPush v S tail
    hindex h0 h139 (hlow 106 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    hpageWidth pageTail hpage haSrc hleftEnd hrightEnd hfresh hready
  change m₁ ≤ retainedIndexedCyclicColumnCost p u l s t a n target k j.val at hm₁
  let original := couplingRowField (2^15*p) q t u band j.val (j.val+1) true (negativeUnitField q j) (fun _ => 0)
  let input := cstream A w (chirpLine s original)++tail
  let residuals := cstream A w (chirpLine s D)++(cstream A w (chirpLine s C)++S.R 132)
  let F : Stacks 154 A := {S with R := Function.update (Function.update S.R 110 input) 132 residuals}
  obtain ⟨v₂,hv₂,he₂⟩ := ucopy_exec
    (embTab tableReg (embTab boundaryArithmeticReg (embTab componentReg (embTab groupReg body))))
    (a := 151) (b := 0) (t := 135) (by decide) (by decide) (by decide) v₁ F (by simpa [F] using h135)
  let G : Stacks 154 A := {F with R := Function.update F.R 0 (List.replicate k tick)}
  have he₂' : Exec (embTab tableReg (embTab boundaryArithmeticReg (embTab componentReg (embTab groupReg body))))
      (ucopy 151 0 135) (mk v₁ F) (4*k+4) (mk v₂ G) := by simpa [G,F,hindex,h0] using he₂
  have hq : (S.R 119).length = q := by
    simpa [embStk,componentReg,boundaryArithmeticReg,tableReg,groupHeaderValue,q] using hready.masters (119,112) (by simp [groupHeaderCopies])
  have hs : (S.R 121).length = s := by
    simpa [embStk,componentReg,boundaryArithmeticReg,tableReg,groupHeaderValue] using hready.masters (121,97) (by simp [groupHeaderCopies])
  have hb : (S.R 124).length = band := by
    simpa [embStk,componentReg,boundaryArithmeticReg,tableReg,groupHeaderValue,band] using hready.masters (124,100) (by simp [groupHeaderCopies])
  have hwork : ∀ r ∈ [(94 : Fin 154),106,131,134,135,136,137,138,139,140], S.R r = [] := by
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hlow 94 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact hlow 106 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · simpa [embStk,componentReg,boundaryArithmeticReg,tableReg] using hready.fresh 131 (by simp)
    · simpa [embStk,componentReg,boundaryArithmeticReg,tableReg] using hready.fresh 134 (by simp)
    · exact h135
    · simpa [embStk,componentReg,boundaryArithmeticReg,tableReg] using hready.fresh 136 (by simp)
    · simpa [embStk,componentReg,boundaryArithmeticReg,tableReg] using hready.fresh 137 (by simp)
    · exact hfresh 138 (by simp)
    · exact h139
    · simpa [embStk,componentReg,boundaryArithmeticReg,tableReg] using hready.fresh 140 (by simp)
  have h150 : S.R 150 = [] := by
    simpa [embStk,componentReg,boundaryArithmeticReg,tableReg] using hready.blank 116 (by decide) (by decide) (by decide)
  have hw : w = 2*q+8 := by dsimp [w,q,executionWidth,executionPrecision]; omega
  obtain ⟨vi,m₃,hvi,hm₃,hex⟩ := publishCyclicBandColumn_exec_within
    (body := embTab boundaryArithmeticReg (embTab componentReg (embTab groupReg body))) B q (publicationGeometryWidth t band) band a (a+min n (s-a)) k cap 0 hcollectionCost
    (by omega) (publicationGeometryWidth_cyclic_address s t band hst.le) ha.le (by omega) hk C D original
    pageTail (S.R 132) tail (embDn tableReg v₂) (embStk tableReg G)
    (by simp [embStk,tableReg,G]) (by simpa [embStk,tableReg,G,F,band] using hpageWidth)
    (by simpa [embStk,tableReg,G,F] using hb) (by simpa [embStk,tableReg,G,F,B,band] using hrows)
    (by simpa [embStk,tableReg,G,F,B,band] using hpage) (by simpa [embStk,tableReg,G,F] using hq)
    (by simpa [embStk,tableReg,G,F] using hs) (by simpa [embStk,tableReg,G,F] using haSrc)
    (by simpa [embStk,tableReg,G,F] using hleftEnd) (by simp [embStk,tableReg,G,F,residuals,hw])
    (by simp [embStk,tableReg,G,F,input,hw])
    (by intro r hr
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simpa [embStk,tableReg,G,F] using hwork _ (by simp))
    (by simpa [embStk,tableReg,G,F] using h150)
    (by intro r hr hr0
        have hr0v : r.val ≠ 0 := fun he => hr0 (Fin.ext he)
        have hr110 : r.val ≠ 110 := by omega
        have hr132 : r.val ≠ 132 := by omega
        have hh := hlow ⟨r.val,by omega⟩ (by change r.val < 117; omega)
          (by intro he; have := congrArg (fun k : Fin 154 => k.val) he; change r.val = 93 at this; omega)
          (by intro he; have := congrArg (fun k : Fin 154 => k.val) he; change r.val = 110 at this; omega)
          (by intro he; have := congrArg (fun k : Fin 154 => k.val) he; change r.val = 109 at this; omega)
          (by intro he; have := congrArg (fun k : Fin 154 => k.val) he; change r.val = 115 at this; omega)
          (by intro he; have := congrArg (fun k : Fin 154 => k.val) he; change r.val = 116 at this; omega)
        simpa [embStk,tableReg,G,F,hr0v,hr110,hr132,Fin.ext_iff] using hh)
  let E := fun i : ZMod s => if a ≤ i.val ∧ i.val < a+min n (s-a) then C i else D i
  let output := cstream A w ((foldedBandRows B (24*band+1) k).reverse.map E)++S.R 132
  have hex' : ExecWithin (embTab boundaryArithmeticReg (embTab componentReg (embTab groupReg body)))
      (fun d z => mnSize z+d ≤ mnSize (mk (embDn tableReg v₂) (embStk tableReg G))+0+
        (preparedCyclicBandCollectionWorkspace cap q band B.card k+8*retireCyclicColumnStreamsCost q s))
      0 publishCyclicBandColumn
      (mk (embDn tableReg v₂) (embStk tableReg G)) m₃
      (mk vi {(embStk tableReg G) with R := (Function.update (Function.update
        (Function.update (embStk tableReg G).R 0 []) 110 tail) 132 output)}) := by
    simpa [output,E,hw] using hex
  obtain ⟨v₃,hv₃,he₃⟩ := exec_emb_rightUpdates_within_stock tableReg tableReg_injective
    publishCyclicBandColumn v₂ G vi m₃ 0
    (preparedCyclicBandCollectionWorkspace cap q band B.card k+8*retireCyclicColumnStreamsCost q s)
    [(0,[]),(110,tail),(132,output)] hvi hex'
  have hsrc : S.R 110 = tail := by simpa [embStk,componentReg,boundaryArithmeticReg,tableReg] using hready.source
  have hfinal : {G with R := (Function.update (Function.update (Function.update G.R (tableReg 0) [])
      (tableReg 110) tail) (tableReg 132) output)} = {S with R := Function.update S.R 132 output} := by
    ext1
    · rfl
    · rfl
    · rfl
    · funext r
      by_cases h0' : r = 0 <;> by_cases h110 : r = 110 <;> by_cases h132 : r = 132 <;>
        simp [G,F,tableReg,h0',h110,h132,h0,hsrc,Function.update_apply]
  have hrealE (i : ZMod s) : (E i).im = 0 := by dsimp [E]; split_ifs <;> first | exact (hreal i).1 | exact (hreal i).2
  have hnormE (i : ZMod s) : ‖value q (E i)‖ ≤ (2 : ℝ)^couplingRowExponent 2 (stableInteriorExponent p 2) (8*p+1) (couplingCountExponent p u) := by
    dsimp [E]; split_ifs <;> first | exact (hnorm i).1 | exact (hnorm i).2
  have hcopy : mnNativePushBound 2 (ucopy (P := P₀) (Q := Q) (A := A) (U := U) (151 : Fin 154) 0 135) := by
    simp [ucopy,umulSym,scanR,drainR,popDo,keepIn,pushN,moveR,moveStep,whileR,peekR,mnNativePushBound,mnActPush]
  have ht₂ := mn_native_exec_within he₂' 2 hcopy 0 _ (Nat.le_refl _)
  have ht := (mn_seq_within_add he₁ (mn_seq_within_add ht₂ he₃)).mono
    (J := fun d z => mnSize z+d ≤ mnSize (mk v S)+0+
      cyclicTableColumnWorkspace (P₀ := P₀) (Q := Q) (A := A) (U := U)
        J ringPush batchPush rowPush cap p l s t u target a n k) (by
      intro d z hz
      unfold cyclicTableColumnWorkspace
      exact hz)
  refine ⟨v₃,m₁+((4*k+4)+m₃),E,hv₃.trans (hv₂.trans hv₁),Nat.add_le_add hm₁ (Nat.add_le_add_left hm₃ _),
    ht.cast rfl (congrArg (mk v₃) hfinal),hrealE,hnormE,?_,?_⟩
  · intro i hi
    have hfit : Fits w (E i) := fits_of_value_power
      (stableInteriorResidual_width p u l (initialSchurTarget p u target 2) 2) _ (hnormE i)
    rw [decodeWord_of_fits (by omega) (by rw [hw]; omega) _ hfit]
    have hh := herror i hi
    simp only [mem_haloVertices] at hh
    by_cases hmem : a ≤ i.val ∧ i.val < a+min n (s-a) <;> simpa [E,hmem] using hh
  · have hpT := tableProject_updateR_inner S (132 : Fin 151) output
    have hcT : tableReg (132 : Fin 151) = (132 : Fin 154) := by decide
    rw [hcT] at hpT
    have hpB := boundaryArithmeticProject_updateR_inner (embStk tableReg S) (132 : Fin 148) output
    have hcB : boundaryArithmeticReg (132 : Fin 148) = (132 : Fin 151) := by decide
    rw [hcB] at hpB
    have hpC := componentProject_updateR_inner (embStk boundaryArithmeticReg (embStk tableReg S)) (132 : Fin 144) output
    have hcC : componentReg (132 : Fin 144) = (132 : Fin 148) := by decide
    rw [hcC] at hpC
    change LengthKeyReady _ _ _ _ _ _ _ _ _ _ _ (embStk componentReg (embStk boundaryArithmeticReg
      (embStk tableReg {S with R := Function.update S.R 132 output})))
    rw [hpT,hpB,hpC]
    exact hready.update_output output

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
