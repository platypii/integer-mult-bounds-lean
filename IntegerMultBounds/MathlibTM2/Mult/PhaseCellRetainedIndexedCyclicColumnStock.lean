module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetainedIndexedCyclicColumn
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellIndexedCyclicColumnStock

/-! Retain the outer index through column generation using the generic write-list lift. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

@[irreducible] def retainedIndexedCyclicColumnWorkspace
    (J ringPush batchPush rowPush p l s t u target a n k : ℕ) [NeZero s] : ℕ :=
  2*(4*k+4)+indexedCyclicColumnWorkspace (P₀ := P₀) (Q := Q) (A := A) (U := U)
    J ringPush batchPush rowPush p l s t u target a n k

theorem retainedIndexedCyclicColumn_spec_within (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
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
    (v : HS 154 Q A U) (S : Stacks 154 A) (tail : List (Fin (A+4)))
    (hindex : (S.R 151).length = k) (h0 : S.R 0 = []) (h139 : S.R 139 = []) (h106 : S.R 106 = [])
    (hpageWidth : (S.R 115).length = publicationGeometryWidth t (PhaseCellBand.width p u))
    (pageTail : List (Fin (A+4)))
    (hpage : S.R 109 = cstream A (publicationGeometryWidth t (PhaseCellBand.width p u))
      ((bFoldOrder s (cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n)).map
        (fun i : ZMod s => (⟨(i.val : ℤ),0⟩ : GaussianInt)))++pageTail)
    (haSrc : (S.R 144).length = a) (hleftEnd : (S.R 145).length = a+min n (s-a))
    (hrightEnd : (S.R 146).length = n-min n (s-a))
    (hfresh : ∀ k ∈ [(127 : Fin 154),138,141,142,143,147], S.R k = [])
    (hready : LengthKeyReady (2^15*p) (executionStagePrecision p l (initialSchurTarget p u target 2) 2+1)
      (executionPrecision p l (initialSchurTarget p u target 2) 2) l s t u (PhaseCellBand.width p u) 0 0 tail (embStk componentReg (embStk boundaryArithmeticReg (embStk tableReg S)))) :
    let j := bFoldAt s (cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n) k
    let q := executionPrecision p l (initialSchurTarget p u target 2) 2
    let w := executionWidth p l (initialSchurTarget p u target 2) 2
    let band := PhaseCellBand.width p u
    let B := couplingRowField (2^15*p) q t u band j.val (j.val+1) true (negativeUnitField q j) (fun _ => 0)
    let input := cstream A w (chirpLine s B)++tail
    ∃ v' m, ∃ C D : ZMod s → GaussianInt,
      let output := cstream A w (chirpLine s D)++(cstream A w (chirpLine s C)++S.R 132)
      let S' : Stacks 154 A := {S with R := Function.update (Function.update S.R 110 input) 132 output}
      v'.user = v.user ∧
      m ≤ (4*k+4)+((k*(12*publicationGeometryWidth t band+11)+27*publicationGeometryWidth t band+6*j.val+36)+
        ((arbitraryOriginalColumnCost p q s t u j.val+
        (windowedSchurResidualCost p l s t u target 2 a (a+min n (s-a))+
          windowedSchurResidualCost p l s t u target 2 0 (n-min n (s-a))))+(2*j.val+2))) ∧
      ExecWithin (embTab tableReg (embTab boundaryArithmeticReg (embTab componentReg (embTab groupReg body))))
        (fun d z => mnSize z+d ≤ mnSize (mk v S)+0+retainedIndexedCyclicColumnWorkspace (P₀ := P₀) (Q := Q) (A := A) (U := U)
            J ringPush batchPush rowPush p l s t u target a n k)
        0 (retainedIndexedCyclicColumn hR hQ) (mk v S) m (mk v' S') ∧
      (∀ i, (C i).im = 0 ∧ (D i).im = 0) ∧
      (∀ i, ‖value q (C i)‖ ≤ (2 : ℝ)^couplingRowExponent 2 (stableInteriorExponent p 2) (8*p+1) (couplingCountExponent p u) ∧
        ‖value q (D i)‖ ≤ (2 : ℝ)^couplingRowExponent 2 (stableInteriorExponent p 2) (8*p+1) (couplingCountExponent p u)) ∧
      (∀ i ∈ cyclicPrincipalBoundary s t band a n,
        |(if i ∈ haloVertices s a (a+min n (s-a)) then (value q (C i)).re else (value q (D i)).re)-
          (SchurDominance.run (realMatrix s t p u) (cyclicPrincipalVertices s a n)
            (cyclicPrincipalInterior s t band a n).toList).1 i j| ≤ 1/(2 : ℝ)^target) ∧
      LengthKeyReady (2^15*p) (executionStagePrecision p l (initialSchurTarget p u target 2) 2+1)
        q l s t u band 0 0 input (embStk componentReg (embStk boundaryArithmeticReg (embStk tableReg S'))) := by
  dsimp only
  let boundary := cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n
  let j := bFoldAt s boundary k
  let q := executionPrecision p l (initialSchurTarget p u target 2) 2
  let w := executionWidth p l (initialSchurTarget p u target 2) 2
  let band := PhaseCellBand.width p u
  have h135 : S.R 135 = [] := by
    simpa [embStk,componentReg,boundaryArithmeticReg,tableReg] using hready.fresh 135 (by simp)
  obtain ⟨v₁,hv₁,he₁⟩ := ucopy_exec
    (embTab tableReg (embTab boundaryArithmeticReg (embTab componentReg (embTab groupReg body))))
    (a := 151) (b := 0) (t := 135) (by decide) (by decide) (by decide) v S h135
  let S₁ : Stacks 154 A := {S with R := Function.update S.R 0 (List.replicate k tick)}
  have he₁' : Exec (embTab tableReg (embTab boundaryArithmeticReg (embTab componentReg (embTab groupReg body))))
      (ucopy 151 0 135) (mk v S) (4*k+4) (mk v₁ S₁) := by simpa [S₁,hindex,h0] using he₁
  have hreset : {(embStk tableReg S₁) with R := Function.update (embStk tableReg S₁).R 0 []} = embStk tableReg S := by
    ext1
    · rfl
    · rfl
    · rfl
    · funext r
      by_cases hr : r = 0 <;> simp [embStk,Function.comp_def,tableReg,S₁,hr,h0]
  obtain ⟨vi,m₂,C,D,hvi,hm₂,hex,hreal,hnorm,herror,hready₂⟩ := indexedCyclicColumn_spec_within (body := body)
    hR hQ hA hp hwidth halpha hst hu hsquare htheta hgap hbudget hband ha hn hpad k hk J ringPush batchPush hpushJ hpushR hpushK rowPush hrowPush
    (embDn tableReg v₁) (embStk tableReg S₁) tail (by simp [embStk,tableReg,S₁])
    (by simpa [embStk,tableReg,S₁] using h139) (by simpa [embStk,tableReg,S₁] using h106)
    (by simpa [embStk,tableReg,S₁] using hpageWidth) pageTail (by simpa [embStk,tableReg,S₁] using hpage)
    (by simpa [embStk,tableReg,S₁] using haSrc) (by simpa [embStk,tableReg,S₁] using hleftEnd)
    (by simpa [embStk,tableReg,S₁] using hrightEnd)
    (by intro r hr
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simpa [embStk,tableReg,S₁] using hfresh _ (by simp))
    (by rw [hreset]; exact hready)
  let B := couplingRowField (2^15*p) q t u band j.val (j.val+1) true (negativeUnitField q j) (fun _ => 0)
  let input := cstream A w (chirpLine s B)++tail
  let output := cstream A w (chirpLine s D)++(cstream A w (chirpLine s C)++S.R 132)
  have hex' : ExecWithin (embTab boundaryArithmeticReg (embTab componentReg (embTab groupReg body)))
      (fun d z => mnSize z+d ≤ mnSize (mk (embDn tableReg v₁) (embStk tableReg S₁))+0+indexedCyclicColumnWorkspace (P₀ := P₀) (Q := Q) (A := A) (U := U)
          J ringPush batchPush rowPush p l s t u target a n k)
      0 (indexedCyclicColumn hR hQ)
      (mk (embDn tableReg v₁) (embStk tableReg S₁)) m₂
      (mk vi {(embStk tableReg S₁) with R := (Function.update (Function.update
        (Function.update (embStk tableReg S₁).R 0 []) 110 input) 132 output)}) := by
    simpa [embStk,tableReg,S₁,input,output,B,q,w,band,j,boundary] using hex
  obtain ⟨v₂,hv₂,he₂⟩ := exec_emb_rightUpdates_within_stock tableReg tableReg_injective
    (indexedCyclicColumn hR hQ) v₁ S₁ vi m₂ 0 (indexedCyclicColumnWorkspace (P₀ := P₀) (Q := Q) (A := A) (U := U)
          J ringPush batchPush rowPush p l s t u target a n k) [(0,[]),(110,input),(132,output)] hvi hex'
  have hfinal : {S₁ with R := (Function.update (Function.update (Function.update S₁.R (tableReg 0) [])
      (tableReg 110) input) (tableReg 132) output)} = {S with R := Function.update (Function.update S.R 110 input) 132 output} := by
    ext1
    · rfl
    · rfl
    · rfl
    · funext r
      by_cases hr : r = 0 <;> simp [S₁,tableReg,hr,h0,Function.update_apply]
  have hcopy : mnNativePushBound 2 (ucopy (P := P₀) (Q := Q) (A := A) (U := U) (151 : Fin 154) 0 135) := by
    simp [ucopy,umulSym,scanR,drainR,popDo,keepIn,pushN,moveR,moveStep,whileR,peekR,mnNativePushBound,mnActPush]
  have ht₁ := mn_native_exec_within he₁' 2 hcopy 0 _ (Nat.le_refl _)
  have ht := (mn_seq_within_add ht₁ he₂).mono (J := fun d z => mnSize z+d ≤ mnSize (mk v S)+0+retainedIndexedCyclicColumnWorkspace (P₀ := P₀) (Q := Q) (A := A) (U := U)
            J ringPush batchPush rowPush p l s t u target a n k) (by
    intro d z hz
    unfold retainedIndexedCyclicColumnWorkspace
    exact hz)
  refine ⟨v₂,(4*k+4)+m₂,C,D,hv₂.trans hv₁,Nat.add_le_add_left hm₂ _,
    ht.cast rfl (congrArg (mk v₂) hfinal),hreal,hnorm,herror,?_⟩
  have hp132 := tableProject_updateR_inner {S with R := Function.update S.R 110 input} (132 : Fin 151) output
  have hc132 : tableReg (132 : Fin 151) = (132 : Fin 154) := by decide
  rw [hc132] at hp132
  have hp110 := tableProject_updateR_inner S (110 : Fin 151) input
  have hc110 : tableReg (110 : Fin 151) = (110 : Fin 154) := by decide
  rw [hc110] at hp110
  change LengthKeyReady _ _ _ _ _ _ _ _ _ _ _ (embStk componentReg (embStk boundaryArithmeticReg
    (embStk tableReg {S with R := Function.update (Function.update S.R 110 input) 132 output})))
  rw [hp132,hp110]
  have hstate : {(embStk tableReg S₁) with R := (Function.update (Function.update
      (Function.update (embStk tableReg S₁).R 0 []) 110 input) 132 output)} =
      {(embStk tableReg S) with R := Function.update (Function.update (embStk tableReg S).R 110 input) 132 output} := by
    rw [← hreset]
  rw [← hstate]
  simpa [embStk,tableReg,S₁,input,output,B,q,w,band,j,boundary] using hready₂

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
