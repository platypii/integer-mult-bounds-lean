module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicResidualPhysical
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicBoundaryRhsPhysical
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetireCyclicResidualPhysical
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicPreparedBoundaryColumns

/-! Produce one joint cyclic residual row without touching the prepared factors. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.BandFactor
variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

noncomputable def cyclicResidualRow (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P₀ 224 Q A U :=
  .seq (cyclicResidualPhysical hR hQ) (.seq cyclicBoundaryRhsPhysical retireCyclicResidualPhysical)

theorem cyclicResidualRow_spec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {p l s t u target a n : ℕ} [NeZero s] {α d : ℝ}
    (axis : RecoveryAxisBounds s t p u l α d) (ha : a < s) (hn : n ≤ s) :
    let q := executionPrecision p l (initialSchurTarget p u target 2) 2
    let w := executionWidth p l (initialSchurTarget p u target 2) 2
    let band := PhaseCellBand.width p u
    let B := cyclicPrincipalBoundary s t band a n
    let V := publicationGeometryWidth t band
    ∀ (rhs : ZMod s → GaussianInt), (∀ i, ‖value q (rhs i)‖ ≤ (2 : ℝ)^2) →
    ∀ (v : HS 224 Q A U) (S : Stacks 224 A) (tail pageTail : List (Fin (A+4))),
    LengthKeyReady (2^15*p) (executionStagePrecision p l (initialSchurTarget p u target 2) 2+1)
      q l s t u band 0 0 (cstream A w (chirpLine s rhs)++tail)
      (embStk componentReg (embStk boundaryArithmeticReg (embStk tableReg (embStk boundaryFactorLegacyReg S)))) →
    (S.R 116).length = B.card → (S.R 115).length = V →
    S.R 109 = cstream A V ((bFoldOrder s B).map
      (fun k : ZMod s => (⟨(k.val : ℤ),0⟩ : GaussianInt)))++pageTail →
    (S.R 144).length = a → (S.R 145).length = a+min n (s-a) →
    (S.R 146).length = n-min n (s-a) →
    (∀ k ∈ [(127 : Fin 224),138,139,141,142,143,147], S.R k = []) → S.R 206 = [] →
    ∃ v' m, ∃ F : ZMod s → GaussianInt, ∃ R : (ZMod s → ℝ) → ZMod s → ℝ,
      let rows := (List.range B.card).map (fun j => F (bFoldAt s B j))
      v'.user = v.user ∧
      m ≤ (windowedSchurResidualCost p l s t u target 2 a (a+min n (s-a))+
        windowedSchurResidualCost p l s t u target 2 0 (n-min n (s-a)))+
        cyclicBoundaryRhsPrepareCost B q V a (a+min n (s-a))+retireCyclicResidualsCost q s ∧
      Exec (embTab boundaryFactorLegacyReg (embTab tableReg (embTab boundaryArithmeticReg
        (embTab componentReg (embTab groupReg body))))) (cyclicResidualRow hR hQ)
        (mk v S) m (mk v' {S with R := Function.update S.R 206 (cstream A w rows)}) ∧
      rows.length = B.card ∧ (∀ z ∈ rows, z.im = 0) ∧
      (∀ z ∈ rows, |gv q z.re| ≤ (2 : ℝ)^couplingRowExponent 2 (stableInteriorExponent p 2) (8*p+1) (couplingCountExponent p u) ∧
        |gv q z.im| ≤ (2 : ℝ)^couplingRowExponent 2 (stableInteriorExponent p 2) (8*p+1) (couplingCountExponent p u)) ∧
      (∀ b, SchurDominance.Solves (realMatrix s t p u) (cyclicPrincipalInterior s t band a n)
        (R b) b) ∧
      (∀ i ∈ B, |(value q (F i)).re-SchurDominance.residual (realMatrix s t p u)
        (cyclicPrincipalInterior s t band a n)
        R
        (fun k => (value q (rhs k)).re) i| ≤ (1/(2 : ℝ)^(recoveryTarget p target+2))/(8*(p : ℝ))) := by
  dsimp only
  let q := executionPrecision p l (initialSchurTarget p u target 2) 2
  let w := executionWidth p l (initialSchurTarget p u target 2) 2
  let band := PhaseCellBand.width p u
  let B := cyclicPrincipalBoundary s t band a n
  let V := publicationGeometryWidth t band
  let native := embTab boundaryFactorLegacyReg (embTab tableReg (embTab boundaryArithmeticReg
    (embTab componentReg (embTab groupReg body))))
  intro rhs hrhs v S tail pageTail hready hN hV hpage haSrc hleftEnd hrightEnd hfresh hvk
  obtain ⟨v₁,m₁,C,D,R,T,hsolver,hv₁,hm₁,he₁,hreal,hnorm,herror,hready₁⟩ :=
    cyclicResidualPhysical_spec (body := body) (target := target) (rhsExp := 2)
      hR hQ hA axis.hp axis.hpacket axis.hα axis.hst axis.hu axis.hαu axis.hθ axis.hgap axis.hbudget axis.hband ha hn axis.hpad
      rhs hrhs v S tail haSrc hleftEnd hrightEnd
      (by intro k hk
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
          rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> exact hfresh _ (by simp)) hready
  let output := cstream A w (chirpLine s D)++(cstream A w (chirpLine s C)++S.R 132)
  let S₁ : Stacks 224 A := {S with R := Function.update S.R 132 output}
  have hq : (S₁.R 119).length = q := by
    simpa [S₁,embStk,componentReg,boundaryArithmeticReg,tableReg,boundaryFactorLegacyReg,groupHeaderValue] using
      hready.masters (119,112) (by simp [groupHeaderCopies])
  have hs : (S₁.R 121).length = s := by
    simpa [S₁,embStk,componentReg,boundaryArithmeticReg,tableReg,boundaryFactorLegacyReg,groupHeaderValue] using
      hready.masters (121,97) (by simp [groupHeaderCopies])
  have hscratch : ∀ k ∈ [(94 : Fin 224),106,134,135,136,137,138,139,140,150], S₁.R k = [] := by
    intro k hk
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simpa [S₁,embStk,componentReg,boundaryArithmeticReg,tableReg,boundaryFactorLegacyReg] using hready.blank 94 (by decide) (by decide) (by decide)
    · simpa [S₁,embStk,componentReg,boundaryArithmeticReg,tableReg,boundaryFactorLegacyReg] using hready.blank 106 (by decide) (by decide) (by decide)
    · simpa [S₁,embStk,componentReg,boundaryArithmeticReg,tableReg,boundaryFactorLegacyReg] using hready.fresh 134 (by simp)
    · simpa [S₁,embStk,componentReg,boundaryArithmeticReg,tableReg,boundaryFactorLegacyReg] using hready.fresh 135 (by simp)
    · simpa [S₁,embStk,componentReg,boundaryArithmeticReg,tableReg,boundaryFactorLegacyReg] using hready.fresh 136 (by simp)
    · simpa [S₁,embStk,componentReg,boundaryArithmeticReg,tableReg,boundaryFactorLegacyReg] using hready.fresh 137 (by simp)
    · simpa [S₁] using hfresh 138 (by simp)
    · simpa [S₁] using hfresh 139 (by simp)
    · simpa [S₁,embStk,componentReg,boundaryArithmeticReg,tableReg,boundaryFactorLegacyReg] using hready.fresh 140 (by simp)
    · simpa [S₁,embStk,componentReg,boundaryArithmeticReg,tableReg,boundaryFactorLegacyReg] using hready.blank 116 (by decide) (by decide) (by decide)
  have hbound : ∀ i ∈ B, |gv q (if a ≤ i.val ∧ i.val < a+min n (s-a) then C i else D i).re| ≤
      (2 : ℝ)^couplingRowExponent 2 (stableInteriorExponent p 2) (8*p+1) (couplingCountExponent p u) ∧
      |gv q (if a ≤ i.val ∧ i.val < a+min n (s-a) then C i else D i).im| ≤
      (2 : ℝ)^couplingRowExponent 2 (stableInteriorExponent p 2) (8*p+1) (couplingCountExponent p u) := by
    intro i _
    split_ifs
    · exact ⟨by simpa [value,gv] using (Complex.abs_re_le_norm _).trans (hnorm i).1,
        by simpa [value,gv] using (Complex.abs_im_le_norm _).trans (hnorm i).1⟩
    · exact ⟨by simpa [value,gv] using (Complex.abs_re_le_norm _).trans (hnorm i).2,
        by simpa [value,gv] using (Complex.abs_im_le_norm _).trans (hnorm i).2⟩
  let rows := (List.range B.card).map (fun j =>
    let i := bFoldAt s B j
    if a ≤ i.val ∧ i.val < a+min n (s-a) then C i else D i)
  have hwide : s+s ≤ 2^V := by
    have hfit := publicationGeometryWidth_fits t (PhaseCellBand.width p u)
    change s+s ≤ 2^(publicationGeometryWidth t (PhaseCellBand.width p u))
    nlinarith only [hfit,axis.hst]
  have hw : w = 2*q+8 := by dsimp [w,q,executionWidth,executionPrecision]; omega
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := cyclicBoundaryRhsPhysical_exec (body := native)
    B q V a (a+min n (s-a)) (by omega) hwide ha.le (by omega) C D pageTail (S.R 132) v₁ S₁
    (by simpa [S₁] using hN) (by simpa [S₁] using hV) (by simpa [S₁] using hpage)
    hq hs (by simpa [S₁] using haSrc) (by simpa [S₁] using hleftEnd)
    (by simp only [S₁,Function.update_self,output,hw])
    (by simpa [S₁,embStk,componentReg,boundaryArithmeticReg,tableReg,boundaryFactorLegacyReg] using
      hready.blank 0 (by decide) (by decide) (by decide)) hscratch
    (by intro k hk hk0
        let j : Fin 144 := ⟨k.val,by omega⟩
        have h := hready.blank j (by change k.val < 117; omega)
          (by intro heq; have hv := congrArg Fin.val heq; change k.val = 93 at hv; omega)
          (by intro heq; have hv := congrArg Fin.val heq; change k.val = 110 at hv; omega)
        have h109 : componentReg j ≠ 109 := by
          intro heq; have hv := congrArg Fin.val heq; change k.val = 109 at hv; omega
        have h115 : componentReg j ≠ 115 := by
          intro heq; have hv := congrArg Fin.val heq; change k.val = 115 at hv; omega
        have h116 : componentReg j ≠ 116 := by
          intro heq; have hv := congrArg Fin.val heq; change k.val = 116 at hv; omega
        have harith : boundaryArithmeticReg (componentReg j) = ⟨k.val,by omega⟩ := by
          unfold boundaryArithmeticReg
          rw [ite_eq_right h109,ite_eq_right h115,ite_eq_right h116]
          rfl
        have heq : boundaryFactorLegacyReg (tableReg (boundaryArithmeticReg (componentReg j))) = k := by
          rw [harith]
          rfl
        change S.R (boundaryFactorLegacyReg (tableReg (boundaryArithmeticReg (componentReg j)))) = [] at h
        rw [heq] at h
        have hne : k ≠ 132 := by
          intro heq; have hv := congrArg Fin.val heq; change k.val = 132 at hv; omega
        simpa [S₁,hne] using h)
  let S₂ : Stacks 224 A := {S₁ with R := Function.update S₁.R 206 (cstream A w rows)}
  have he₂' : Exec native cyclicBoundaryRhsPhysical (mk v₁ S₁) m₂ (mk v₂ S₂) := by
    simpa only [S₂,rows,S₁,hw,hvk,Function.update_of_ne (show (206 : Fin 224) ≠ 132 by decide),List.append_nil] using he₂
  have hretire : ∀ k ∈ [(94 : Fin 224),131,134,135,138], S₂.R k = [] := by
    intro k hk
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl
    · simpa [S₂,S₁] using hscratch 94 (by simp)
    · simpa [S₂,S₁,embStk,componentReg,boundaryArithmeticReg,tableReg,boundaryFactorLegacyReg] using hready.fresh 131 (by simp)
    · simpa [S₂,S₁] using hscratch 134 (by simp)
    · simpa [S₂,S₁] using hscratch 135 (by simp)
    · simpa [S₂,S₁] using hscratch 138 (by simp)
  obtain ⟨v₃,m₃,hu₃,hm₃,he₃⟩ := retireCyclicResidualPhysical_exec (body := native) q s
    (cstream A w (chirpLine s D)) (cstream A w (chirpLine s C)) (S.R 132)
    (by simp [chirpLine,hw]) (by simp [chirpLine,hw]) v₂ S₂
    (by simpa [S₂,S₁] using hq) (by simpa [S₂,S₁] using hs)
    (by simp [S₂,S₁,output]) hretire
  refine ⟨v₃,m₁+(m₂+m₃),
    (fun i => if a ≤ i.val ∧ i.val < a+min n (s-a) then C i else D i),
    (fun b k => if k ∈ haloInterior s t band a (a+min n (s-a)) then R b k else T b k),hu₃.trans (hu₂.trans hv₁),(by
      dsimp only [q,w,B,V,band] at hm₁ hm₂ hm₃ ⊢
      omega),
    (Exec.seq he₁ (Exec.seq he₂' he₃)).cast rfl ?_,by simp,?_,?_,hsolver,?_⟩
  · apply congrArg (mk v₃)
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases h132 : k = 132 <;> by_cases h206 : k = 206 <;>
      simp [S₂,S₁,rows,w,B,band,h132,h206]
  · intro z hz
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hz
    dsimp only
    split_ifs
    · exact (hreal _).1
    · exact (hreal _).2
  · intro z hz
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hz
    exact hbound _ (bFoldAt_mem s B j (List.mem_range.mp hj))
  · intro i hi
    simpa only [mem_haloVertices,apply_ite] using herror i hi

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
