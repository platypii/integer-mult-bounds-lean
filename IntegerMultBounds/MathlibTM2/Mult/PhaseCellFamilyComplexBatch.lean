module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFamilyComplexBatchFinish
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupOps
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedBoundaryBatch

/-! Execute a complex input through both real solves on one retained factor page, restoring every borrowed tape. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.BandFactor
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.SchurDominance
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 263 Q A U}

noncomputable def familyComplexBatch (recovery : Bool) (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P 263 Q A U :=
  .seq (unaryProduct 121 160 243 245 244)
    (.seq (ucopy 246 240 244)
      (.seq (countedLoop 240 (familyComplexBatchStep recovery hR hQ)) familyComplexBatchFinish))

theorem familyComplexBatch_spec (recovery : Bool) (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {p l s t u target a b : ℕ} [NeZero s] {α d : ℝ}
    (hp : 2 ≤ p) (hwidth : 8*p ≤ 2^u) (hα : 0 < α) (hst : s < t) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hband : PhaseCellBand.width p u ≤ s) (has : a ≤ s) (hbs : b ≤ s)
    (hpad : 2*((s/(t-s)+1)-2*PhaseCellBand.width p u) ≤ 2^l+1) :
    let B := haloBoundary s t (PhaseCellBand.width p u) a b
    let band := PhaseCellBand.width p u
    let W := 12*band+1
    let bits := boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2 B.card
    let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
    let w := executionWidth p l (initialSchurTarget p u bits 2) 2
    let K := factorNewtonSteps p q
    ∀ (columns : List (ZMod s → GaussianInt)),
    let AZ := factorRankIntegerMatrix B W columns
    let Lc := naturalLineLc q K W B.card AZ
    let Uc := naturalLineUc q K W B.card AZ
    let rcs := naturalLineRcs q K W B.card AZ
    columns.length = B.card → ColumnFamilyFormat w columns →
    StageInv (factorRankMatrix A q w B W columns) (Finset.range B.card)
      (1/(8*(p : ℝ))-(B.card : ℝ)*(1/(2 : ℝ)^bits)) (2+(B.card : ℝ)*(1/(2 : ℝ)^bits)) →
    (∀ i ∈ B, ∀ j ∈ B, |bandBoundaryTable B W (computedBoundaryTable A q w B columns) i j-
      (SchurDominance.run (realMatrix s t p u) (haloVertices s a b) (haloInterior s t band a b).toList).1 i j| ≤ 1/(2 : ℝ)^bits) →
    ∀ (Fs : List (ZMod s → GaussianInt)), (∀ F ∈ Fs, ∀ i, ‖value q (F i)‖ ≤ (2 : ℝ)^2) →
    ∀ (v : HS 263 Q A U) (S : Stacks 263 A) (tail coordinateTail pageTail familyTail : List (Fin (A+4))) (V : ℕ),
    let σ := boundaryFactorState (embStk sharedPageRecoveryReg (embStk familyBoundaryReg S))
    LengthKeyReady (2^15*p) (executionStagePrecision p l (initialSchurTarget p u bits 2) 2+1)
      q l s t u band 0 0 (cstream A w (Fs.map (chirpLine s)).flatten++tail)
      (embStk familyCouplingSourceReg S) →
    CouplingPageCacheReady recovery (2^15*p) q w s t u band a b pageTail (embStk familyInverseLegacyReg S) →
    S.R 260 = weightKeyFamily (haloWeightKeyPages A w q (2^15*p) s t u band a b (haloLengthKeys s t band a b))++familyTail →
    (∀ i ∈ ([(256 : Fin 263),257,258,259,261,262] : List (Fin 263)), S.R i = []) →
    (S.R 141).length = a → (S.R 142).length = b →
    (∀ i : Fin 240, (embStk familyBoundaryReg S).L i = []) → (∀ i : Fin 64, S.R ⟨i.val,by omega⟩ = []) →
    BoundarySolveReady σ q w W B.card →
    σ .bo = cstream A w (Lc.map colC).flatten →
    σ .hf = cstream A w (Uc.map colC).flatten →
    σ .df = cstream A w (rcs.map fun x => (⟨x,0⟩ : GaussianInt)) →
    s ≤ 2^V → (S.R 116).length = B.card → (S.R 115).length = V → (S.R 160).length = w →
    S.R 109 = cstream A V ((bFoldOrder s B).map (fun k : ZMod s => (⟨(k.val : ℤ),0⟩ : GaussianInt)))++coordinateTail →
    (S.R 119).length = q →
    (∀ i ∈ ([127,138,143,106,139,206,223,184,220,221,225,217,201,208,211,215,231,232,233,234,235,236,237,94,131,134,135,136,140,147] : List (Fin 263)), S.R i = []) →
    S.R 116 = List.replicate B.card tick → (S.R 192).length = B.card → (S.R 121).length = s →
    ∀ (borrowed : List (Fin (A+4))),
    S.R 239 = gatherControls A (originAdvances w 0 (boundaryScatterOrigins s B)++[0])++borrowed →
    (S.R 246).length = Fs.length →
    (∀ i ∈ ([240,241,242,243,244,245] : List (Fin 263)), S.R i = []) →
    ∀ (x y : (ZMod s → GaussianInt) → ZMod s → ℝ),
    (∀ F ∈ Fs, Solves (realMatrix s t p u) (haloVertices s a b) (x F) (fun i => (value q (F i)).re)) →
    (∀ F ∈ Fs, Solves (realMatrix s t p u) (haloVertices s a b) (y F) (fun i => (value q (F i)).im)) →
    ∃ v' n, ∃ Zs : List (ZMod s → GaussianInt),
      v'.user = v.user ∧
      n ≤ s*(4*w+9)+4+(4*Fs.length+4)+(Fs.length*(originalComponentInputsCost q s+familyBoundaryPairCost A p u l s t a b target V+(8*(s*w)+8)+3)+2)+(4*(Fs.length*s*w)+2*(s*w)+6) ∧
      Exec body (familyComplexBatch recovery hR hQ) (mk v S) n
        (mk v' {S with R := (Function.update S.R 132
          (cstream A w (Zs.map (chirpLine s)).flatten++S.R 132))}) ∧
      List.Forall₂ (fun F Z => PhaseCellInterface.ErrorOn (haloVertices s a b)
        (pairedCellRead q w (cstream A w (chirpLine s Z)++S.R 132))
          (fun i => (⟨x F i,y F i⟩ : ℂ)) (1/(2 : ℝ)^target)) Fs Zs := by
  dsimp only
  let B := haloBoundary s t (PhaseCellBand.width p u) a b
  let bits := boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2 B.card
  let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
  let w := executionWidth p l (initialSchurTarget p u bits 2) 2
  intro columns hlen hformat hstage htable Fs hF v S tail coordinateTail pageTail familyTail V hready hcache hfamily hfamilyFresh ha hb hleft hmul
    hsolve hbo hhf hdf hsV hN hV hw hcoordinates hmaster hclean hc hrows hs borrowed hadv
    hcount hfresh x y hx hy
  let raw := cstream A w (Fs.map (chirpLine s)).flatten
  have hrawLen : raw.length = Fs.length*s*w := by
    simpa only [List.length_map] using cstream_flatten_length (A := A) w s (Fs.map (chirpLine s))
      (by intro xs hxs; obtain ⟨F,hF,rfl⟩ := List.mem_map.mp hxs; simp [chirpLine])
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := unaryProduct_exec (body := body)
    (a := 121) (b := 160) (dst := 243) (t₁ := 245) (t₂ := 244) (by decide)
    v S (hfresh 245 (by simp)) (hfresh 244 (by simp))
  let S₁ : Stacks 263 A := {S with R := Function.update S.R 243 (List.replicate (s*w) tick)}
  have he₁' : Exec body (unaryProduct 121 160 243 245 244) (mk v S) n₁ (mk v₁ S₁) := by
    simpa only [show (S.R 121).length = s from hs, show (S.R 160).length = w from hw,
      hfresh 243 (by simp),List.append_nil] using he₁
  have hn₁' : n₁ ≤ s*(4*w+9)+4 := by
    simpa only [show (S.R 121).length = s from hs,show (S.R 160).length = w from hw] using hn₁
  obtain ⟨v₂,hu₂,he₂⟩ := ucopy_exec (body := body) (a := 246) (b := 240) (t := 244)
    (by decide) (by decide) (by decide) v₁ S₁ (by simpa [S₁] using hfresh 244 (by simp))
  let S₂ : Stacks 263 A := {S₁ with R := Function.update S₁.R 240 (List.replicate Fs.length tick)}
  have he₂' : Exec body (ucopy 246 240 244) (mk v₁ S₁) (4*Fs.length+4) (mk v₂ S₂) := by
    simpa [S₂,S₁,hcount,hfresh 240 (by simp)] using he₂
  have hcore : embStk familyBoundaryReg S₂ = embStk familyBoundaryReg S := by
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    simp only [embStk,Function.comp_def,S₂,S₁,
      Function.update_of_ne (familyBoundaryReg_off i 240 (by decide)),
      Function.update_of_ne (familyBoundaryReg_off i 243 (by decide))]
  have hnative : embStk familyCouplingSourceReg S₂ = embStk familyCouplingSourceReg S := by
    change embStk familyCouplingSourceReg {S₁ with R := Function.update S₁.R 240 _} = _
    rw [familyCouplingSource_high_update S₁ 240 (by decide)]
    exact familyCouplingSource_high_update S 243 (by decide) _
  have hcache₂ : CouplingPageCacheReady recovery (2^15*p) q w s t u
      (PhaseCellBand.width p u) a b pageTail (embStk familyInverseLegacyReg S₂) := by
    apply hcache.of_frame
    intro i
    have hi := couplingCachePort_ge recovery i
    have hne (k : Fin 263) (hk : k.val < 248) : familyInverseLegacyReg (couplingCachePort recovery i) ≠ k := by
      intro h; have hv := congrArg Fin.val h; dsimp [familyInverseLegacyReg] at hv; omega
    simp [S₂,S₁,embStk,hne 240 (by decide),hne 243 (by decide)]
  have hclean₂ : ∀ i ∈ ([127,138,143,106,139,206,223,184,220,221,225,217,201,208,211,215,231,232,233,234,235,236,237,94,131,134,135,136,140,147] : List (Fin 263)), S₂.R i = [] := by
    intro i hi
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simpa [S₂,S₁] using hclean _ (by simp)
  obtain ⟨v₃,n₃,Zs,hu₃,hn₃,he₃,hgood,_htrace⟩ := familyComplexBatchLoop_spec (body := body)
    recovery hR hQ hA hp hwidth hα hst hu hαu hθ hgap hbudget hband has hbs hpad columns hlen hformat hstage htable
    Fs hF v₂ S₂ tail coordinateTail pageTail familyTail V
    (by rw [hnative]; exact hready) hcache₂
    (by simpa [S₂,S₁] using hfamily) (by
      intro i hi
      have hn (k : Fin 263) (hk : k.val < 256) : i ≠ k := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
        rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> intro he <;> subst k <;> norm_num at hk
      simpa [S₂,S₁,hn 240 (by decide),hn 243 (by decide)] using hfamilyFresh i hi) (by simpa [S₂,S₁] using ha) (by simpa [S₂,S₁] using hb)
    hleft (by
      intro i
      have hne (k : Fin 263) (hk : 64 ≤ k.val) : (⟨i.val,by omega⟩ : Fin 263) ≠ k := by
        intro h; have hv := congrArg Fin.val h; have hi := i.isLt
        change i.val = k.val at hv; omega
      simpa [S₂,S₁,hne 240 (by decide),hne 243 (by decide)] using hmul i) (by rw [hcore]; exact hsolve)
    (by rw [hcore]; exact hbo) (by rw [hcore]; exact hhf) (by rw [hcore]; exact hdf) hsV
    (by simpa [S₂,S₁] using hN) (by simpa [S₂,S₁] using hV) (by simpa [S₂,S₁] using hw)
    (by simpa [S₂,S₁] using hcoordinates) (by simpa [S₂,S₁] using hmaster) hclean₂
    (by simpa [S₂,S₁] using hc) (by simpa [S₂,S₁] using hrows) (by simpa [S₂,S₁] using hs)
    borrowed (by simpa [S₂,S₁] using hadv) (by change (S₂.R 243).length = s*w; simp [S₂,S₁])
    (by simpa [S₂,S₁] using hfresh 244 (by simp)) (by simp [S₂])
    (by simpa [S₂,S₁] using hfresh 241 (by simp)) (by simpa [S₂,S₁] using hfresh 242 (by simp)) x y hx hy
  let ys := cstream A w (Zs.map (chirpLine s)).flatten
  let S₃ : Stacks 263 A := {S₂ with R := (Function.update (Function.update (Function.update
    (Function.update S₂.R 110 tail) 241 raw.reverse) 242 ys.reverse) 240 [])}
  have hysLen : ys.length = Fs.length*s*w := by
    have hZs : Zs.length = Fs.length := hgood.length_eq.symm
    simpa only [List.length_map,hZs] using cstream_flatten_length (A := A) w s (Zs.map (chirpLine s))
      (by intro xs hxs; obtain ⟨F,hF,rfl⟩ := List.mem_map.mp hxs; simp [chirpLine])
  obtain ⟨v₄,hu₄,he₄⟩ := familyComplexBatchFinish_exec (body := body) v₃ S₃ raw ys
    (by simp [S₃]) (by simp [S₃])
  have hclock : (S₃.R 243).length = s*w := by simp [S₃,S₂,S₁]
  have he₄' := he₄
  rw [hrawLen,hysLen,hclock] at he₄'
  have hfinishCost : 2*(Fs.length*s*w)+2*(Fs.length*s*w)+2*(s*w)+6 =
      4*(Fs.length*s*w)+2*(s*w)+6 := by omega
  rw [hfinishCost] at he₄'
  refine ⟨v₄,n₁+((4*Fs.length+4)+(n₃+(4*(Fs.length*s*w)+2*(s*w)+6))),Zs,
    hu₄.trans (hu₃.trans (hu₂.trans hu₁)),?_,?_,?_⟩
  · have hbound : n₁+((4*Fs.length+4)+(n₃+(4*(Fs.length*s*w)+2*(s*w)+6))) ≤
        (s*(4*w+9)+4)+((4*Fs.length+4)+
          ((Fs.length*(originalComponentInputsCost q s+familyBoundaryPairCost A p u l s t a b target V+
            (8*(s*w)+8)+3)+2)+(4*(Fs.length*s*w)+2*(s*w)+6))) :=
      Nat.add_le_add hn₁' (Nat.add_le_add_left (Nat.add_le_add_right hn₃ _) _)
    simpa only [Nat.add_assoc] using hbound
  · exact (Exec.seq he₁' (Exec.seq he₂' (Exec.seq he₃ he₄'))).cast rfl (congrArg (mk v₄) (by
      refine Stacks.ext rfl rfl rfl ?_
      funext i
      have hsource : S.R 110 = raw++tail := hready.source
      by_cases h110 : i = 110 <;> by_cases h132 : i = 132 <;> by_cases h240 : i = 240 <;>
        by_cases h241 : i = 241 <;> by_cases h242 : i = 242 <;> by_cases h243 : i = 243 <;>
        simp [S₃,S₂,S₁,h110,h132,h240,h241,h242,h243,hsource,
          hfresh 240 (by simp),hfresh 241 (by simp),hfresh 242 (by simp),hfresh 243 (by simp)] <;> rfl))
  · exact hgood

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
