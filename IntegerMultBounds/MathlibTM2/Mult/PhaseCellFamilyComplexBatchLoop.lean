module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFamilyComplexBatchNumerics
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSharedPageComplexBatchReady
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCountedLoop

/-! Execute a complex input through both real solves on one retained factor page, restoring every borrowed tape. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.BandFactor
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.SchurDominance
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

def familyComplexBatchNext {A : ℕ} (S : Stacks 263 A)
    (input output tail : List (Fin (A+4))) : Stacks 263 A :=
  {S with R := (Function.update (Function.update (Function.update S.R 110 tail)
    241 (input.reverse++S.R 241)) 242 (output.reverse++S.R 242))}

theorem familyBoundaryReg_off (i : Fin 240) (j : Fin 263) (hj : 240 ≤ j.val) :
    familyBoundaryReg i ≠ j := by
  intro h
  have hv := congrArg Fin.val h
  change i.val = j.val at hv
  have hi := i.isLt
  omega

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 263 Q A U}

theorem familyComplexBatchLoop_spec (recovery : Bool) (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
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
    (S.R 243).length = s*w → S.R 244 = [] →
    (S.R 240).length = Fs.length → S.R 241 = [] → S.R 242 = [] →
    ∀ (x y : (ZMod s → GaussianInt) → ZMod s → ℝ),
    (∀ F ∈ Fs, Solves (realMatrix s t p u) (haloVertices s a b) (x F) (fun i => (value q (F i)).re)) →
    (∀ F ∈ Fs, Solves (realMatrix s t p u) (haloVertices s a b) (y F) (fun i => (value q (F i)).im)) →
    ∃ v' n, ∃ Zs : List (ZMod s → GaussianInt),
      v'.user = v.user ∧
      n ≤ Fs.length*(originalComponentInputsCost q s+familyBoundaryPairCost A p u l s t a b target V+(8*(s*w)+8)+3)+2 ∧
      Exec body (countedLoop 240 (familyComplexBatchStep recovery hR hQ)) (mk v S) n
        (mk v' {S with R := (Function.update (Function.update (Function.update (Function.update S.R
          110 tail) 241 (cstream A w (Fs.map (chirpLine s)).flatten).reverse)
            242 (cstream A w (Zs.map (chirpLine s)).flatten).reverse) 240 [])}) ∧
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
    hclock htmp hcount h241 h242 x y hx hy
  let words := fun (Fs : List (ZMod s → GaussianInt)) => cstream A w (Fs.map (chirpLine s)).flatten
  let Good := fun F Z => PhaseCellInterface.ErrorOn (haloVertices s a b)
    (pairedCellRead q w (cstream A w (chirpLine s Z)++S.R 132))
      (fun i => (⟨x F i,y F i⟩ : ℂ)) (1/(2 : ℝ)^target)
  let changed : List (Fin 263) := [110,240,241,242]
  let Inv := fun j (R : Stacks 263 A) =>
    R.inp = S.inp ∧ R.out = S.out ∧ R.L = S.L ∧
    (∀ k, k ∉ changed → R.R k = S.R k) ∧
    R.R 110 = words (Fs.drop j)++tail ∧
    R.R 241 = (words (Fs.take j)).reverse ∧
    ∃ Zs, R.R 242 = (words Zs).reverse ∧ List.Forall₂ Good (Fs.take j) Zs
  have hstable : ∀ j R xs, Inv j R → Inv j {R with R := Function.update R.R 240 xs} := by
    intro j R xs ⟨hi,ho,hl,hf,hs,ha,Zs,hb,hgood⟩
    refine ⟨hi,ho,hl,?_,?_,?_,Zs,?_,hgood⟩
    · intro k hk
      have hn : k ≠ 240 := by intro he; subst k; exact hk (by simp [changed])
      simpa only [Function.update_of_ne hn] using hf k hk
    · simpa using hs
    · simpa using ha
    · simpa using hb
  have hstep : ∀ j < Fs.length, ∀ (vi : HS 263 Q A U) R, Inv j R →
      ∃ vf R' n, vf.user = vi.user ∧
        n ≤ originalComponentInputsCost q s+familyBoundaryPairCost A p u l s t a b target V+(8*(s*w)+8) ∧
        Exec body (familyComplexBatchStep recovery hR hQ) (mk vi R) n (mk vf R') ∧
        R'.R 240 = R.R 240 ∧ Inv (j+1) R' := by
    intro j hj vi R ⟨hi,ho,hl,hf,hsource,hsaved,Zs,houtputs,hgood⟩
    have hcore : embStk familyBoundaryReg R =
        {(embStk familyBoundaryReg S) with R :=
          (Function.update (embStk familyBoundaryReg S).R 110 (R.R 110))} := by
      refine Stacks.ext hi ho ?_ ?_
      · funext i; exact congrFun hl _
      · funext i
        by_cases hn : i = 110
        · subst i; rfl
        have hne : familyBoundaryReg i ≠ 110 := familyBoundaryReg_injective.ne hn
        simp only [Function.update_of_ne hn]
        exact hf _ (by
          simp only [changed,List.mem_cons,List.not_mem_nil,or_false,not_or]
          exact ⟨hne,familyBoundaryReg_off i 240 (by decide),
            familyBoundaryReg_off i 241 (by decide),familyBoundaryReg_off i 242 (by decide)⟩)
    have hreg (i : Fin 263) (hn : i ≠ 110) (hi : i.val < 240) : R.R i = S.R i := by
      apply hf i
      simp only [changed,List.mem_cons,List.not_mem_nil,or_false,not_or]
      refine ⟨hn,?_,?_,?_⟩ <;> intro h <;> have := congrArg Fin.val h <;> omega
    have hfactor : boundaryFactorState (embStk sharedPageRecoveryReg (embStk familyBoundaryReg R)) =
        boundaryFactorState (embStk sharedPageRecoveryReg (embStk familyBoundaryReg S)) := by
      rw [hcore]
      funext r
      cases r <;> first | rfl | (rename_i c; cases c <;> rfl)
    have hsrc : R.R 110 = cstream A w (chirpLine s Fs[j])++(words (Fs.drop (j+1))++tail) := by
      rw [List.drop_eq_getElem_cons hj] at hsource
      simpa only [words,List.map_cons,List.flatten_cons,cstream_append,List.append_assoc] using hsource
    have hprojR : embStk familyCouplingSourceReg R =
        {embStk familyCouplingSourceReg S with R := Function.update (embStk familyCouplingSourceReg S).R 110 (R.R 110)} := by
      refine Stacks.ext hi ho ?_ ?_
      · funext i; exact congrFun hl _
      · funext i
        by_cases hn : i = 110
        · subst i; rfl
        have hne : familyCouplingSourceReg i ≠ (110 : Fin 263) := familyCouplingSourceReg_injective.ne hn
        change R.R (familyCouplingSourceReg i) = Function.update (embStk familyCouplingSourceReg S).R 110 (R.R 110) i
        rw [Function.update_of_ne hn]
        exact hreg (familyCouplingSourceReg i) hne ((familyCouplingSourceReg_lt i).trans (by decide))
    have hreadyR : LengthKeyReady (2^15*p)
        (executionStagePrecision p l (initialSchurTarget p u bits 2) 2+1) q l s t u
        (PhaseCellBand.width p u) 0 0 (R.R 110) (embStk familyCouplingSourceReg R) := by
      rw [hprojR]; exact hready.update_source _
    rw [hsrc] at hreadyR
    have hcacheR : CouplingPageCacheReady recovery (2^15*p) q w s t u
        (PhaseCellBand.width p u) a b pageTail (embStk familyInverseLegacyReg R) := by
      apply hcache.of_frame
      intro i
      apply hf
      have hi := couplingCachePort_ge recovery i
      simp only [changed,List.mem_cons,List.not_mem_nil,or_false,not_or]
      refine ⟨?_,?_,?_,?_⟩ <;> intro h <;> have hv := congrArg Fin.val h <;>
        dsimp [familyInverseLegacyReg] at hv <;> omega
    have hmem : Fs[j] ∈ Fs := List.getElem_mem hj
    obtain ⟨vf,n,Z,hu',hn,he,herror⟩ := familyComplexBatchStep_spec (body := body)
      recovery hR hQ hA hp hwidth hα hst hu hαu hθ hgap hbudget hband has hbs hpad
      columns hlen hformat hstage htable Fs[j] (hF _ hmem) vi R
      (words (Fs.drop (j+1))++tail) coordinateTail pageTail familyTail V hreadyR hcacheR
      (by rw [hf 260 (by simp [changed])]; exact hfamily) (by
        intro i hi
        have hiChanged : i ∉ changed := by
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
          rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
        exact (hf i hiChanged).trans (hfamilyFresh i hi))
      (by rw [hreg 141 (by decide) (by decide)]; exact ha) (by rw [hreg 142 (by decide) (by decide)]; exact hb)
      (by intro i; exact (congrFun hl _).trans (hleft i))
      (by intro i; rw [hreg ⟨i.val,by omega⟩ (by intro he; have hv := congrArg Fin.val he; have hi := i.isLt; dsimp at hv; omega) (by have hi := i.isLt; change i.val < 240; omega)]; exact hmul i)
      (by rw [hfactor]; exact hsolve) (by rw [hfactor]; exact hbo)
      (by rw [hfactor]; exact hhf) (by rw [hfactor]; exact hdf) hsV
      (by rw [hreg 116 (by decide) (by decide)]; exact hN) (by rw [hreg 115 (by decide) (by decide)]; exact hV)
      (by rw [hreg 160 (by decide) (by decide)]; exact hw) (by rw [hreg 109 (by decide) (by decide)]; exact hcoordinates)
      (by rw [hreg 119 (by decide) (by decide)]; exact hmaster)
      (by
        intro i himem
        have hne : i ≠ 110 := by intro he; subst i; norm_num at himem
        have hilow : i.val < 240 := by
          simp only [List.mem_cons,List.not_mem_nil,or_false] at himem
          rcases himem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
        exact (hreg i hne hilow).trans (hclean i himem))
      (by rw [hreg 116 (by decide) (by decide)]; exact hc) (by rw [hreg 192 (by decide) (by decide)]; exact hrows)
      (by rw [hreg 121 (by decide) (by decide)]; exact hs) borrowed (by rw [hreg 239 (by decide) (by decide)]; exact hadv)
      (by rw [hf 243 (by decide)]; exact hclock) ((hf 244 (by decide)).trans htmp)
      (x Fs[j]) (y Fs[j]) (hx _ hmem) (hy _ hmem)
    let R' := familyComplexBatchNext R (cstream A w (chirpLine s Fs[j]))
      (cstream A w (chirpLine s Z)) (words (Fs.drop (j+1))++tail)
    refine ⟨vf,R',n,hu',hn,he,by simp [R',familyComplexBatchNext],hi,ho,hl,?_,?_,?_,Zs++[Z],?_,?_⟩
    · intro k hk
      have h110 : k ≠ 110 := by intro he; subst k; exact hk (by simp [changed])
      have h241' : k ≠ 241 := by intro he; subst k; exact hk (by simp [changed])
      have h242' : k ≠ 242 := by intro he; subst k; exact hk (by simp [changed])
      simpa [R',familyComplexBatchNext,h110,h241',h242'] using hf k hk
    · simp [R',familyComplexBatchNext]
    · change (cstream A w (chirpLine s Fs[j])).reverse++R.R 241 = (words (Fs.take (j+1))).reverse
      rw [hsaved]
      change (cstream A w (chirpLine s Fs[j])).reverse++
        (cstream A w ((Fs.take j).map (chirpLine s)).flatten).reverse =
          (cstream A w ((Fs.take (j+1)).map (chirpLine s)).flatten).reverse
      rw [List.take_succ_eq_append_getElem hj]
      simp only [List.map_append,List.map_cons,List.map_nil,List.flatten_append,List.flatten_cons,
        List.flatten_nil,List.append_nil,cstream_append,List.reverse_append]
    · change (cstream A w (chirpLine s Z)).reverse++R.R 242 = (words (Zs++[Z])).reverse
      rw [houtputs]
      simp [words,List.map_append,List.flatten_append,cstream_append]
    · rw [List.take_succ_eq_append_getElem hj]
      apply List.rel_append hgood
      exact .cons (by simpa only [Good,hf 132 (by decide)] using herror) .nil
  have hInv : Inv 0 S := by
    refine ⟨rfl,rfl,rfl,fun _ _ => rfl,?_,?_,[],?_,.nil⟩
    · exact hready.source
    · simpa [words] using h241
    · simpa [words] using h242
  obtain ⟨v',S',n,hu',hn,he,h240,hi,ho,hl,hf,hsource,hsaved,Zs,houtputs,hgood⟩ :=
    countedLoop_exec (body := body) 240 (familyComplexBatchStep recovery hR hQ) Fs.length
      (originalComponentInputsCost q s+familyBoundaryPairCost A p u l s t a b target V+(8*(s*w)+8))
      Inv hstable hstep v S hcount hInv
  refine ⟨v',n,Zs,hu',hn,he.cast rfl ?_,?_⟩
  · apply congrArg (mk v')
    refine Stacks.ext hi ho hl ?_
    funext k
    by_cases h110 : k = 110
    · subst k; simpa [words] using hsource
    by_cases h241' : k = 241
    · subst k; simpa using hsaved
    by_cases h242' : k = 242
    · subst k; simpa using houtputs
    by_cases h240' : k = 240
    · subst k; simpa using h240
    simpa [h110,h241',h242',h240'] using hf k (by simp [changed,h110,h241',h242',h240'])
  · change List.Forall₂ Good Fs Zs
    simpa only [List.take_length] using hgood

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
