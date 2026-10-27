module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedCachedRealComponent
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedComponentControls
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSharedPageComponentFrame
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSharedPageFinishComponents
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPairedPhysicalRead

/-! Execute both real components with the same factor page and publication controls, then restore the borrowed original input. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.BandFactor
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.SchurDominance
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 256 Q A U}

noncomputable def placedCachedBoundaryPair (recovery : Bool) (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P 256 Q A U :=
  .seq (.seq (placedCachedRealComponent recovery hR hQ) placedComponentTransition)
    (.seq (placedCachedRealComponent recovery hR hQ) placedFinishComponents)

noncomputable def placedCachedBoundaryPairCost (p u l s t a b target V : ℕ) [NeZero s] : ℕ :=
  let N := (haloBoundary s t (PhaseCellBand.width p u) a b).card
  let bits := boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2 N
  let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
  2*placedCachedRealComponentCost p u l s t a b (target+1) V+
    cleanComponentTransitionCost q s+cleanFinishComponentsCost q s

private theorem transition_restore {A : ℕ} (S : Stacks 256 A)
    (output next parked : List (Fin (A+4))) :
    let S₁ : Stacks 256 A := {S with R := Function.update S.R 132 (output++S.R 132)}
    {S₁ with R := (Function.update (Function.update (Function.update (Function.update S₁.R
      110 next) 132 (S.R 132)) 144 parked) 145 (output++S₁.R 145))} =
      {S with R := (Function.update (Function.update (Function.update S.R 110 next) 144 parked)
        145 (output++S.R 145))} := by
  dsimp only
  refine Stacks.ext rfl rfl rfl ?_
  funext i
  by_cases hi110 : i = 110 <;> by_cases hi132 : i = 132 <;>
    by_cases hi144 : i = 144 <;> by_cases hi145 : i = 145 <;> simp [hi110,hi132,hi144,hi145]

private theorem finish_restore {A : ℕ} (S : Stacks 256 A)
    (next parked saved prior output original originalTail : List (Fin (A+4))) :
    let M : Stacks 256 A := {S with R := (Function.update (Function.update (Function.update S.R
      110 next) 144 parked) 145 saved)}
    let N : Stacks 256 A := {M with R := Function.update M.R 132 prior}
    {N with R := (Function.update (Function.update (Function.update (Function.update N.R
      110 original) 145 (S.R 145)) 146 originalTail) 132 output)} =
      {S with R := (Function.update (Function.update (Function.update (Function.update S.R
        110 original) 144 parked) 146 originalTail) 132 output)} := by
  dsimp only
  refine Stacks.ext rfl rfl rfl ?_
  funext i
  by_cases hi110 : i = 110 <;> by_cases hi132 : i = 132 <;> by_cases hi144 : i = 144 <;>
    by_cases hi145 : i = 145 <;> by_cases hi146 : i = 146 <;> simp [hi110,hi132,hi144,hi145,hi146]

theorem placedCachedBoundaryPair_spec (recovery : Bool) (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
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
    ∀ (F : ZMod s → GaussianInt), (∀ i, ‖value q (F i)‖ ≤ (2 : ℝ)^2) →
    ∀ (v : HS 256 Q A U) (S : Stacks 256 A) (tail coordinateTail pageTail : List (Fin (A+4))) (V : ℕ),
    let σ := boundaryFactorState (embStk sharedPageRecoveryReg (embStk couplingBoundaryReg S))
    LengthKeyReady (2^15*p) (executionStagePrecision p l (initialSchurTarget p u bits 2) 2+1)
      q l s t u band 0 0 (cstream A w (chirpLine s F)++tail)
      (embStk couplingSourceReg S) →
    CouplingPageCacheReady recovery (2^15*p) q w s t u band a b pageTail S →
    (S.R 141).length = a → (S.R 142).length = b →
    (∀ i : Fin 240, (embStk couplingBoundaryReg S).L i = []) → (∀ i : Fin 64, S.R ⟨i.val,by omega⟩ = []) →
    BoundarySolveReady σ q w W B.card →
    σ .bo = cstream A w (Lc.map colC).flatten →
    σ .hf = cstream A w (Uc.map colC).flatten →
    σ .df = cstream A w (rcs.map fun x => (⟨x,0⟩ : GaussianInt)) →
    s ≤ 2^V → (S.R 116).length = B.card → (S.R 115).length = V → (S.R 160).length = w →
    S.R 109 = cstream A V ((bFoldOrder s B).map (fun k : ZMod s => (⟨(k.val : ℤ),0⟩ : GaussianInt)))++coordinateTail →
    (S.R 119).length = q →
    (∀ i ∈ ([127,138,143,106,139,206,223,184,220,221,225,217,201,208,211,215,231,232,233,234,235,236,237,94,131,134,135,136,140,147] : List (Fin 256)), S.R i = []) →
    S.R 116 = List.replicate B.card tick → (S.R 192).length = B.card → (S.R 121).length = s →
    ∀ (borrowed : List (Fin (A+4))),
    S.R 239 = gatherControls A (originAdvances w 0 (boundaryScatterOrigins s B)++[0])++borrowed →
    ∀ x : ZMod s → ℝ, Solves (realMatrix s t p u) (haloVertices s a b) x (fun i => (value q (F i)).re) →
    ∀ (H : ZMod s → GaussianInt), (∀ i, ‖value q (H i)‖ ≤ (2 : ℝ)^2) →
    ∀ y : ZMod s → ℝ, Solves (realMatrix s t p u) (haloVertices s a b) y (fun i => (value q (H i)).re) →
    ∀ (parkedTail original originalTail : List (Fin (A+4))),
    S.R 144 = cstream A w (chirpLine s H)++parkedTail →
    original.length = s*w → S.R 146 = original++originalTail →
    ∃ v' n, ∃ X Y : ZMod s → GaussianInt,
      let S' : Stacks 256 A := {S with R := (Function.update (Function.update (Function.update (Function.update S.R
        110 (original++tail)) 144 parkedTail) 146 originalTail) 132
        (cstream A w (chirpLine s (fun i => pairComponentWord (X i) (Y i)))++S.R 132))}
      v'.user = v.user ∧ n ≤ placedCachedBoundaryPairCost p u l s t a b target V ∧
      Exec body (placedCachedBoundaryPair recovery hR hQ) (mk v S) n (mk v' S') ∧
      PhaseCellInterface.ErrorOn (haloVertices s a b) (pairedCellRead q w (S'.R 132))
        (fun i => (⟨x i,y i⟩ : ℂ)) (1/(2 : ℝ)^target) := by
  dsimp only
  let B := haloBoundary s t (PhaseCellBand.width p u) a b
  let band := PhaseCellBand.width p u
  let solveTarget := boundaryRecoveryTarget p (target+1)
  let bits := boundaryTableBits p solveTarget 2 B.card
  let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
  let w := executionWidth p l (initialSchurTarget p u bits 2) 2
  have hwq : w = 2*q+8 := by dsimp [w,q,executionWidth,executionPrecision]; omega
  intro columns hlen hformat hstage htable F hF v S tail coordinateTail pageTail V hready hcache ha hb hleft hmul
    hsolve hbo hhf hdf hsV hN hV hw hcoordinates hmaster hclean hc hrows hs borrowed hadv x hx
    H hH y hy parkedTail original originalTail h144 horiginal h146
  have hz : ∀ i ∈ ([127,138,143,106,139,206,223,184,220,221,225,217,201,208,211,215,231,232,233,234,235,236,237] : List (Fin 256)), S.R i = [] := by
    intro i hi
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact hclean _ (by simp)
  obtain ⟨v₁,n₁,X,hu₁,hn₁,he₁,hX⟩ := placedCachedRealComponent_spec (body := body) (target := target+1)
    recovery hR hQ hA hp hwidth hα hst hu hαu hθ hgap hbudget hband has hbs hpad columns hlen hformat hstage htable
    F hF v S tail coordinateTail pageTail V hready hcache ha hb hleft hmul hsolve hbo hhf hdf hsV hN hV hw hcoordinates hmaster
    hz hc hrows hs borrowed hadv x hx
  let rawX := cstream A w (chirpLine s X)
  let rawH := cstream A w (chirpLine s H)
  let S₁ : Stacks 256 A := {S with R := Function.update S.R 132 (rawX++S.R 132)}
  have hsource : S.R 110 = cstream A w (chirpLine s F)++tail := hready.source
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := placedComponentTransition_exec (body := body) q s
    (cstream A w (chirpLine s F)) rawX rawH tail (S.R 132) parkedTail
    (by simp [hwq,chirpLine]) (by simp [rawX,hwq,chirpLine]) (by simp [rawH,hwq,chirpLine])
    v₁ S₁ (by simpa [S₁] using hmaster) (by simpa [S₁] using hs)
    (by simpa [S₁] using hsource) (by rfl) (by simpa [S₁] using h144)
    (by simpa [S₁] using hclean 94 (by simp)) (by simpa [S₁] using hclean 131 (by simp))
    (by simpa [S₁] using hclean 134 (by simp)) (by simpa [S₁] using hclean 135 (by simp))
    (by simpa [S₁] using hclean 136 (by simp)) (by simpa [S₁] using hclean 147 (by simp))
  let M : Stacks 256 A := {S with R := (Function.update (Function.update (Function.update S.R
    110 (rawH++tail)) 144 parkedTail) 145 (rawX++S.R 145))}
  have he₁₂ : Exec body (.seq (placedCachedRealComponent recovery hR hQ) placedComponentTransition)
      (mk v S) (n₁+n₂) (mk v₂ M) := by
    exact (Exec.seq he₁ he₂).cast rfl (congrArg (mk v₂) (transition_restore S rawX (rawH++tail) parkedTail))
  have hreadyM : LengthKeyReady (2^15*p) (executionStagePrecision p l (initialSchurTarget p u bits 2) 2+1)
      q l s t u band 0 0 (rawH++tail)
      (embStk couplingSourceReg M) := by
    rw [placedArithmetic_transition]
    exact hready.update_source _
  have hfM : boundaryFactorState (embStk sharedPageRecoveryReg (embStk couplingBoundaryReg M)) =
      boundaryFactorState (embStk sharedPageRecoveryReg (embStk couplingBoundaryReg S)) := by
    funext r
    cases r <;> first | rfl | (rename_i c; cases c <;> rfl)
  have hmM : ∀ i : Fin 64, M.R ⟨i.val,by omega⟩ = [] := by
    intro i
    have hn (k : Fin 256) (hk : 64 ≤ k.val) : (⟨i.val,by omega⟩ : Fin 256) ≠ k := by
      intro he
      have hh := congrArg (fun j : Fin 256 => j.val) he
      have hi := i.isLt
      change i.val = k.val at hh
      omega
    simpa only [M,Function.update_of_ne (hn 145 (by decide)),Function.update_of_ne (hn 144 (by decide)),
      Function.update_of_ne (hn 110 (by decide))] using hmul i
  have hzM : ∀ i ∈ ([127,138,143,106,139,206,223,184,220,221,225,217,201,208,211,215,231,232,233,234,235,236,237] : List (Fin 256)), M.R i = [] := by
    intro i hi
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simpa [M] using hclean _ (by simp)
  have hcacheM : CouplingPageCacheReady recovery (2^15*p) q w s t u band a b pageTail M := by
    apply hcache.of_frame
    intro i
    have hi := couplingCachePort_ge recovery i
    have hne (k : Fin 256) (hk : k.val < 248) : couplingCachePort recovery i ≠ k := by
      intro h; have := congrArg Fin.val h; omega
    simp [M,hne 110 (by decide),hne 144 (by decide),hne 145 (by decide)]
  obtain ⟨v₃,n₃,Y,hu₃,hn₃,he₃,hY⟩ := placedCachedRealComponent_spec (body := body) (target := target+1)
    recovery hR hQ hA hp hwidth hα hst hu hαu hθ hgap hbudget hband has hbs hpad columns hlen hformat hstage htable
    H hH v₂ M tail coordinateTail pageTail V hreadyM hcacheM (by simpa [M] using ha) (by simpa [M] using hb) hleft hmM
    (by rw [hfM]; exact hsolve) (by rw [hfM]; exact hbo) (by rw [hfM]; exact hhf) (by rw [hfM]; exact hdf)
    hsV (by simpa [M] using hN) (by simpa [M] using hV) (by simpa [M] using hw)
    (by simpa [M] using hcoordinates) (by simpa [M] using hmaster) hzM
    (by simpa [M] using hc) (by simpa [M] using hrows) (by simpa [M] using hs) borrowed
    (by simpa [M] using hadv) y hy
  let rawY := cstream A w (chirpLine s Y)
  let N : Stacks 256 A := {M with R := Function.update M.R 132 (rawY++M.R 132)}
  obtain ⟨v₄,n₄,hu₄,hn₄,he₄⟩ := placedFinishComponents_exec (body := body)
    (Nat.le_trans (by decide : 4 ≤ 96) hA) q s (chirpLine s X) (chirpLine s Y)
    (by simp [chirpLine]) (by simp [chirpLine]) rawH tail (S.R 145) (S.R 132) original originalTail
    (by simp [rawH,hwq,chirpLine]) (by simpa only [← hwq] using horiginal)
    v₃ N (by simpa [N,M] using hmaster) (by simpa [N,M] using hs)
    (by simp [N,M]) (by simp [N,M,rawX,hwq]) (by simp [N,M,rawY,hwq]) (by simpa [N,M] using h146)
    (by simpa [N,M] using hclean 94 (by simp)) (by simpa [N,M] using hclean 131 (by simp))
    (by simpa [N,M] using hclean 134 (by simp)) (by simpa [N,M] using hclean 135 (by simp))
    (by simpa [N,M] using hclean 136 (by simp)) (by simpa [N,M] using hclean 140 (by simp))
    (by simpa [N,M] using hclean 147 (by simp))
  simp only [← hwq,pairComponentWords_chirpLine] at he₄
  refine ⟨v₄,(n₁+n₂)+(n₃+n₄),X,Y,hu₄.trans (hu₃.trans (hu₂.trans hu₁)),?_,
    (Exec.seq he₁₂ (Exec.seq he₃ he₄)).cast rfl ?_,?_⟩
  · have h₁ : n₁ ≤ placedCachedRealComponentCost p u l s t a b (target+1) V := hn₁
    have h₂ : n₂ ≤ cleanComponentTransitionCost q s := hn₂
    have h₃ : n₃ ≤ placedCachedRealComponentCost p u l s t a b (target+1) V := hn₃
    have h₄ : n₄ ≤ cleanFinishComponentsCost q s := hn₄
    change (n₁+n₂)+(n₃+n₄) ≤ placedCachedBoundaryPairCost p u l s t a b target V
    dsimp only [placedCachedBoundaryPairCost]
    change (n₁+n₂)+(n₃+n₄) ≤ 2*placedCachedRealComponentCost p u l s t a b (target+1) V+
      cleanComponentTransitionCost q s+cleanFinishComponentsCost q s
    omega
  · apply congrArg (mk v₄)
    exact finish_restore S (rawH++tail) parkedTail (rawX++S.R 145) (rawY++S.R 132)
      (cstream A w (chirpLine s (fun i => pairComponentWord (X i) (Y i)))++S.R 132)
      (original++tail) originalTail
  · have hX' : PhaseCellInterface.ErrorOn (haloVertices s a b)
        (fun i => publishedCellRead q w (0 : ZMod s) (rawX++S.R 132) i) x (1/(2 : ℝ)^(target+1)) := hX
    have hY' : PhaseCellInterface.ErrorOn (haloVertices s a b)
        (fun i => publishedCellRead q w (0 : ZMod s) (rawY++S.R 132) i) y (1/(2 : ℝ)^(target+1)) := hY
    have hh := pairedComponents_physical_accuracy (q := q) (w := w) (Nat.le_trans (by decide : 4 ≤ 96) hA) X Y
      (haloVertices s a b) (fun i => (⟨x i,y i⟩ : ℂ))
      (1/(2 : ℝ)^(target+1)) (1/(2 : ℝ)^(target+1)) (S.R 132) (S.R 132) (S.R 132) hX' hY'
    rw [component_error_budget] at hh
    exact hh

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
