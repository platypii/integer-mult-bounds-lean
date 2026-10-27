module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedCachedBoundaryPair
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedOriginalInputs

/-! Execute a complex input through both real solves on one retained factor page, restoring every borrowed tape. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.BandFactor
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.SchurDominance
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 256 Q A U}

noncomputable def placedCachedComplexComponent (recovery : Bool) (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P 256 Q A U :=
  .seq placedOriginalComponentInputs (placedCachedBoundaryPair recovery hR hQ)

private theorem original_restore {A : ℕ} (S : Stacks 256 A)
    (real imag original tail output : List (Fin (A+4))) (hsource : S.R 110 = original++tail) :
    let M : Stacks 256 A := {S with R := (Function.update (Function.update (Function.update S.R
      146 (original++S.R 146)) 110 real) 144 imag)}
    {M with R := (Function.update (Function.update (Function.update (Function.update M.R
      110 (original++tail)) 144 (S.R 144)) 146 (S.R 146)) 132 (output++M.R 132))} =
      {S with R := Function.update S.R 132 (output++S.R 132)} := by
  dsimp only
  refine Stacks.ext rfl rfl rfl ?_
  funext i
  by_cases hi110 : i = 110 <;> by_cases hi132 : i = 132 <;>
    by_cases hi144 : i = 144 <;> by_cases hi146 : i = 146 <;> simp [hi110,hi132,hi144,hi146,hsource]

theorem placedCachedComplexComponent_spec (recovery : Bool) (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
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
    ∀ (x y : ZMod s → ℝ),
    Solves (realMatrix s t p u) (haloVertices s a b) x (fun i => (value q (F i)).re) →
    Solves (realMatrix s t p u) (haloVertices s a b) y (fun i => (value q (F i)).im) →
    ∃ v' n, ∃ Z : ZMod s → GaussianInt,
      let S' : Stacks 256 A := {S with R := Function.update S.R 132 (cstream A w (chirpLine s Z)++S.R 132)}
      v'.user = v.user ∧ n ≤ originalComponentInputsCost q s+placedCachedBoundaryPairCost p u l s t a b target V ∧
      Exec body (placedCachedComplexComponent recovery hR hQ) (mk v S) n (mk v' S') ∧
      PhaseCellInterface.ErrorOn (haloVertices s a b) (pairedCellRead q w (S'.R 132))
        (fun i => (⟨x i,y i⟩ : ℂ)) (1/(2 : ℝ)^target) := by
  dsimp only
  let B := haloBoundary s t (PhaseCellBand.width p u) a b
  let band := PhaseCellBand.width p u
  let bits := boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2 B.card
  let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
  let w := executionWidth p l (initialSchurTarget p u bits 2) 2
  have hwq : w = 2*q+8 := by dsimp [w,q,executionWidth,executionPrecision]; omega
  intro columns hlen hformat hstage htable F hF v S tail coordinateTail pageTail V hready hcache ha hb hleft hmul
    hsolve hbo hhf hdf hsV hN hV hw hcoordinates hmaster hclean hc hrows hs borrowed hadv x y hx hy
  let FRe := fun i => realPartWord (F i)
  let FIm := fun i => imagPartWord (F i)
  have hreadyInput : LengthKeyReady (2^15*p) (executionStagePrecision p l (initialSchurTarget p u bits 2) 2+1) q l s t u band 0 0
      (cstream A (2*q+8) (chirpLine s F)++tail)
      (embStk couplingSourceReg S) := by
    have hh : LengthKeyReady (2^15*p) (executionStagePrecision p l (initialSchurTarget p u bits 2) 2+1)
        q l s t u band 0 0 (cstream A w (chirpLine s F)++tail)
        (embStk couplingSourceReg S) := hready
    simpa only [hwq] using hh
  obtain ⟨v₀,n₀,hu₀,hn₀,he₀,hready₀⟩ := placedOriginalComponentInputs_exec (body := body)
    (Nat.le_trans (by decide : 4 ≤ 96) hA) F tail v S hreadyInput (hclean 147 (by simp))
  simp only [← hwq] at he₀ hready₀
  let original := cstream A w (chirpLine s F)
  let M : Stacks 256 A := {S with R := (Function.update (Function.update (Function.update S.R
    146 (original++S.R 146)) 110 (cstream A w (chirpLine s FRe)++tail))
    144 (cstream A w (chirpLine s FIm)++S.R 144))}
  have hRe : ∀ i, ‖value q (FRe i)‖ ≤ (2 : ℝ)^2 := fun i => (componentWords_norm_le q (F i)).1.trans (hF i)
  have hIm : ∀ i, ‖value q (FIm i)‖ ≤ (2 : ℝ)^2 := fun i => (componentWords_norm_le q (F i)).2.trans (hF i)
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
    simpa only [M,Function.update_of_ne (hn 144 (by decide)),Function.update_of_ne (hn 110 (by decide)),
      Function.update_of_ne (hn 146 (by decide))] using hmul i
  have hzM : ∀ i ∈ ([127,138,143,106,139,206,223,184,220,221,225,217,201,208,211,215,231,232,233,234,235,236,237,94,131,134,135,136,140,147] : List (Fin 256)), M.R i = [] := by
    intro i hi
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simpa [M] using hclean _ (by simp)
  have hcacheM : CouplingPageCacheReady recovery (2^15*p) q w s t u band a b pageTail M := by
    apply hcache.of_frame
    intro i
    have hi := couplingCachePort_ge recovery i
    have hne (k : Fin 256) (hk : k.val < 248) : couplingCachePort recovery i ≠ k := by
      intro h; have := congrArg Fin.val h; omega
    simp [M,hne 110 (by decide),hne 144 (by decide),hne 146 (by decide)]
  obtain ⟨v₁,n₁,X,Y,hu₁,hn₁,he₁,herror⟩ := placedCachedBoundaryPair_spec (body := body)
    recovery hR hQ hA hp hwidth hα hst hu hαu hθ hgap hbudget hband has hbs hpad columns hlen hformat hstage htable
    FRe hRe v₀ M tail coordinateTail pageTail V hready₀ hcacheM (by simpa [M] using ha) (by simpa [M] using hb) hleft hmM
    (by rw [hfM]; exact hsolve) (by rw [hfM]; exact hbo) (by rw [hfM]; exact hhf) (by rw [hfM]; exact hdf)
    hsV (by simpa [M] using hN) (by simpa [M] using hV) (by simpa [M] using hw)
    (by simpa [M] using hcoordinates) (by simpa [M] using hmaster) hzM
    (by simpa [M] using hc) (by simpa [M] using hrows) (by simpa [M] using hs) borrowed (by simpa [M] using hadv)
    x (by simpa only [FRe,value_realPartWord_re] using hx) FIm hIm y
    (by simpa only [FIm,value_imagPartWord_re] using hy) (S.R 144) original (S.R 146)
    (by rfl) (by change original.length = s*w; simp [original,chirpLine]) (by rfl)
  let Z := fun i => pairComponentWord (X i) (Y i)
  refine ⟨v₁,n₀+n₁,Z,hu₁.trans hu₀,Nat.add_le_add hn₀ hn₁,(Exec.seq he₀ he₁).cast rfl ?_,herror⟩
  apply congrArg (mk v₁)
  have hsource : S.R 110 = original++tail := hready.source
  exact original_restore S (cstream A w (chirpLine s FRe)++tail)
    (cstream A w (chirpLine s FIm)++S.R 144) original tail (cstream A w (chirpLine s Z)) hsource

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
