module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedHaloInputRun
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedHaloPublication

/-! Execute the original local setup, solve, disposal and owned-core publication.
The shared input record replaces a repeated list of physical preconditions. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry ScalarPlacement

variable {Q A : ℕ} {P U : Type}
  {body : P → Pr P 242 Q A U} {body' : P → Pr P 248 Q A U} {body'' : P → Pr P 256 Q A U}

theorem packedHaloCoreUsing_spec (freshGeometry : Bool) (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    (hbody : ∀ f, body' f = embProg packedBoundaryRecoveryBase id (body f))
    (hbody' : ∀ f, body'' f = embProg packedHaloPublicationReg id (body' f))
    {p l s t u target rhsExp a b V : ℕ} [NeZero s] {α d : ℝ}
    (C : ZMod s → GaussianInt) (tail E outputTail : List (Fin (A+4))) (S : Stacks 242 A)
    (hinput : PackedHaloInput (freshGeometry := freshGeometry) (p := p) (l := l) (t := t) (u := u) (target := target)
      (rhsExp := rhsExp) (a := a) (b := b) (V := V) α d C tail E outputTail S)
    (width k radius : ℕ) (ha : a = coreStart width k-radius)
    (hb : b = coreStart width k+coreLength s width k+radius)
    (hleft : radius ≤ coreStart width k)
    (v : HS 256 Q A U) (M : Stacks 256 A)
    (hview : embStk packedHaloPublicationReg M = extendStacks (by decide) S)
    (hoffset : (M.R 249).length = radius) (hrows : (M.R 250).length = coreLength s width k)
    (hfresh : ∀ i ∈ ([251,252,253,254] : List (Fin 256)), M.R i = [])
    (x : ZMod s → ℝ)
    (hx : let B := haloBoundary s t (PhaseCellBand.width p u) a b
      let j := boundaryHaloTarget p u (boundaryRecoveryTarget p target) rhsExp B.card
      SchurDominance.Solves (realMatrix s t p u) (haloVertices s a b) x
        (fun i => (value (executionPrecision p l j rhsExp) (C i)).re)) :
    let B := haloBoundary s t (PhaseCellBand.width p u) a b
    let bits := boundaryTableBits p (boundaryRecoveryTarget p target) rhsExp B.card
    let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
    let w := executionWidth p l (initialSchurTarget p u bits 2) 2
    ∃ v' F n, ∃ D : ZMod s → GaussianInt,
      v'.user = v.user ∧
      n ≤ packedHaloSolveUsingCost freshGeometry p u l target rhsExp s t a b V+
        preparedPackedSliceCost radius (coreLength s width k) w ∧
      Exec body'' (packedHaloPublicationUsing freshGeometry hR hQ) (IntegerMultBounds.MathlibTM2.Host.mk v M) n (IntegerMultBounds.MathlibTM2.Host.mk v' F) ∧
      F.inp = S.inp ∧ F.out = S.out ∧
      F.R 248 = cstream A w (ownedCoreWords width k D)++M.R 248 ∧
      (F.R 130).length = w ∧
      (∀ i ∈ ([104,105,109] : List (Fin 256)), F.R i = []) ∧
      F.R 132 = cstream A w (packedInterval a (b-a) D)++outputTail ∧
      (∃ residual : List (Fin (A+4)), residual.length = (b-a)*w ∧
        F.R 110 = residual++(cstream A w (packedInterval a (b-a) C)++tail)) ∧
      (∀ i, Fits w (D i)) ∧
      PhaseCellInterface.ErrorOn (ownedCore s width k)
        (fun i => (packedIntervalRead q w (coreStart width k) (F.R 248) i).re) x (1/(2 : ℝ)^target) ∧
      PackedHaloNativeClean (embStk (Fin.castLE (by decide : 168 ≤ 256)) F) ∧
      PackedHaloRetainedHeaders (2^15*p)
        (executionStagePrecision p l (initialSchurTarget p u bits 2) 2+1)
        q l s t u (PhaseCellBand.width p u) a b V w
        (embStk (Fin.castLE (by decide : 168 ≤ 256)) F) ∧
      ∀ i : Fin 256, 248 ≤ i.val → i ≠ 248 → F.R i = M.R i := by
  dsimp only
  let B := haloBoundary s t (PhaseCellBand.width p u) a b
  let bits := boundaryTableBits p (boundaryRecoveryTarget p target) rhsExp B.card
  let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
  let w := executionWidth p l (initialSchurTarget p u bits 2) 2
  obtain ⟨v₁,F₁,m,D,hu₁,hm,he,hin,hout,hwidth,h104,h105,h109,hsource,hfits,herror,hnativeClean,hretainedHeaders,hbuffers⟩ :=
    hinput.runUsing (body := body) (body' := body') freshGeometry hR hQ hA hbody
      (embDn packedHaloPublicationReg v) x hx
  have he' : Exec body' (packedHaloSolveUsing freshGeometry hR hQ)
      (IntegerMultBounds.MathlibTM2.Host.mk (embDn packedHaloPublicationReg v) (embStk packedHaloPublicationReg M)) m (IntegerMultBounds.MathlibTM2.Host.mk v₁ F₁) := by
    simpa only [hview] using he
  have hlength : b-a = coreLength s width k+2*radius := by omega
  have hsource' : F₁.R 132 = cstream A w (packedInterval a (b-a) D)++outputTail := hsource
  have herror' : PhaseCellInterface.ErrorOn (haloVertices s a b)
      (fun i => (packedIntervalRead q w a (F₁.R 132) i).re) x (1/(2 : ℝ)^target) := herror
  obtain ⟨v₂,F,n,hu₂,hn,he₂,hpublished,hfinal,haccuracy,hframe⟩ :=
    packedHaloPublicationUsing_exec (body := body') (body' := body'') freshGeometry hR hQ hbody' q w width k radius D x _
      hleft (by rw [← hb]; exact hinput.hbs) outputTail v M v₁ F₁ m hu₁ he' hwidth h104 h105
      (by rw [hlength] at hsource'; simpa only [ha] using hsource')
      (by simpa only [ha,hb] using herror') hoffset hrows hfresh
  have hread (i : Fin 248) : F.R (packedHaloPublicationReg i) = F₁.R i :=
    congrArg (fun G : Stacks 248 A => G.R i) hfinal
  have hread132 : F.R 132 = F₁.R 132 := by
    simpa only [show packedHaloPublicationReg 132 = 132 by decide] using hread 132
  have hread110 : F.R 110 = F₁.R 110 := by
    simpa only [show packedHaloPublicationReg 110 = 110 by decide] using hread 110
  refine ⟨v₂,F,n,D,hu₂,hn.trans (Nat.add_le_add_right hm _),he₂,?_,?_,hpublished,?_,?_,
    hread132.trans hsource,?_,hfits,haccuracy,?_,?_,hframe⟩
  · have hh := congrArg (fun G : Stacks 248 A => G.inp) hfinal
    exact hh.trans hin
  · have hh := congrArg (fun G : Stacks 248 A => G.out) hfinal
    exact hh.trans hout

  · have hh := congrArg List.length (hread 130)
    simpa only [show packedHaloPublicationReg 130 = 130 by decide] using hh.trans hwidth
  · intro i hi
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl | rfl
    · simpa only [show packedHaloPublicationReg 104 = 104 by decide] using (hread 104).trans h104
    · simpa only [show packedHaloPublicationReg 105 = 105 by decide] using (hread 105).trans h105
    · simpa only [show packedHaloPublicationReg 109 = 109 by decide] using (hread 109).trans h109
  · obtain ⟨residual,hlen,hs⟩ := hbuffers
    exact ⟨residual,hlen,hread110.trans hs⟩
  · have hv : embStk (Fin.castLE (by decide : 168 ≤ 256)) F =
        embStk packedRecoveryRuntimeReg F₁ :=
      congrArg (embStk packedRecoveryRuntimeReg) hfinal
    rw [hv]
    exact hnativeClean
  · have hv : embStk (Fin.castLE (by decide : 168 ≤ 256)) F =
        embStk packedRecoveryRuntimeReg F₁ :=
      congrArg (embStk packedRecoveryRuntimeReg) hfinal
    rw [hv]
    exact hretainedHeaders

theorem packedHaloCore_spec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    (hbody : ∀ f, body' f = embProg packedBoundaryRecoveryBase id (body f))
    (hbody' : ∀ f, body'' f = embProg packedHaloPublicationReg id (body' f))
    {p l s t u target rhsExp a b V : ℕ} [NeZero s] {α d : ℝ}
    (C : ZMod s → GaussianInt) (tail E outputTail : List (Fin (A+4))) (S : Stacks 242 A)
    (hinput : PackedHaloInput (p := p) (l := l) (t := t) (u := u) (target := target)
      (rhsExp := rhsExp) (a := a) (b := b) (V := V) α d C tail E outputTail S)
    (width k radius : ℕ) (ha : a = coreStart width k-radius)
    (hb : b = coreStart width k+coreLength s width k+radius)
    (hleft : radius ≤ coreStart width k)
    (v : HS 256 Q A U) (M : Stacks 256 A)
    (hview : embStk packedHaloPublicationReg M = extendStacks (by decide) S)
    (hoffset : (M.R 249).length = radius) (hrows : (M.R 250).length = coreLength s width k)
    (hfresh : ∀ i ∈ ([251,252,253,254] : List (Fin 256)), M.R i = [])
    (x : ZMod s → ℝ)
    (hx : let B := haloBoundary s t (PhaseCellBand.width p u) a b
      let j := boundaryHaloTarget p u (boundaryRecoveryTarget p target) rhsExp B.card
      SchurDominance.Solves (realMatrix s t p u) (haloVertices s a b) x
        (fun i => (value (executionPrecision p l j rhsExp) (C i)).re)) :
    let B := haloBoundary s t (PhaseCellBand.width p u) a b
    let bits := boundaryTableBits p (boundaryRecoveryTarget p target) rhsExp B.card
    let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
    let w := executionWidth p l (initialSchurTarget p u bits 2) 2
    ∃ v' F n, ∃ D : ZMod s → GaussianInt,
      v'.user = v.user ∧
      n ≤ packedHaloSolveCost p u l target rhsExp s t a b V+
        preparedPackedSliceCost radius (coreLength s width k) w ∧
      Exec body'' (packedHaloPublication hR hQ) (IntegerMultBounds.MathlibTM2.Host.mk v M) n (IntegerMultBounds.MathlibTM2.Host.mk v' F) ∧
      F.inp = S.inp ∧ F.out = S.out ∧
      F.R 248 = cstream A w (ownedCoreWords width k D)++M.R 248 ∧
      (F.R 130).length = w ∧
      (∀ i ∈ ([104,105,109] : List (Fin 256)), F.R i = []) ∧
      F.R 132 = cstream A w (packedInterval a (b-a) D)++outputTail ∧
      (∃ residual : List (Fin (A+4)), residual.length = (b-a)*w ∧
        F.R 110 = residual++(cstream A w (packedInterval a (b-a) C)++tail)) ∧
      (∀ i, Fits w (D i)) ∧
      PhaseCellInterface.ErrorOn (ownedCore s width k)
        (fun i => (packedIntervalRead q w (coreStart width k) (F.R 248) i).re) x (1/(2 : ℝ)^target) ∧
      PackedHaloNativeClean (embStk (Fin.castLE (by decide : 168 ≤ 256)) F) ∧
      PackedHaloRetainedHeaders (2^15*p)
        (executionStagePrecision p l (initialSchurTarget p u bits 2) 2+1)
        q l s t u (PhaseCellBand.width p u) a b V w
        (embStk (Fin.castLE (by decide : 168 ≤ 256)) F) ∧
      ∀ i : Fin 256, 248 ≤ i.val → i ≠ 248 → F.R i = M.R i := by
  exact packedHaloCoreUsing_spec (body := body) (body' := body') (body'' := body'') true
    hR hQ hA hbody hbody' C tail E outputTail S hinput width k radius ha hb hleft
    v M hview hoffset hrows hfresh x hx

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
