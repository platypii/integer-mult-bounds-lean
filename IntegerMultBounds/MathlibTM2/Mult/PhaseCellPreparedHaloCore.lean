module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedHaloInput
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedHaloCoreRelease

/-! Initialize the local output, execute the concrete core solver/publication,
and restore its owned output/RHS buffers, with all preparation paid. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry ScalarPlacement

variable {Q A : ℕ} {P U : Type}
  {body : P → Pr P 242 Q A U} {body' : P → Pr P 248 Q A U} {body'' : P → Pr P 256 Q A U}

noncomputable def preparedHaloCore (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P 256 Q A U :=
  .seq prepareHaloBuffer (packedHaloCoreRelease hR hQ)

theorem preparedHaloCore_spec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    (hbody : ∀ f, body' f = embProg packedBoundaryRecoveryBase id (body f))
    (hbody' : ∀ f, body'' f = embProg packedHaloPublicationReg id (body' f))
    {p l s t u target rhsExp a b V : ℕ} [NeZero s] {α d : ℝ}
    (C : ZMod s → GaussianInt) (tail : List (Fin (A+4))) (S : Stacks 242 A)
    (hframe : PackedHaloFrame (p := p) (l := l) (t := t) (u := u) (target := target)
      (rhsExp := rhsExp) (a := a) (b := b) (V := V) α d C tail S)
    (width k radius : ℕ) (ha : a = coreStart width k-radius)
    (hb : b = coreStart width k+coreLength s width k+radius)
    (hleft : radius ≤ coreStart width k)
    (v : HS 256 Q A U) (M : Stacks 256 A)
    (hview : embStk packedHaloPublicationReg M = extendStacks (by decide) S)
    (hoffset : (M.R 249).length = radius) (hrows : (M.R 250).length = coreLength s width k)
    (hfresh : ∀ i ∈ ([251,252,253,254,255] : List (Fin 256)), M.R i = [])
    (x : ZMod s → ℝ)
    (hx : let B := haloBoundary s t (PhaseCellBand.width p u) a b
      let j := boundaryHaloTarget p u (boundaryRecoveryTarget p target) rhsExp B.card
      SchurDominance.Solves (realMatrix s t p u) (haloVertices s a b) x
        (fun i => (value (executionPrecision p l j rhsExp) (C i)).re)) :
    let B := haloBoundary s t (PhaseCellBand.width p u) a b
    let bits := boundaryTableBits p (boundaryRecoveryTarget p target) rhsExp B.card
    let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
    let w := 2*q+8
    ∃ v' F n, ∃ D : ZMod s → GaussianInt,
      v'.user = v.user ∧
      n ≤ prepareHaloBufferCost q (coreLength s width k) radius+
        packedHaloSolveCost p u l target rhsExp s t a b V+
        preparedPackedSliceCost radius (coreLength s width k) w+
        haloBufferReleaseCost (coreLength s width k) radius w ∧
      Exec body'' (preparedHaloCore hR hQ) (mk v M) n (mk v' F) ∧
      F.inp = S.inp ∧ F.out = S.out ∧
      F.R 248 = cstream A w (ownedCoreWords width k D)++M.R 248 ∧
      F.R 132 = S.R 132 ∧ F.R 110 = tail ∧ F.R 255 = [] ∧
      (∀ i, Fits w (D i)) ∧
      PhaseCellInterface.ErrorOn (ownedCore s width k)
        (fun i => (packedIntervalRead q w (coreStart width k) (F.R 248) i).re) x (1/(2 : ℝ)^target) ∧
      PackedHaloRetainedHeaders (2^15*p)
        (executionStagePrecision p l (initialSchurTarget p u bits 2) 2+1)
        q l s t u (PhaseCellBand.width p u) a b V w
        (embStk (Fin.castLE (by decide : 168 ≤ 256)) F) ∧
      ∀ i : Fin 256, 248 ≤ i.val → i ≠ 248 → F.R i = M.R i := by
  dsimp only
  let B := haloBoundary s t (PhaseCellBand.width p u) a b
  let bits := boundaryTableBits p (boundaryRecoveryTarget p target) rhsExp B.card
  let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
  let E := cstream A (2*q+8) (List.replicate (coreLength s width k+2*radius) (0 : GaussianInt))
  let S' : Stacks 242 A := {S with R := Function.update S.R 132 (E++S.R 132)}
  obtain ⟨v₀,M₀,n₀,hu₀,hn₀,he₀,hinput,hview₀,hframe₀⟩ := prepareHaloBuffer_input (body := body'')
    C tail S hframe width k radius ha hb hleft v M hview hoffset hrows (by
      intro i hi; exact hfresh i (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢; tauto))
  obtain ⟨v₁,F,n₁,D,hu₁,hn₁,he₁,hin,hout,hpublished,houtput,hsource,h255,hfits,herror,hretainedHeaders,hframe₁⟩ :=
    packedHaloCoreRelease_spec (body := body) (body' := body') (body'' := body'')
      (p := p) (l := l) (s := s) (t := t) (u := u) (target := target) (rhsExp := rhsExp)
      (a := a) (b := b) (V := V) hR hQ hA hbody hbody' C tail E (S.R 132) S' hinput width k radius
      ha hb hleft v₀ M₀ hview₀ (by rw [hframe₀ 249 (by decide)]; exact hoffset)
      (by rw [hframe₀ 250 (by decide)]; exact hrows) (by
        intro i hi
        have hb : 248 ≤ i.val := by
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
          rcases hi with rfl | rfl | rfl | rfl <;> decide
        rw [hframe₀ i hb]
        exact hfresh i (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢; tauto))
      ((hframe₀ 255 (by decide)).trans (hfresh 255 (by decide))) x hx
  have hww : executionWidth p l (initialSchurTarget p u bits 2) 2 = 2*q+8 := by
    dsimp only [q,executionWidth,executionPrecision]; omega
  dsimp only [bits,B] at hww
  simp only [hww] at hn₁ hpublished hfits herror hretainedHeaders
  refine ⟨v₁,F,n₀+n₁,D,hu₁.trans hu₀,?_,Exec.seq he₀ he₁,hin,hout,?_,houtput,hsource,h255,hfits,herror,hretainedHeaders,?_⟩
  · have hh := Nat.add_le_add hn₀ hn₁
    simpa only [Nat.add_assoc] using hh
  · rw [hpublished,hframe₀ 248 (by decide)]
  · intro i hi hn
    exact (hframe₁ i hi hn).trans (hframe₀ i hi)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
