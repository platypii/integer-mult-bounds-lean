module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedHaloCore
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHaloBufferRelease

/-! Publish a concrete local core, then retire all three owned local word buffers. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry ScalarPlacement

variable {Q A : ℕ} {P U : Type}
  {body : P → Pr P 242 Q A U} {body' : P → Pr P 248 Q A U} {body'' : P → Pr P 256 Q A U}

noncomputable def packedHaloCoreReleaseUsing (freshGeometry : Bool) (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P 256 Q A U :=
  .seq (packedHaloPublicationUsing freshGeometry hR hQ) haloBufferRelease

noncomputable def packedHaloCoreRelease (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P 256 Q A U :=
  packedHaloCoreReleaseUsing true hR hQ

theorem packedHaloCoreReleaseUsing_spec (freshGeometry : Bool) (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
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
    (h255 : M.R 255 = [])
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
        preparedPackedSliceCost radius (coreLength s width k) w+
        haloBufferReleaseCost (coreLength s width k) radius w ∧
      Exec body'' (packedHaloCoreReleaseUsing freshGeometry hR hQ) (mk v M) n (mk v' F) ∧
      F.inp = S.inp ∧ F.out = S.out ∧
      F.R 248 = cstream A w (ownedCoreWords width k D)++M.R 248 ∧
      F.R 132 = outputTail ∧ F.R 110 = tail ∧ F.R 255 = [] ∧
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
  let w := executionWidth p l (initialSchurTarget p u bits 2) 2
  obtain ⟨v₁,G,m,D,hu₁,hm,he₁,hin,hout,hpublished,hwidth,hclean,hsource,hbuffers,hfits,herror,hnativeClean,hretainedHeaders,hframe⟩ :=
    packedHaloCoreUsing_spec (body := body) (body' := body') (body'' := body'')
      (p := p) (l := l) (s := s) (t := t) (u := u) (target := target) (rhsExp := rhsExp)
      (a := a) (b := b) (V := V) freshGeometry hR hQ hA hbody hbody' C tail E outputTail S hinput
      width k radius ha hb hleft v M hview hoffset hrows hfresh x hx
  have hlength : b-a = coreLength s width k+2*radius := by omega
  have hfit : a+(b-a) ≤ s := by have hh := hinput.hbs; have ha' := hinput.hab; omega
  obtain ⟨residual,hlen,hrhs⟩ := hbuffers
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := haloBufferRelease_exec (body := body'')
    (coreLength s width k) radius w (cstream A w (packedInterval a (b-a) D)) residual
    (cstream A w (packedInterval a (b-a) C)) outputTail tail
    (by rw [length_cstream,packedInterval_length D hfit,hlength])
    (by simpa only [hlength] using hlen)
    (by rw [length_cstream,packedInterval_length C hfit,hlength]) v₁ G
    (by rw [hframe 250 (by decide) (by decide)]; exact hrows)
    (by rw [hframe 249 (by decide) (by decide)]; exact hoffset) hwidth hsource hrhs (by
      intro i hi
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl
      · exact hclean 104 (by decide)
      · exact hclean 105 (by decide)
      · exact hclean 109 (by decide)
      · exact (hframe 255 (by decide) (by decide)).trans h255)
  let F : Stacks 256 A := {G with R := (Function.update (Function.update G.R 132 outputTail) 110 tail)}
  refine ⟨v₂,F,m+n₂,D,hu₂.trans hu₁,Nat.add_le_add hm hn₂,Exec.seq he₁ he₂,hin,hout,?_,?_,?_,?_,hfits,?_,?_,?_,?_⟩
  · simpa [F] using hpublished
  · simp [F]
  · simp [F]
  · simpa [F] using (hframe 255 (by decide) (by decide)).trans h255
  · simpa only [show F.R 248 = G.R 248 by simp [F]] using herror
  · intro i hi93 hi110
    have h110 : Fin.castLE (by decide : 117 ≤ 256) i ≠ 110 := by
      intro he; apply hi110; apply Fin.ext; exact congrArg (fun k : Fin 256 => k.val) he
    have h132 : Fin.castLE (by decide : 117 ≤ 256) i ≠ 132 := by
      intro he
      have hv := congrArg (fun k : Fin 256 => k.val) he
      change i.val = 132 at hv
      have hi := i.isLt
      omega
    change Function.update (Function.update G.R 132 outputTail) 110 tail
      (Fin.castLE (by decide : 117 ≤ 256) i) = []
    rw [Function.update_of_ne h110,Function.update_of_ne h132]
    exact hnativeClean i hi93 hi110
  · apply hretainedHeaders.of_frame
    intro i hi
    have hs := haloRetainedHeaderPorts_safe i hi
    have hn132 : Fin.castLE (by decide : 168 ≤ 256) i ≠ 132 := by
      intro he; apply hs.2.1; apply Fin.ext; exact congrArg (fun k : Fin 256 => k.val) he
    have hn110 : Fin.castLE (by decide : 168 ≤ 256) i ≠ 110 := by
      intro he
      have hv := congrArg (fun k : Fin 256 => k.val) he
      change i.val = 110 at hv
      have hh := hs.1
      omega
    simp only [embStk,Function.comp_apply,F,Function.update_of_ne hn110,Function.update_of_ne hn132]
  · intro i hi hn
    have hn132 : i ≠ 132 := by intro he; subst i; omega
    have hn110 : i ≠ 110 := by intro he; subst i; omega
    simpa only [F,Function.update_of_ne hn110,Function.update_of_ne hn132] using hframe i hi hn

theorem packedHaloCoreRelease_spec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
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
    (h255 : M.R 255 = [])
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
        preparedPackedSliceCost radius (coreLength s width k) w+
        haloBufferReleaseCost (coreLength s width k) radius w ∧
      Exec body'' (packedHaloCoreRelease hR hQ) (mk v M) n (mk v' F) ∧
      F.inp = S.inp ∧ F.out = S.out ∧
      F.R 248 = cstream A w (ownedCoreWords width k D)++M.R 248 ∧
      F.R 132 = outputTail ∧ F.R 110 = tail ∧ F.R 255 = [] ∧
      (∀ i, Fits w (D i)) ∧
      PhaseCellInterface.ErrorOn (ownedCore s width k)
        (fun i => (packedIntervalRead q w (coreStart width k) (F.R 248) i).re) x (1/(2 : ℝ)^target) ∧
      PackedHaloNativeClean (embStk (Fin.castLE (by decide : 168 ≤ 256)) F) ∧
      PackedHaloRetainedHeaders (2^15*p)
        (executionStagePrecision p l (initialSchurTarget p u bits 2) 2+1)
        q l s t u (PhaseCellBand.width p u) a b V w
        (embStk (Fin.castLE (by decide : 168 ≤ 256)) F) ∧
      ∀ i : Fin 256, 248 ≤ i.val → i ≠ 248 → F.R i = M.R i := by
  exact packedHaloCoreReleaseUsing_spec (body := body) (body' := body') (body'' := body'') true
    hR hQ hA hbody hbody' C tail E outputTail S hinput width k radius ha hb hleft
    v M hview hoffset hrows hfresh h255 x hx

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
