module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellQueuedHaloFrame
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedHaloCore

/-! Consume a queued packed RHS, execute the concrete core solver, and restore
the borrowed ambient source while preserving the rest of the queue. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry ScalarPlacement

variable {Q A : ℕ} {P U : Type}
  {body : P → Pr P 242 Q A U} {body₁ : P → Pr P 248 Q A U}
  {body₂ : P → Pr P 256 Q A U} {body₃ : P → Pr P 264 Q A U}

def queuedHaloCoreReg : Fin 256 → Fin 264 := Fin.castLE (by decide)

theorem queuedHaloCoreReg_injective : Function.Injective queuedHaloCoreReg := by
  intro i j he
  exact Fin.ext (congrArg (fun k : Fin 264 => k.val) he)

noncomputable def queuedHaloCoreUsing (freshGeometry : Bool) (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P 264 Q A U :=
  .seq attachQueuedHalo (embProg queuedHaloCoreReg id (preparedHaloCoreUsing freshGeometry hR hQ))

noncomputable def queuedHaloCore (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P 264 Q A U :=
  queuedHaloCoreUsing true hR hQ

theorem queuedHaloCoreUsing_spec (freshGeometry : Bool) (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    (hbody : ∀ f, body₁ f = embProg packedBoundaryRecoveryBase id (body f))
    (hbody₁ : ∀ f, body₂ f = embProg packedHaloPublicationReg id (body₁ f))
    (hbody₂ : ∀ f, body₃ f = embProg queuedHaloCoreReg id (body₂ f))
    {p l s t u target rhsExp a b V : ℕ} [NeZero s] {α d : ℝ}
    (C : ZMod s → GaussianInt) (S : Stacks 242 A)
    (hsetup : PackedHaloSetup (freshGeometry := freshGeometry) (p := p) (l := l) (t := t) (u := u) (target := target)
      (rhsExp := rhsExp) (a := a) (b := b) (V := V) α d C S)
    (width k radius : ℕ) (ha : a = coreStart width k-radius)
    (hb : b = coreStart width k+coreLength s width k+radius) (hleft : radius ≤ coreStart width k)
    (v : HS 264 Q A U) (M : Stacks 264 A)
    (hview : embStk packedHaloPublicationReg (embStk queuedHaloCoreReg M) = extendStacks (by decide) S)
    (hoffset : (M.R 249).length = radius) (hrows : (M.R 250).length = coreLength s width k)
    (tail : List (Fin (A+4)))
    (hqueue : M.R 256 = cstream A (executionWidth p l
      (boundaryHaloTarget p u (boundaryRecoveryTarget p target) rhsExp
        (haloBoundary s t (PhaseCellBand.width p u) a b).card) rhsExp)
      (packedInterval a (b-a) C)++tail)
    (hfresh : ∀ i ∈ [(251 : Fin 264),252,253,254,255,258,259,260], M.R i = [])
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
      n ≤ attachQueuedHaloCost V q (b-a)+prepareHaloBufferCost q (coreLength s width k) radius+
        packedHaloSolveUsingCost freshGeometry p u l target rhsExp s t a b V+
        preparedPackedSliceCost radius (coreLength s width k) w+
        haloBufferReleaseCost (coreLength s width k) radius w ∧
      Exec body₃ (queuedHaloCoreUsing freshGeometry hR hQ) (mk v M) n (mk v' F) ∧
      F.inp = S.inp ∧ F.out = S.out ∧
      F.R 248 = cstream A w (ownedCoreWords width k D)++M.R 248 ∧
      F.R 132 = S.R 132 ∧ F.R 110 = S.R 110 ∧ F.R 255 = [] ∧ F.R 256 = tail ∧
      (∀ i, Fits w (D i)) ∧
      PhaseCellInterface.ErrorOn (ownedCore s width k)
        (fun i => (packedIntervalRead q w (coreStart width k) (F.R 248) i).re) x (1/(2 : ℝ)^target) ∧
      PackedHaloNativeClean (embStk (Fin.castLE (by decide : 168 ≤ 264)) F) ∧
      PackedHaloRetainedHeaders (2^15*p)
        (executionStagePrecision p l (initialSchurTarget p u bits 2) 2+1)
        q l s t u (PhaseCellBand.width p u) a b V w
        (embStk (Fin.castLE (by decide : 168 ≤ 264)) F) ∧
      ∀ i : Fin 264, 248 ≤ i.val → i ≠ 248 → i ≠ 256 → F.R i = M.R i := by
  dsimp only
  let B := haloBoundary s t (PhaseCellBand.width p u) a b
  let bits := boundaryTableBits p (boundaryRecoveryTarget p target) rhsExp B.card
  let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
  let j := boundaryHaloTarget p u (boundaryRecoveryTarget p target) rhsExp B.card
  let xs := cstream A (executionWidth p l j rhsExp) (packedInterval a (b-a) C)
  let S' : Stacks 242 A := {S with R := Function.update S.R 110 (xs++S.R 110)}
  have hbase : embStk queuedHaloBaseReg M = S := by
    have h := congrArg (embStk (Fin.castLE (by decide : 242 ≤ 248))) hview
    rw [embStk_extendStacks] at h
    exact h
  have h110 : M.R 110 = S.R 110 := by
    have h := congrArg (fun D : Stacks 242 A => D.R 110) hbase
    exact h
  obtain ⟨v₀,M₀,n₀,hu₀,hn₀,he₀,hstate,hframe,hbase₀,hqueue₀,hoff₀⟩ :=
    attachQueuedHalo_frame (body := body₃) C S hsetup v M hbase tail hqueue
      (by intro i hi; exact hfresh i (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢; tauto))
  let reg := fun i : Fin 248 => queuedHaloCoreReg (packedHaloPublicationReg i)
  have hinj : Function.Injective reg := by
    intro i j he
    exact Fin.ext (congrArg (fun k : Fin 264 => k.val) he)
  have hreg110 : reg 110 = 110 := by decide
  have hview₀ : embStk packedHaloPublicationReg (embStk queuedHaloCoreReg M₀) = extendStacks (by decide) S' := by
    have hvm : embStk reg M = extendStacks (by decide) S := hview
    have hoff : ∀ i, reg i ≠ 256 := by
      intro i he
      have hv := congrArg (fun k : Fin 264 => k.val) he
      have hi := i.isLt
      change i.val = 256 at hv
      omega
    have hupdate := embStk_updateR hinj {M with R := Function.update M.R 256 tail} 110 (xs++M.R 110)
    rw [hreg110,embStk_updateR_off M 256 tail hoff,hvm,h110] at hupdate
    have hext := extendStacks_updateR (by decide : 242 ≤ 248) S 110 (xs++S.R 110)
    have hcast : Fin.castLE (by decide : 242 ≤ 248) 110 = (110 : Fin 248) := by decide
    rw [hcast] at hext
    rw [hstate,h110]
    exact hupdate.trans hext.symm
  have hread₀ (i : Fin 256) (hi110 : i ≠ 110) : (embStk queuedHaloCoreReg M₀).R i = M.R (queuedHaloCoreReg i) :=
    hoff₀ _ (by intro he; apply hi110; apply Fin.ext; exact congrArg (fun k : Fin 264 => k.val) he)
      (by intro he; have hv := congrArg (fun k : Fin 264 => k.val) he; have hi := i.isLt; change i.val = 256 at hv; omega)
  obtain ⟨vi,Fi,n₁,D,hui,hn₁,hei,hin,hout,hpublished,h132,hsource,h255,hfits,herror,hnativeClean,hretainedHeaders,hframe₁⟩ :=
    preparedHaloCoreUsing_spec (body := body) (body' := body₁) (body'' := body₂)
      freshGeometry hR hQ hA hbody hbody₁ C (S.R 110) S' hframe width k radius ha hb hleft
      (embDn queuedHaloCoreReg v₀) (embStk queuedHaloCoreReg M₀) hview₀
      (by rw [hread₀ 249 (by decide)]; exact hoffset)
      (by rw [hread₀ 250 (by decide)]; exact hrows)
      (by
        intro i hi
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
        rcases hi with rfl | rfl | rfl | rfl | rfl <;>
          rw [hread₀ _ (by decide)] <;> apply hfresh <;> simp [queuedHaloCoreReg]) x hx
  obtain ⟨v₁,F,he₁,hv₁,hu₁,hview₁,hoff₁⟩ := exec_emb queuedHaloCoreReg_injective hbody₂ hei v₀ rfl M₀ rfl
  have hread₁ (i : Fin 256) : F.R (queuedHaloCoreReg i) = Fi.R i :=
    congrArg (fun D : Stacks 256 A => D.R i) hview₁
  have hhigh (i : Fin 264) (hi : 256 ≤ i.val) : F.R i = M₀.R i :=
    (hoff₁ i (by
      intro k he
      have hv := congrArg (fun j : Fin 264 => j.val) he
      have hk := k.isLt
      change k.val = i.val at hv
      omega)).2
  have hreg248 : queuedHaloCoreReg 248 = 248 := by decide
  have hreg132 : queuedHaloCoreReg 132 = 132 := by decide
  have hreg110' : queuedHaloCoreReg 110 = 110 := by decide
  have hreg255 : queuedHaloCoreReg 255 = 255 := by decide
  refine ⟨v₁,F,n₀+n₁,D,hu₁.trans (hui.trans hu₀),?_,Exec.seq he₀ he₁,
    (congrArg (fun D : Stacks 256 A => D.inp) hview₁).trans hin,
    (congrArg (fun D : Stacks 256 A => D.out) hview₁).trans hout,?_,?_,?_,?_,?_,hfits,?_,?_,?_,?_⟩
  · have hh := Nat.add_le_add hn₀ hn₁
    simpa only [Nat.add_assoc] using hh
  · rw [←hreg248,hread₁,hpublished,hread₀ 248 (by decide),hreg248]
  · simpa only [S',Function.update_of_ne (by decide : (132 : Fin 242) ≠ 110),hreg132] using
      (hread₁ 132).trans h132
  · simpa only [hreg110'] using (hread₁ 110).trans hsource
  · simpa only [hreg255] using (hread₁ 255).trans h255
  · exact (hhigh 256 (by decide)).trans hqueue₀
  · have hh : F.R 248 = Fi.R 248 := by simpa only [hreg248] using hread₁ 248
    rw [hh]
    exact herror
  · have hv : embStk (Fin.castLE (by decide : 168 ≤ 264)) F =
        embStk (Fin.castLE (by decide : 168 ≤ 256)) Fi :=
      congrArg (embStk (Fin.castLE (by decide : 168 ≤ 256))) hview₁
    rw [hv]
    exact hnativeClean
  · have hv : embStk (Fin.castLE (by decide : 168 ≤ 264)) F =
        embStk (Fin.castLE (by decide : 168 ≤ 256)) Fi :=
      congrArg (embStk (Fin.castLE (by decide : 168 ≤ 256))) hview₁
    rw [hv]
    exact hretainedHeaders
  · intro i hi hi248 hi256
    by_cases hsmall : i.val < 256
    · let j : Fin 256 := ⟨i.val,hsmall⟩
      have heq : queuedHaloCoreReg j = i := Fin.ext rfl
      have hj248 : j ≠ 248 := by
        intro he
        apply hi248
        apply Fin.ext
        exact congrArg (fun k : Fin 256 => k.val) he
      have hj110 : j ≠ 110 := by
        intro he
        have hv := congrArg (fun k : Fin 256 => k.val) he
        change i.val = 110 at hv
        omega
      rw [←heq,hread₁ j]
      exact (hframe₁ j hi hj248).trans (hread₀ j hj110)
    · exact (hhigh i (by omega)).trans
        (hoff₀ i (by intro he; subst i; norm_num at hi) hi256)

theorem queuedHaloCore_spec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    (hbody : ∀ f, body₁ f = embProg packedBoundaryRecoveryBase id (body f))
    (hbody₁ : ∀ f, body₂ f = embProg packedHaloPublicationReg id (body₁ f))
    (hbody₂ : ∀ f, body₃ f = embProg queuedHaloCoreReg id (body₂ f))
    {p l s t u target rhsExp a b V : ℕ} [NeZero s] {α d : ℝ}
    (C : ZMod s → GaussianInt) (S : Stacks 242 A)
    (hsetup : PackedHaloSetup (p := p) (l := l) (t := t) (u := u) (target := target)
      (rhsExp := rhsExp) (a := a) (b := b) (V := V) α d C S)
    (width k radius : ℕ) (ha : a = coreStart width k-radius)
    (hb : b = coreStart width k+coreLength s width k+radius) (hleft : radius ≤ coreStart width k)
    (v : HS 264 Q A U) (M : Stacks 264 A)
    (hview : embStk packedHaloPublicationReg (embStk queuedHaloCoreReg M) = extendStacks (by decide) S)
    (hoffset : (M.R 249).length = radius) (hrows : (M.R 250).length = coreLength s width k)
    (tail : List (Fin (A+4)))
    (hqueue : M.R 256 = cstream A (executionWidth p l
      (boundaryHaloTarget p u (boundaryRecoveryTarget p target) rhsExp
        (haloBoundary s t (PhaseCellBand.width p u) a b).card) rhsExp)
      (packedInterval a (b-a) C)++tail)
    (hfresh : ∀ i ∈ [(251 : Fin 264),252,253,254,255,258,259,260], M.R i = [])
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
      n ≤ attachQueuedHaloCost V q (b-a)+prepareHaloBufferCost q (coreLength s width k) radius+
        packedHaloSolveCost p u l target rhsExp s t a b V+
        preparedPackedSliceCost radius (coreLength s width k) w+
        haloBufferReleaseCost (coreLength s width k) radius w ∧
      Exec body₃ (queuedHaloCore hR hQ) (mk v M) n (mk v' F) ∧
      F.inp = S.inp ∧ F.out = S.out ∧
      F.R 248 = cstream A w (ownedCoreWords width k D)++M.R 248 ∧
      F.R 132 = S.R 132 ∧ F.R 110 = S.R 110 ∧ F.R 255 = [] ∧ F.R 256 = tail ∧
      (∀ i, Fits w (D i)) ∧
      PhaseCellInterface.ErrorOn (ownedCore s width k)
        (fun i => (packedIntervalRead q w (coreStart width k) (F.R 248) i).re) x (1/(2 : ℝ)^target) ∧
      PackedHaloNativeClean (embStk (Fin.castLE (by decide : 168 ≤ 264)) F) ∧
      PackedHaloRetainedHeaders (2^15*p)
        (executionStagePrecision p l (initialSchurTarget p u bits 2) 2+1)
        q l s t u (PhaseCellBand.width p u) a b V w
        (embStk (Fin.castLE (by decide : 168 ≤ 264)) F) ∧
      ∀ i : Fin 264, 248 ≤ i.val → i ≠ 248 → i ≠ 256 → F.R i = M.R i := by
  exact queuedHaloCoreUsing_spec (body := body) (body₁ := body₁) (body₂ := body₂) (body₃ := body₃) true
    hR hQ hA hbody hbody₁ hbody₂ C S hsetup width k radius ha hb hleft
    v M hview hoffset hrows tail hqueue hfresh x hx

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
