module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellProtectedCoreGatherInput
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellQueuedHaloCore
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellAdvanceGroupCursor

/-! Generate a fitting core batch and execute its first concrete local solve.
The remaining generated windows stay queued for subsequent calls. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry ScalarPlacement

variable {Q A : ℕ} {P U : Type}
  {body : P → Pr P 242 Q A U} {body₁ : P → Pr P 248 Q A U}
  {body₂ : P → Pr P 256 Q A U} {body₃ : P → Pr P 264 Q A U}
  {body₄ : P → Pr P 272 Q A U}

def gatheredHaloCoreReg : Fin 264 → Fin 272 := Fin.castLE (by decide)

theorem gatheredHaloCoreReg_injective : Function.Injective gatheredHaloCoreReg := by
  intro i j he
  exact Fin.ext (congrArg (fun k : Fin 272 => k.val) he)

noncomputable def gatheredHaloCore (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P 272 Q A U :=
  .seq protectedCoreGather (.seq (advanceGroupCursor 163 257 261 269 270)
    (embProg gatheredHaloCoreReg id (queuedHaloCore hR hQ)))

theorem gatheredHaloCore_spec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    (hbody : ∀ f, body₁ f = embProg packedBoundaryRecoveryBase id (body f))
    (hbody₁ : ∀ f, body₂ f = embProg packedHaloPublicationReg id (body₁ f))
    (hbody₂ : ∀ f, body₃ f = embProg queuedHaloCoreReg id (body₂ f))
    (hbody₃ : ∀ f, body₄ f = embProg gatheredHaloCoreReg id (body₃ f))
    {p l s t u target rhsExp a b V width k radius : ℕ} [NeZero s] {α d : ℝ}
    (C : ZMod s → GaussianInt) (S : Stacks 242 A)
    (hsetup : PackedHaloSetup (p := p) (l := l) (t := t) (u := u) (target := target)
      (rhsExp := rhsExp) (a := a) (b := b) (V := V) α d C S)
    (ha : a = coreStart width k-radius) (hb : b = coreStart width k+coreLength s width k+radius)
    (hleft : radius ≤ coreStart width k) (ks : List ℕ)
    (hhead : coreGatherIndices s width radius (b-a) = k::ks)
    (v : HS 272 Q A U) (M : Stacks 272 A)
    (hview : embStk packedHaloPublicationReg (embStk queuedHaloCoreReg
      (embStk gatheredHaloCoreReg M)) = extendStacks (by decide) S)
    (hgather : let B := haloBoundary s t (PhaseCellBand.width p u) a b
      let bits := boundaryTableBits p (boundaryRecoveryTarget p target) rhsExp B.card
      ProtectedCoreGatherInput V (executionPrecision p l (initialSchurTarget p u bits 2) 2)
        s width radius (b-a) C M)
    (hoffset : (M.R 249).length = radius) (hrows : (M.R 250).length = coreLength s width k)
    (hfresh : ∀ i ∈ [(251 : Fin 272),252,253,254,255,258,259,260,269,270], M.R i = [])
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
      n ≤ protectedCoreGatherCost V q s width radius (b-a)+(6*V+7)+
        attachQueuedHaloCost V q (b-a)+prepareHaloBufferCost q (coreLength s width k) radius+
        packedHaloSolveCost p u l target rhsExp s t a b V+
        preparedPackedSliceCost radius (coreLength s width k) w+
        haloBufferReleaseCost (coreLength s width k) radius w ∧
      Exec body₄ (gatheredHaloCore hR hQ) (mk v M) n (mk v' F) ∧
      F.inp = S.inp ∧ F.out = S.out ∧
      F.R 248 = cstream A w (ownedCoreWords width k D)++M.R 248 ∧
      F.R 132 = S.R 132 ∧ F.R 110 = S.R 110 ∧ F.R 255 = [] ∧
      F.R 256 = ks.flatMap (fun i => cstream A w
        (packedInterval (coreStart width i-radius) (b-a) C))++M.R 256 ∧
      F.R 257 = ks.flatMap
        (fun i => binSyms V (coreStart width i-radius))++M.R 257 ∧
      F.R 261 = List.replicate ks.length tick ∧
      (∀ i, Fits w (D i)) ∧
      PhaseCellInterface.ErrorOn (ownedCore s width k)
        (fun i => (packedIntervalRead q w (coreStart width k) (F.R 248) i).re) x (1/(2 : ℝ)^target) ∧
      ∀ i : Fin 272, 248 ≤ i.val → i ≠ 248 → i ≠ 256 → i ≠ 257 → i ≠ 261 → F.R i = M.R i := by
  dsimp only at hgather ⊢
  let B := haloBoundary s t (PhaseCellBand.width p u) a b
  let bits := boundaryTableBits p (boundaryRecoveryTarget p target) rhsExp B.card
  let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
  let w := 2*q+8
  let batch := (coreGatherIndices s width radius (b-a)).flatMap
    (fun i => cstream A w (packedInterval (coreStart width i-radius) (b-a) C))
  let origins := (coreGatherIndices s width radius (b-a)).flatMap
    (fun i => binSyms (A := A) V (coreStart width i-radius))
  let count := List.replicate (coreGatherIndices s width radius (b-a)).length (tick : Fin (A+4))
  let tail := ks.flatMap (fun i => cstream A w (packedInterval (coreStart width i-radius) (b-a) C))++M.R 256
  obtain ⟨v₀,n₀,hu₀,hn₀,he₀⟩ := hgather.run (body := body₄) (by rw [hhead]; simp) v
  let G : Stacks 272 A := {M with R := (Function.update (Function.update (Function.update M.R
    256 (batch++M.R 256)) 257 (origins++M.R 257)) 261 count)}
  have he₀' : Exec body₄ protectedCoreGather (mk v M) n₀ (mk v₀ G) := by
    simpa only [G,batch,origins,count,w,q,bits,B] using he₀
  let originTail := ks.flatMap (fun i => binSyms (A := A) V (coreStart width i-radius))++M.R 257
  have hOrigin : G.R 257 = binSyms V (coreStart width k-radius)++originTail := by
    simp [G,origins,hhead,List.append_assoc,originTail]
  have hCount : G.R 261 = tick::List.replicate ks.length tick := by
    simp [G,count,hhead,List.replicate_succ]
  obtain ⟨vc,huc,hec⟩ := advanceGroupCursor_exec (body := body₄)
    (width := 163) (origins := 257) (count := 261) (trash := 269) (tmp := 270)
    (by decide) V (binSyms V (coreStart width k-radius)) originTail (List.replicate ks.length tick)
    (by simp) v₀ G (by simpa [G] using hgather.h163) hOrigin hCount
    (by simpa [G] using hfresh 269 (by simp)) (by simpa [G] using hfresh 270 (by simp))
  let H : Stacks 272 A := {G with R := (Function.update (Function.update G.R 257 originTail)
    261 (List.replicate ks.length tick))}
  have hec' : Exec body₄ (advanceGroupCursor 163 257 261 269 270)
      (mk v₀ G) (6*V+7) (mk vc H) := hec
  have hoffH (i : Fin 272) (h256 : i ≠ 256) (h257 : i ≠ 257) (h261 : i ≠ 261) : H.R i = M.R i := by
    simp [H,G,h256,h257,h261]
  let reg := fun i : Fin 248 => gatheredHaloCoreReg (queuedHaloCoreReg (packedHaloPublicationReg i))
  have hviewH : embStk packedHaloPublicationReg (embStk queuedHaloCoreReg
      (embStk gatheredHaloCoreReg H)) = extendStacks (by decide) S := by
    have hoff (j : Fin 272) (hj : 256 ≤ j.val) : ∀ i, reg i ≠ j := by
      intro i he
      have hv := congrArg (fun k : Fin 272 => k.val) he
      have hi := i.isLt
      change i.val = j.val at hv
      omega
    have heq : embStk reg H = embStk reg M := by
      refine Stacks.ext rfl rfl rfl ?_
      funext i
      simp only [embStk,Function.comp_apply,H,G,
        Function.update_of_ne (hoff 261 (by decide) i),
        Function.update_of_ne (hoff 257 (by decide) i),
        Function.update_of_ne (hoff 256 (by decide) i)]
    exact heq.trans hview
  have hwidth : executionWidth p l
      (boundaryHaloTarget p u (boundaryRecoveryTarget p target) rhsExp B.card) rhsExp = w := by
    have hh := (boundaryHaloTarget_sizing p u l (boundaryRecoveryTarget p target) rhsExp B.card).2.2
    change executionWidth p l
      (boundaryHaloTarget p u (boundaryRecoveryTarget p target) rhsExp B.card) rhsExp =
        executionWidth p l (initialSchurTarget p u bits 2) 2 at hh
    rw [hh]
    dsimp only [w,q,executionWidth,executionPrecision]
    omega
  have hqueue : (embStk gatheredHaloCoreReg H).R 256 =
      cstream A (executionWidth p l
        (boundaryHaloTarget p u (boundaryRecoveryTarget p target) rhsExp B.card) rhsExp)
        (packedInterval a (b-a) C)++tail := by
    have hreg : gatheredHaloCoreReg 256 = 256 := by decide
    simp only [embStk,Function.comp_apply,hreg]
    simp only [H,G,Function.update_of_ne (by decide : (256 : Fin 272) ≠ 261),
      Function.update_of_ne (by decide : (256 : Fin 272) ≠ 257),Function.update_self]
    rw [hwidth]
    simp only [batch,hhead,List.flatMap_cons,←ha,List.append_assoc,tail]
  have hreadH (i : Fin 264) (h256 : i ≠ 256) (h257 : i ≠ 257) (h261 : i ≠ 261) :
      (embStk gatheredHaloCoreReg H).R i = M.R (gatheredHaloCoreReg i) :=
    hoffH _ (by intro he; apply h256; apply Fin.ext; exact congrArg (fun k : Fin 272 => k.val) he)
      (by intro he; apply h257; apply Fin.ext; exact congrArg (fun k : Fin 272 => k.val) he)
      (by intro he; apply h261; apply Fin.ext; exact congrArg (fun k : Fin 272 => k.val) he)
  obtain ⟨vi,Fi,n₁,D,hui,hn₁,hei,hin,hout,hpublished,h132,hsource,h255,hqueue₁,hfits,herror,hframe⟩ :=
    queuedHaloCore_spec (body := body) (body₁ := body₁) (body₂ := body₂) (body₃ := body₃)
      hR hQ hA hbody hbody₁ hbody₂ C S hsetup width k radius ha hb hleft
      (embDn gatheredHaloCoreReg vc) (embStk gatheredHaloCoreReg H) hviewH
      (by rw [hreadH 249 (by decide) (by decide) (by decide)]; exact hoffset)
      (by rw [hreadH 250 (by decide) (by decide) (by decide)]; exact hrows) tail hqueue
      (by
        intro i hi
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
        rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          rw [hreadH _ (by decide) (by decide) (by decide)] <;> apply hfresh <;> simp [gatheredHaloCoreReg]) x hx
  obtain ⟨v₁,F,he₁,hv₁,hu₁,hview₁,hoff₁⟩ := exec_emb gatheredHaloCoreReg_injective hbody₃ hei vc rfl H rfl
  have hreadF (i : Fin 264) : F.R (gatheredHaloCoreReg i) = Fi.R i :=
    congrArg (fun H : Stacks 264 A => H.R i) hview₁
  have hreg248 : gatheredHaloCoreReg 248 = 248 := by decide
  have hreg132 : gatheredHaloCoreReg 132 = 132 := by decide
  have hreg110 : gatheredHaloCoreReg 110 = 110 := by decide
  have hreg255 : gatheredHaloCoreReg 255 = 255 := by decide
  have hreg256 : gatheredHaloCoreReg 256 = 256 := by decide
  have hreg257 : gatheredHaloCoreReg 257 = 257 := by decide
  have hreg261 : gatheredHaloCoreReg 261 = 261 := by decide
  refine ⟨v₁,F,n₀+((6*V+7)+n₁),D,hu₁.trans (hui.trans (huc.trans hu₀)),?_,
    Exec.seq he₀' (Exec.seq hec' he₁),
    (congrArg (fun H : Stacks 264 A => H.inp) hview₁).trans hin,
    (congrArg (fun H : Stacks 264 A => H.out) hview₁).trans hout,?_,?_,?_,?_,?_,?_,?_,hfits,?_,?_⟩
  · have hh := Nat.add_le_add hn₀ (Nat.add_le_add_left hn₁ (6*V+7))
    simpa only [Nat.add_assoc] using hh
  · rw [←hreg248,hreadF,hpublished,hreadH 248 (by decide) (by decide) (by decide),hreg248]
  · simpa only [hreg132] using (hreadF 132).trans h132
  · simpa only [hreg110] using (hreadF 110).trans hsource
  · simpa only [hreg255] using (hreadF 255).trans h255
  · simpa only [hreg256] using (hreadF 256).trans hqueue₁
  · rw [←hreg257,hreadF,hframe 257 (by decide) (by decide) (by decide)]
    simp [embStk,Function.comp_apply,hreg257,H,originTail]
  · rw [←hreg261,hreadF,hframe 261 (by decide) (by decide) (by decide)]
    simp [embStk,Function.comp_apply,hreg261,H]
  · have hh : F.R 248 = Fi.R 248 := by simpa only [hreg248] using hreadF 248
    rw [hh]
    exact herror
  · intro i hi hi248 hi256 hi257 hi261
    by_cases hsmall : i.val < 264
    · let j : Fin 264 := ⟨i.val,hsmall⟩
      have heq : gatheredHaloCoreReg j = i := Fin.ext rfl
      have hj248 : j ≠ 248 := by intro he; apply hi248; apply Fin.ext; exact congrArg (fun k : Fin 264 => k.val) he
      have hj256 : j ≠ 256 := by intro he; apply hi256; apply Fin.ext; exact congrArg (fun k : Fin 264 => k.val) he
      have hj257 : j ≠ 257 := by intro he; apply hi257; apply Fin.ext; exact congrArg (fun k : Fin 264 => k.val) he
      have hj261 : j ≠ 261 := by intro he; apply hi261; apply Fin.ext; exact congrArg (fun k : Fin 264 => k.val) he
      rw [←heq,hreadF j]
      exact (hframe j hi hj248 hj256).trans (hreadH j hj256 hj257 hj261)
    · have hh := (hoff₁ i (by
        intro j he
        have hv := congrArg (fun k : Fin 272 => k.val) he
        have hj := j.isLt
        change j.val = i.val at hv
        omega)).2
      exact hh.trans (hoffH i hi256 hi257 hi261)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
