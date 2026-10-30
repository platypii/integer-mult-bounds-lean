module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellProtectedCoreGatherInput
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellQueuedHaloCore
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPrepareHaloHeaders
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPrepareCoreDimensions

/-! Generate a fitting core batch, initialize its first coordinate headers, and solve.
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
  .seq protectedCoreGather (.seq (prepareCoreDimensions 266 165 249 250 269 270 271)
    (.seq (prepareHaloHeaders 163 257 165 141 142 155 261 269 270 271)
      (embProg gatheredHaloCoreReg id (queuedHaloCore hR hQ))))

theorem gatheredHaloCore_spec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    (hbody : ∀ f, body₁ f = embProg packedBoundaryRecoveryBase id (body f))
    (hbody₁ : ∀ f, body₂ f = embProg packedHaloPublicationReg id (body₁ f))
    (hbody₂ : ∀ f, body₃ f = embProg queuedHaloCoreReg id (body₂ f))
    (hbody₃ : ∀ f, body₄ f = embProg gatheredHaloCoreReg id (body₃ f))
    {p l s t u target rhsExp a b V width k radius : ℕ} [NeZero s] {α d : ℝ}
    (C : ZMod s → GaussianInt) (S : Stacks 242 A)
    (hsetup : PackedHaloSetup (p := p) (l := l) (t := t) (u := u) (target := target)
      (rhsExp := rhsExp) (a := a) (b := b) (V := V) α d C (haloHeaderBank V a b S))
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
    (hdimensions : ∀ i ∈ [(249 : Fin 272),250], M.R i = [])
    (hfresh : ∀ i ∈ [(251 : Fin 272),252,253,254,255,258,259,260,269,270,271], M.R i = [])
    (hheaders : ∀ i ∈ [(141 : Fin 272),142,155], M.R i = [])
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
      n ≤ protectedCoreGatherCost V q s width radius (b-a)+prepareCoreDimensionsCost V (b-a) radius+
        prepareHaloHeadersCost V a (b-a)+
        attachQueuedHaloCost V q (b-a)+prepareHaloBufferCost q (coreLength s width k) radius+
        packedHaloSolveCost p u l target rhsExp s t a b V+
        preparedPackedSliceCost radius (coreLength s width k) w+
        haloBufferReleaseCost (coreLength s width k) radius w ∧
      Exec body₄ (gatheredHaloCore hR hQ) (mk v M) n (mk v' F) ∧
      F.inp = S.inp ∧ F.out = S.out ∧
      F.R 248 = cstream A w (ownedCoreWords width k D)++M.R 248 ∧
      F.R 132 = S.R 132 ∧ F.R 110 = S.R 110 ∧ F.R 255 = [] ∧
      F.R 249 = List.replicate radius tick ∧ F.R 250 = List.replicate (coreLength s width k) tick ∧
      F.R 256 = ks.flatMap (fun i => cstream A w
        (packedInterval (coreStart width i-radius) (b-a) C))++M.R 256 ∧
      F.R 257 = ks.flatMap
        (fun i => binSyms V (coreStart width i-radius))++M.R 257 ∧
      F.R 261 = List.replicate ks.length tick ∧
      (∀ i, Fits w (D i)) ∧
      PhaseCellInterface.ErrorOn (ownedCore s width k)
        (fun i => (packedIntervalRead q w (coreStart width k) (F.R 248) i).re) x (1/(2 : ℝ)^target) ∧
      PackedHaloNativeClean (embStk (Fin.castLE (by decide : 168 ≤ 272)) F) ∧
      PackedHaloRetainedHeaders (2^15*p)
        (executionStagePrecision p l (initialSchurTarget p u bits 2) 2+1)
        q l s t u (PhaseCellBand.width p u) a b V w
        (embStk (Fin.castLE (by decide : 168 ≤ 272)) F) ∧
      ∀ i : Fin 272, 248 ≤ i.val → i ≠ 248 → i ≠ 249 → i ≠ 250 → i ≠ 256 → i ≠ 257 → i ≠ 261 → F.R i = M.R i := by
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
  let S' := haloHeaderBank V a b S
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
  have hlength : b-a = coreLength s width k+2*radius :=
    (coreGatherIndices_spec s width radius (b-a) k (by rw [hhead]; simp)).2.2.symm
  have hrFit : radius < 2^V := by have hh := hgather.hwide; omega
  have hlenFit : coreLength s width k+2*radius < 2^V := by
    rw [←hlength]
    exact hgather.hLfit
  obtain ⟨vd,nd,hud,hnd,hed⟩ := prepareCoreDimensions_exec (body := body₄)
    (radiusWord := 266) (lengthWord := 165) (radius := 249) (rows := 250)
    (work := 269) (saved := 270) (tmp := 271) (by decide)
    V (coreLength s width k) radius hrFit hlenFit v₀ G
    (by simpa [G] using hgather.hr) (by simpa [G,hlength] using hgather.hL)
    (by
      intro i hi
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl
      · simpa [G] using hdimensions 249 (by simp)
      · simpa [G] using hdimensions 250 (by simp)
      · simpa [G] using hfresh 269 (by simp)
      · simpa [G] using hfresh 270 (by simp)
      · simpa [G] using hfresh 271 (by simp))
  let J : Stacks 272 A := {G with R := (Function.update (Function.update G.R
    249 (List.replicate radius tick)) 250 (List.replicate (coreLength s width k) tick))}
  have hed' : Exec body₄ (prepareCoreDimensions 266 165 249 250 269 270 271)
      (mk v₀ G) nd (mk vd J) := hed
  have hnd' : nd ≤ prepareCoreDimensionsCost V (b-a) radius := by
    simpa only [←hlength] using hnd
  have haFit : a < 2^V := by have hh := hsetup.hfitV; omega
  have hLfit : b-a < 2^V := by have hh := hsetup.hfitV; omega
  obtain ⟨vc,nc,huc,hnc,hec⟩ := prepareHaloHeaders_exec (body := body₄)
    (width := 163) (src := 257) (lengthWord := 165) (aMaster := 141) (bMaster := 142)
    (word := 155) (count := 261) (work := 269) (saved := 270) (tmp := 271)
    (by decide) V a (b-a) haFit hLfit originTail (List.replicate ks.length tick) vd J
    (by simpa [J,G] using hgather.h163)
    (by rw [ha]; simpa [J] using hOrigin) (by simpa [J,G] using hgather.hL) (by simpa [J] using hCount)
    (by
      intro i hi
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl
      · simpa [J,G] using hheaders 141 (by simp)
      · simpa [J,G] using hheaders 142 (by simp)
      · simpa [J,G] using hheaders 155 (by simp)
      · simpa [J,G] using hfresh 269 (by simp)
      · simpa [J,G] using hfresh 270 (by simp)
      · simpa [J,G] using hfresh 271 (by simp))
  let headerG : Stacks 272 A := {J with R := haloHeaderR 141 142 155 V a b J.R}
  let H : Stacks 272 A := {headerG with R := (Function.update (Function.update headerG.R 257 originTail)
    261 (List.replicate ks.length tick))}
  have hec' : Exec body₄ (prepareHaloHeaders 163 257 165 141 142 155 261 269 270 271)
      (mk vd J) nc (mk vc H) := by
    simpa only [H,headerG,Nat.add_sub_of_le hsetup.hab] using hec
  have hoffH (i : Fin 272) (hi : 168 ≤ i.val) (h249 : i ≠ 249) (h250 : i ≠ 250) (h256 : i ≠ 256) (h257 : i ≠ 257) (h261 : i ≠ 261) : H.R i = M.R i := by
    have h141 : i ≠ 141 := by intro he; subst i; norm_num at hi
    have h142 : i ≠ 142 := by intro he; subst i; norm_num at hi
    have h155 : i ≠ 155 := by intro he; subst i; norm_num at hi
    simp [H,headerG,J,G,haloHeaderR,h249,h250,h256,h257,h261,h141,h142,h155]
  let reg := fun i : Fin 248 => gatheredHaloCoreReg (queuedHaloCoreReg (packedHaloPublicationReg i))
  have hviewH : embStk packedHaloPublicationReg (embStk queuedHaloCoreReg
      (embStk gatheredHaloCoreReg H)) = extendStacks (by decide) S' := by
    have hoff (j : Fin 272) (hj : 248 ≤ j.val) : ∀ i, reg i ≠ j := by
      intro i he
      have hv := congrArg (fun k : Fin 272 => k.val) he
      have hi := i.isLt
      change i.val = j.val at hv
      omega
    have hviewJ : embStk reg J = extendStacks (by decide) S := by
      have heq : embStk reg J = embStk reg M := by
        refine Stacks.ext rfl rfl rfl ?_
        funext i
        simp only [embStk,Function.comp_apply,J,G,
          Function.update_of_ne (hoff 250 (by decide) i),
          Function.update_of_ne (hoff 249 (by decide) i),
          Function.update_of_ne (hoff 261 (by decide) i),
          Function.update_of_ne (hoff 257 (by decide) i),
          Function.update_of_ne (hoff 256 (by decide) i)]
      exact heq.trans hview
    have hinj : Function.Injective reg := by
      intro i j he
      exact Fin.ext (congrArg (fun k : Fin 272 => k.val) he)
    have hreg141 : reg 141 = 141 := by decide
    have hreg142 : reg 142 = 142 := by decide
    have hreg155 : reg 155 = 155 := by decide
    have hh := embStk_haloHeaderR hinj J 141 142 155 V a b
    rw [hreg141,hreg142,hreg155,hviewJ] at hh
    have hext := extendStacks_haloHeaderR (by decide : 242 ≤ 248) S 141 142 155 V a b
    have hc141 : Fin.castLE (by decide : 242 ≤ 248) 141 = (141 : Fin 248) := by decide
    have hc142 : Fin.castLE (by decide : 242 ≤ 248) 142 = (142 : Fin 248) := by decide
    have hc155 : Fin.castLE (by decide : 242 ≤ 248) 155 = (155 : Fin 248) := by decide
    rw [hc141,hc142,hc155] at hext
    change embStk reg {{headerG with R := Function.update headerG.R 257 originTail} with
      R := (Function.update (Function.update headerG.R 257 originTail) 261 (List.replicate ks.length tick))} = _
    rw [embStk_updateR_off _ 261 _ (hoff 261 (by decide)),
      embStk_updateR_off headerG 257 originTail (hoff 257 (by decide))]
    exact hh.trans hext.symm
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
    have h256 : H.R 256 = G.R 256 := by simp [H,headerG,J,haloHeaderR]
    rw [h256]
    simp only [G,Function.update_of_ne (by decide : (256 : Fin 272) ≠ 261),
      Function.update_of_ne (by decide : (256 : Fin 272) ≠ 257),Function.update_self]
    rw [hwidth]
    simp only [batch,hhead,List.flatMap_cons,←ha,List.append_assoc,tail]
  have hreadH (i : Fin 264) (hi : 168 ≤ i.val) (h249 : i ≠ 249) (h250 : i ≠ 250) (h256 : i ≠ 256) (h257 : i ≠ 257) (h261 : i ≠ 261) :
      (embStk gatheredHaloCoreReg H).R i = M.R (gatheredHaloCoreReg i) :=
    hoffH _ hi
      (by intro he; apply h249; apply Fin.ext; exact congrArg (fun k : Fin 272 => k.val) he)
      (by intro he; apply h250; apply Fin.ext; exact congrArg (fun k : Fin 272 => k.val) he)
      (by intro he; apply h256; apply Fin.ext; exact congrArg (fun k : Fin 272 => k.val) he)
      (by intro he; apply h257; apply Fin.ext; exact congrArg (fun k : Fin 272 => k.val) he)
      (by intro he; apply h261; apply Fin.ext; exact congrArg (fun k : Fin 272 => k.val) he)
  obtain ⟨vi,Fi,n₁,D,hui,hn₁,hei,hin,hout,hpublished,h132,hsource,h255,hqueue₁,hfits,herror,hnativeClean,hretainedHeaders,hframe⟩ :=
    queuedHaloCore_spec (body := body) (body₁ := body₁) (body₂ := body₂) (body₃ := body₃)
      hR hQ hA hbody hbody₁ hbody₂ C S' hsetup width k radius ha hb hleft
      (embDn gatheredHaloCoreReg vc) (embStk gatheredHaloCoreReg H) hviewH
      (by simp [embStk,Function.comp_apply,gatheredHaloCoreReg,H,headerG,J,haloHeaderR])
      (by simp [embStk,Function.comp_apply,gatheredHaloCoreReg,H,headerG,J,haloHeaderR]) tail hqueue
      (by
        intro i hi
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
        rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          rw [hreadH _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)] <;> apply hfresh <;> simp [gatheredHaloCoreReg]) x hx
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
  refine ⟨v₁,F,n₀+(nd+(nc+n₁)),D,hu₁.trans (hui.trans (huc.trans (hud.trans hu₀))),?_,
    Exec.seq he₀' (Exec.seq hed' (Exec.seq hec' he₁)),
    (congrArg (fun H : Stacks 264 A => H.inp) hview₁).trans hin,
    (congrArg (fun H : Stacks 264 A => H.out) hview₁).trans hout,?_,?_,?_,?_,?_,?_,?_,?_,?_,hfits,?_,?_,?_,?_⟩
  · have hh := Nat.add_le_add hn₀ (Nat.add_le_add hnd' (Nat.add_le_add hnc hn₁))
    simpa only [Nat.add_assoc] using hh
  · rw [←hreg248,hreadF,hpublished,hreadH 248 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),hreg248]
  · simpa [S',haloHeaderBank,haloHeaderR,hreg132] using (hreadF 132).trans h132
  · simpa [S',haloHeaderBank,haloHeaderR,hreg110] using (hreadF 110).trans hsource
  · simpa only [hreg255] using (hreadF 255).trans h255
  · have hr : gatheredHaloCoreReg 249 = 249 := by decide
    rw [←hr,hreadF,hframe 249 (by decide) (by decide) (by decide)]
    simp [embStk,Function.comp_apply,hr,H,headerG,J,haloHeaderR]
  · have hr : gatheredHaloCoreReg 250 = 250 := by decide
    rw [←hr,hreadF,hframe 250 (by decide) (by decide) (by decide)]
    simp [embStk,Function.comp_apply,hr,H,headerG,J,haloHeaderR]
  · simpa only [hreg256] using (hreadF 256).trans hqueue₁
  · rw [←hreg257,hreadF,hframe 257 (by decide) (by decide) (by decide)]
    simp [embStk,Function.comp_apply,hreg257,H,originTail]
  · rw [←hreg261,hreadF,hframe 261 (by decide) (by decide) (by decide)]
    simp [embStk,Function.comp_apply,hreg261,H]
  · have hh : F.R 248 = Fi.R 248 := by simpa only [hreg248] using hreadF 248
    rw [hh]
    exact herror
  · have hv : embStk (Fin.castLE (by decide : 168 ≤ 272)) F =
        embStk (Fin.castLE (by decide : 168 ≤ 264)) Fi :=
      congrArg (embStk (Fin.castLE (by decide : 168 ≤ 264))) hview₁
    rw [hv]
    exact hnativeClean
  · have hv : embStk (Fin.castLE (by decide : 168 ≤ 272)) F =
        embStk (Fin.castLE (by decide : 168 ≤ 264)) Fi :=
      congrArg (embStk (Fin.castLE (by decide : 168 ≤ 264))) hview₁
    rw [hv]
    exact hretainedHeaders
  · intro i hi hi248 hi249 hi250 hi256 hi257 hi261
    by_cases hsmall : i.val < 264
    · let j : Fin 264 := ⟨i.val,hsmall⟩
      have heq : gatheredHaloCoreReg j = i := Fin.ext rfl
      have hj248 : j ≠ 248 := by intro he; apply hi248; apply Fin.ext; exact congrArg (fun k : Fin 264 => k.val) he
      have hj249 : j ≠ 249 := by intro he; apply hi249; apply Fin.ext; exact congrArg (fun k : Fin 264 => k.val) he
      have hj250 : j ≠ 250 := by intro he; apply hi250; apply Fin.ext; exact congrArg (fun k : Fin 264 => k.val) he
      have hj256 : j ≠ 256 := by intro he; apply hi256; apply Fin.ext; exact congrArg (fun k : Fin 264 => k.val) he
      have hj257 : j ≠ 257 := by intro he; apply hi257; apply Fin.ext; exact congrArg (fun k : Fin 264 => k.val) he
      have hj261 : j ≠ 261 := by intro he; apply hi261; apply Fin.ext; exact congrArg (fun k : Fin 264 => k.val) he
      rw [←heq,hreadF j]
      exact (hframe j hi hj248 hj256).trans (hreadH j (by change 168 ≤ i.val; omega) hj249 hj250 hj256 hj257 hj261)
    · have hh := (hoff₁ i (by
        intro j he
        have hv := congrArg (fun k : Fin 272 => k.val) he
        have hj := j.isLt
        change j.val = i.val at hv
        omega)).2
      exact hh.trans (hoffH i (by omega) hi249 hi250 hi256 hi257 hi261)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
