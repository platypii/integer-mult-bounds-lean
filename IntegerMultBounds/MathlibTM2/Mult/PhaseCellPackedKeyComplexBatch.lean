module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedKeyComplexRealBatch
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedCoreRows
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellComponentSolutionMagnitude

/-! Execute complex local inputs through the shared real solver and complex output assembly. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.BandFactor
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {P U : Type}
variable {body : P → Pr P 242 Q A U} {body' : P → Pr P 248 Q A U}
  {body'' : P → Pr P 249 Q A U} {bodyLarge : P → Pr P 263 Q A U}

def complexBatchReg : Fin 277 → Fin 280 := Fin.castLE (by decide)

theorem complexBatchReg_injective : Function.Injective complexBatchReg := by
  intro i j h
  exact Fin.ext (congrArg (fun k : Fin 280 => k.val) h)

theorem complexBatchReg_off (j : Fin 280) (hj : 277 ≤ j.val) : ∀ i, complexBatchReg i ≠ j := by
  intro i he
  have hv := congrArg Fin.val he
  have hi := i.isLt
  change i.val = j.val at hv
  omega

def complexBatchInputBank (M : Stacks 276 A) (B L : ℕ) : Stacks 280 A :=
  {extendStacks (by decide : 276 ≤ 280) M with R :=
    (Function.update (extendStacks (by decide : 276 ≤ 280) M).R 277 (binSyms B L))}

/-- Retain the generated row headers for subsequent normalization. -/
noncomputable def packedKeyComplexBatch (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P 280 Q A U :=
  .seq (preparePackedCoreRows 277 119 278 279 270 271 272)
    (.seq (embProg complexBatchReg id (packedKeyComplexRealBatch hR hQ))
      (packedComplexBatchFinish 276 264 251 279 269 253 270 271 272))

theorem packedKeyComplexBatch_exec
    (hbody : ∀ f, body' f = embProg packedBoundaryRecoveryBase id (body f))
    (hbody' : ∀ f, body'' f = embProg packedHaloBatchReg id (body' f))
    (hbody'' : ∀ f, bodyLarge f = embProg packedHaloPublishedReg id (body'' f))
    (bodyProtected : P → Pr P 276 Q A U)
    (hbodyProtected : ∀ f, bodyProtected f = embProg packedKeySolverReg id (bodyLarge f))
    (bodyComplex : P → Pr P 277 Q A U)
    (hbodyComplex : ∀ f, bodyComplex f = embProg packedKeyComplexReg id (bodyProtected f))
    (bodyFinal : P → Pr P 280 Q A U)
    (hbodyFinal : ∀ f, bodyFinal f = embProg complexBatchReg id (bodyComplex f))
    (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {p l s t u boundaryTarget target finalTarget rhsExp a b V : ℕ} [NeZero s] {α gap : ℝ}
    (Bcore : ℕ) (hsCore : s < 2^Bcore)
    (q W : ℕ) (hpq : p+1 ≤ q) (hW : 2*q+8 ≤ W)
    (hqSizing : q = executionPrecision p l target rhsExp)
    (Fs : List (ZMod s → GaussianInt)) (hF : ∀ F ∈ Fs, ∀ i, ‖value p (F i)‖ ≤ 1)
    (y : (ZMod s → GaussianInt) → ZMod s → ℝ) (C : ZMod s → GaussianInt)
    (tail : List (Fin (A+4))) (v : HS 280 Q A U)
    (M : Stacks 276 A) (B : Stacks 263 A) (S₀ : Stacks 249 A) (S : Stacks 242 A)
    (hviews : PackedKeyBankViews M B S₀ S)
    (hsetup : PackedHaloSetup (p := p) (l := l) (t := t) (u := u) (target := finalTarget)
      (rhsExp := rhsExp) (a := a) (b := b) (V := V) α gap C S)
    (hq : (M.R 119).length = q) (hpHeader : (M.R 266).length = p)
    (hcommon : (M.R 265).length = W) (hreplicas : (M.R 264).length = Fs.length)
    (hpacket : (M.R 267).length = (b-a)*W)
    (hsource : M.R 263 = cstream A W (Fs.map (packedInterval a (b-a))).flatten++tail)
    (hblank : ∀ i ∈ ([110,268,269,270,271,272,273,274,275] : List (Fin 276)), M.R i = [])
    (hcountBlank : M.R 251 = []) (hcounterBlank : S₀.R 248 = [])
    (hscratch : ∀ i ∈ ([125,127,128,129,130,131,133,134,135,136,138,139,140,143,153,158,166,167] : List (Fin 242)), S.R i = [])
    (hcell : target = boundaryHaloTarget p u boundaryTarget rhsExp
      (haloBoundary s t (PhaseCellBand.width p u) a b).card)
    (hboundary : boundaryTarget = boundaryRecoveryTarget p finalTarget)
    (coreWidth k radius : ℕ) (haEq : a = coreStart coreWidth k-radius)
    (hbEq : b = coreStart coreWidth k+coreLength s coreWidth k+radius)
    (hleft : radius ≤ coreStart coreWidth k)
    (hright : coreStart coreWidth k+coreLength s coreWidth k+radius ≤ s)
    (h249 : B.R 249 = []) (h250 : B.R 250 = [])
    (hpublicationClean : ∀ i ∈ ([254,255,256,257,258,259,260,261,262] : List (Fin 263)), B.R i = [])
    (hradiusWord : B.R 252 = binSyms V radius)
    (hy : ∀ F ∈ complexComponentFields Fs, SchurDominance.Solves (realMatrix s t p u) (haloVertices s a b) (y F)
      (fun i => (value q ((2 : GaussianInt)^(q-p-1)*F i)).re))
    (hcoeff : ∀ j < b-a, ∀ z ∈ couplingCoefficientWords (2^15*p) q s t u (PhaseCellBand.width p u) (a+j),
      Fits (2*q+8) z ∧ z.im = 0) :
    let L := coreLength s coreWidth k
    let Zs := Fs.map (componentSolution y)
    ∃ v' H n, ∃ Gs : List (ZMod s → GaussianInt), v'.user = v.user ∧
      Gs.length = Fs.length ∧
      n ≤ preparePackedCoreRowsCost Bcore q L+
        (Fs.length*(26*((b-a)*W)+17)+34+
          ((packedKeyInputCost p q W (2*Fs.length) (b-a)+(4*(2*Fs.length)+4))+
          packedHaloBatchCostFromSetup p u l s t a b V boundaryTarget finalTarget rhsExp coreWidth k radius (2*Fs.length)))+
        (Fs.length*(16*(L*(2*q+8))+19)+22) ∧
      Exec bodyFinal (packedKeyComplexBatch hR hQ)
        (mk v (complexBatchInputBank M Bcore L)) n (mk v' H) ∧
      H.R 253 = (Gs.map (fun D => cstream A (2*q+8) (ownedCoreWords coreWidth k D))).flatten++M.R 253 ∧
      H.R 264 = M.R 264 ∧ H.R 251 = [] ∧ H.R 276 = [] ∧ H.R 278 = List.replicate L tick ∧ H.R 279 = List.replicate (L*(2*q+8)) tick ∧
      H.R 277 = binSyms Bcore L ∧
      (∀ j : Fin 276, 265 ≤ j.val → H.R (Fin.castLE (by decide : 276 ≤ 280) j) = M.R j) ∧
      (∀ z ∈ Zs, ∀ i ∈ ownedCore s coreWidth k, ‖z i‖ ≤ 4*(2 : ℝ)^(p+8)) ∧
      List.Forall₂ (fun z D => PhaseCellInterface.ErrorOn (ownedCore s coreWidth k)
        (packedIntervalRead q (2*q+8) (coreStart coreWidth k)
          (cstream A (2*q+8) (ownedCoreWords coreWidth k D)++M.R 253)) z
        (1/(2 : ℝ)^finalTarget+1/(2 : ℝ)^finalTarget)) Zs Gs ∧
      ∀ c, mnProgPush (packedKeyComplexBatch (P := P) (U := U) (A := A) hR hQ) ≤ c →
        (∀ f, mnProgPush (bodyFinal f) ≤ c) → ∀ depth,
        ExecWithin bodyFinal (fun d z => mnSize z+d ≤ mnSize (mk v (complexBatchInputBank M Bcore L))+
          ((2*Fs.length)*((b-a)*(2*q+8))+V)+depth+(c+1)*
            (preparePackedCoreRowsCost Bcore q L+
              ((Fs.length*(26*((b-a)*W)+17)+34)+
                ((packedKeyInputCost p q W (2*Fs.length) (b-a)+(4*(2*Fs.length)+4))+
                  packedHaloGeometryWorkspace p u l s t a b V boundaryTarget finalTarget rhsExp coreWidth k radius (2*Fs.length)))+
              (Fs.length*(16*(L*(2*q+8))+19)+22)))
          depth (packedKeyComplexBatch hR hQ) (mk v (complexBatchInputBank M Bcore L)) n (mk v' H) := by
  dsimp only
  let L := coreLength s coreWidth k
  let S₀big := complexBatchInputBank M Bcore L
  have hL : L < 2^Bcore :=
    (show L ≤ s from (min_le_right coreWidth (s-coreStart coreWidth k)).trans (Nat.sub_le s _)).trans_lt hsCore
  obtain ⟨v₀,n₀,hu₀,hn₀,he₀⟩ := preparePackedCoreRows_exec (body := bodyFinal)
    (coreWord := 277) (precision := 119) (rows := 278) (rowWidth := 279)
    (work := 270) (saved := 271) (tmp := 272) (by decide) Bcore q L hL v S₀big
    (by simp [S₀big,complexBatchInputBank])
    (by simpa [S₀big,complexBatchInputBank,extendStacks] using hq)
    (by intro i hi; simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
        rcases hi with rfl | rfl | rfl | rfl | rfl
        · simp [S₀big,complexBatchInputBank,extendStacks]
        · simp [S₀big,complexBatchInputBank,extendStacks]
        · simpa [S₀big,complexBatchInputBank,extendStacks] using hblank 270 (by simp)
        · simpa [S₀big,complexBatchInputBank,extendStacks] using hblank 271 (by simp)
        · simpa [S₀big,complexBatchInputBank,extendStacks] using hblank 272 (by simp))
  let S₁ : Stacks 280 A := {S₀big with R := (Function.update (Function.update S₀big.R 278
    (List.replicate L tick)) 279 (List.replicate (L*(2*q+8)) tick))}
  have hview₁ : embStk complexBatchReg S₁ = extendStacks (by decide : 276 ≤ 277) M := by
    refine Stacks.ext rfl rfl ?_ ?_
    · funext i; simp [embStk,complexBatchReg,S₁,S₀big,complexBatchInputBank,extendStacks]
    · funext i
      have hi := i.isLt
      have h277 : complexBatchReg i ≠ (277 : Fin 280) := complexBatchReg_off 277 (by decide) i
      have h278 : complexBatchReg i ≠ (278 : Fin 280) := complexBatchReg_off 278 (by decide) i
      have h279 : complexBatchReg i ≠ (279 : Fin 280) := complexBatchReg_off 279 (by decide) i
      change (Function.update (Function.update (Function.update
        (extendStacks (by decide : 276 ≤ 280) M).R 277 (binSyms Bcore L))
        278 (List.replicate L tick)) 279 (List.replicate (L*(2*q+8)) tick)) (complexBatchReg i) = _
      simp only [Function.update_apply,h279,h278,h277,ite_false]
      simp [complexBatchReg,extendStacks]
  obtain ⟨v₁,H₁,G,n₁,Ds,hu₁,hn₁,he₁,hproj,hholdL,hholdR,hqueue,hsrc,h132,h220,h248,h252,
    h251,hfactors,houtput,hDs,hgood,hframe,hcomplexRealStock⟩ := packedKeyComplexRealBatch_exec
    hbody hbody' hbody'' bodyProtected hbodyProtected bodyComplex hbodyComplex hR hQ hA
    q W hpq hW hqSizing Fs hF y C tail (embDn complexBatchReg v₀) M B S₀ S hviews hsetup
    hq hpHeader hcommon hreplicas hpacket hsource hblank hcountBlank hcounterBlank hscratch hcell hboundary
    coreWidth k radius haEq hbEq hleft hright h249 h250 hpublicationClean hradiusWord hy hcoeff
  obtain ⟨v₂,S₂,he₂,hv₂,hu₂,hproj₂,hoff⟩ := exec_emb complexBatchReg_injective hbodyFinal he₁
    v₀ rfl S₁ hview₁
  have hread (i : Fin 276) : S₂.R (complexBatchReg (packedKeyComplexReg i)) = G.R i := by
    exact (congrArg (fun T : Stacks 277 A => T.R (packedKeyComplexReg i)) hproj₂).trans
      (congrArg (fun T : Stacks 276 A => T.R i) hproj)
  have hhold : S₂.R 276 = List.replicate Fs.length tick :=
    (congrArg (fun T : Stacks 277 A => T.R 276) hproj₂).trans hholdR
  have hwidth : S₂.R 279 = List.replicate (L*(2*q+8)) tick := by
    simpa [S₁] using (hoff 279 (complexBatchReg_off 279 (by decide))).2
  have hrows : S₂.R 278 = List.replicate L tick := by
    simpa [S₁] using (hoff 278 (complexBatchReg_off 278 (by decide))).2
  have hcore : S₂.R 277 = binSyms Bcore L := by
    simpa [S₁,S₀big,complexBatchInputBank] using (hoff 277 (complexBatchReg_off 277 (by decide))).2
  have hrep : S₂.R 264 = List.replicate Fs.length tick++M.R 264 := by
    rw [show S₂.R 264 = G.R 264 from hread 264]
    simpa using (hframe 264 (by decide)).2
  have hblank₂ : ∀ i ∈ ([269,270,271,272] : List (Fin 280)), S₂.R i = [] := by
    intro i hi
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    all_goals first
      | exact (show S₂.R 269 = G.R 269 from hread 269).trans
          ((by simpa using (hframe 269 (by decide)).2 : G.R 269 = M.R 269).trans (hblank 269 (by simp)))
      | exact (show S₂.R 270 = G.R 270 from hread 270).trans
          ((by simpa using (hframe 270 (by decide)).2 : G.R 270 = M.R 270).trans (hblank 270 (by simp)))
      | exact (show S₂.R 271 = G.R 271 from hread 271).trans
          ((by simpa using (hframe 271 (by decide)).2 : G.R 271 = M.R 271).trans (hblank 271 (by simp)))
      | exact (show S₂.R 272 = G.R 272 from hread 272).trans
          ((by simpa using (hframe 272 (by decide)).2 : G.R 272 = M.R 272).trans (hblank 272 (by simp)))
  have houtput₂ : S₂.R 253 = (Ds.map (fun D => cstream A (2*q+8)
      (packedInterval (coreStart coreWidth k) L D))).flatten++M.R 253 := by
    rw [show S₂.R 253 = G.R 253 from hread 253]
    simpa only [ownedCoreWords,packedInterval,L,Function.update_of_ne (by decide : (253 : Fin 276) ≠ 264),
      Function.update_of_ne (by decide : (253 : Fin 276) ≠ 263)] using houtput
  have hc := packedComponentSolutions_certificate q (2*q+8) (q-p-1)
    (coreStart coreWidth k) L (ownedCore s coreWidth k) Fs y Ds (1/(2 : ℝ)^finalTarget) (M.R 253)
    (by simpa only [ownedCoreWords,packedInterval,L,Function.update_of_ne (by decide : (253 : Fin 276) ≠ 264),
      Function.update_of_ne (by decide : (253 : Fin 276) ≠ 263)] using hgood)
  have hcoreFit : coreStart coreWidth k+L ≤ s := by
    dsimp only [L]; omega
  have hactive : ∀ i ∈ ownedCore s coreWidth k,
      coreStart coreWidth k ≤ i.val ∧ i.val < coreStart coreWidth k+L := by
    intro i hi
    exact (mem_haloVertices _ _ i).mp hi
  obtain ⟨hlen,v₃,n₃,hu₃,hn₃,he₃,haccuracy⟩ := packedComplexBatchFinish_exec (body := bodyFinal)
    (hold := 276) (replicas := 264) (nativeCount := 251) (width := 279)
    (count := 269) (src := 253) (buf := 270) (saved := 271) (tmp := 272)
    (by decide) (by omega) q (2*q+8) (coreStart coreWidth k) L (ownedCore s coreWidth k)
    hcoreFit hactive (Fs.map (componentSolution y)) Ds (1/(2 : ℝ)^finalTarget)
    (M.R 253) (M.R 253) (M.R 264) hc v₂ S₂
    (by simp [hhold]) (by simp [hwidth]) (by simpa only [List.length_map] using hrep)
    (by rw [show S₂.R 251 = G.R 251 from hread 251,h251]; simp) houtput₂
    (hblank₂ 269 (by simp)) (hblank₂ 270 (by simp)) (hblank₂ 271 (by simp)) (hblank₂ 272 (by simp))
  let Gs := pairedComponentFields (Ds.take Fs.length) (Ds.drop Fs.length)
  let S₃ : Stacks 280 A := {S₂ with R := (Function.update (Function.update (Function.update
    (Function.update S₂.R 253 ((Gs.map (fun D => cstream A (2*q+8)
      (packedInterval (coreStart coreWidth k) L D))).flatten++M.R 253)) 264 (M.R 264)) 251 []) 276 [])}
  have he₃' : Exec bodyFinal (packedComplexBatchFinish 276 264 251 279 269 253 270 271 272)
      (mk v₂ S₂) n₃ (mk v₃ S₃) := by simpa only [List.length_map] using he₃
  refine ⟨v₃,S₃,n₀+n₁+n₃,Gs,
    hu₃.trans (hu₂.trans (hu₁.trans hu₀)),?_,?_,
    (Exec.seq he₀ (Exec.seq he₂ he₃')).cast (by omega) rfl,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [List.length_map] using hlen
  · simp only [complexComponentFields_length] at hn₁
    simp only [List.length_map] at hn₃
    dsimp only [L] at hn₀ hn₃ ⊢
    omega
  · simp [S₃,ownedCoreWords,packedInterval,L]
  · simp [S₃]
  · simp [S₃]
  · simp [S₃]
  · simp [S₃,hrows,L]
  · simp [S₃,hwidth,L]
  · simpa [S₃] using hcore
  · intro j hj
    have hj263 : j ≠ 263 := by intro he; have := congrArg Fin.val he; change j.val = 263 at this; omega
    have hj264 : j ≠ 264 := by intro he; have := congrArg Fin.val he; change j.val = 264 at this; omega
    have hraw : S₂.R (Fin.castLE (by decide : 276 ≤ 280) j) = M.R j :=
      (hread j).trans (by simpa [hj263,hj264] using (hframe j (by omega)).2)
    have hne (i : Fin 280) (hi : i.val < 265 ∨ 276 ≤ i.val) :
        (Fin.castLE (by decide : 276 ≤ 280) j) ≠ i := by
      intro he
      have hv := congrArg Fin.val he
      change j.val = i.val at hv
      have := j.isLt
      omega
    simpa [S₃,Function.update_apply,hne 253 (by decide),hne 264 (by decide),
      hne 251 (by decide),hne 276 (by decide)] using hraw
  · intro z hz i hi
    obtain ⟨F,hmem,rfl⟩ := List.mem_map.mp hz
    apply componentSolution_round_magnitude
    have hdom := SchurDominance.dominates_mono (realMatrix s t p u) Finset.univ
      (haloVertices s a b) (1/(8*(p : ℝ))) (Finset.subset_univ _) hsetup.hdom
    apply componentSolution_stable_bound p q (by have := hsetup.hp; omega) hpq
      (realMatrix s t p u) (haloVertices s a b) hdom Fs hF y hy F hmem i
    apply (mem_haloVertices _ _ i).mpr
    have hi' := hactive i hi
    dsimp only [L] at hi'
    constructor <;> omega
  · simpa only [List.length_map,ownedCoreWords,packedInterval,L] using haccuracy
  · intro c hpLarge hbLarge depth
    have hpParts := hpLarge
    simp only [packedKeyComplexBatch,mnProgPush,embProg_push] at hpParts
    have hpSetup := Nat.le_trans (Nat.le_max_left _ _) hpParts
    have hpInner := Nat.le_trans (Nat.le_max_left _ _) (Nat.le_trans (Nat.le_max_right _ _) hpParts)
    have hpFinish := Nat.le_trans (Nat.le_max_right _ _) (Nat.le_trans (Nat.le_max_right _ _) hpParts)
    have hbSmall : ∀ f, mnProgPush (bodyComplex f) ≤ c := by
      intro f
      simpa only [hbodyFinal f,embProg_push] using hbLarge f
    have ht := hcomplexRealStock c hpInner hbSmall depth
    let persistent := (complexComponentFields Fs).length*((b-a)*(2*q+8))+V
    let work := (Fs.length*(26*((b-a)*W)+17)+34)+
      ((packedKeyInputCost p q W (complexComponentFields Fs).length (b-a)+(4*(complexComponentFields Fs).length+4))+
        packedHaloGeometryWorkspace p u l s t a b V boundaryTarget finalTarget rhsExp coreWidth k radius (complexComponentFields Fs).length)
    have htSmall : ExecWithin bodyComplex (fun d z => mnSize z+d ≤
        mnSize (mk (embDn complexBatchReg v₀) (extendStacks (by decide : 276 ≤ 277) M))+depth+(persistent+(c+1)*work))
        depth (packedKeyComplexRealBatch hR hQ)
        (mk (embDn complexBatchReg v₀) (extendStacks (by decide : 276 ≤ 277) M)) n₁ (mk v₁ H₁) :=
      ht.mono (by intro d z hz; dsimp only [persistent,work]; omega)
    obtain ⟨v',F',hv',hu',ht',hproj',hframe'⟩ := exec_emb_within_stock complexBatchReg
      complexBatchReg_injective hbodyFinal htSmall v₀ rfl S₁ hview₁
    have hout := (ht'.toExec.unique he₂).2
    rw [hout] at ht'
    have htLarge : ExecWithin bodyFinal (fun d z => mnSize z+d ≤
        mnSize (mk v₀ S₁)+persistent+depth+(c+1)*work)
        depth (embProg complexBatchReg id (packedKeyComplexRealBatch hR hQ))
        (mk v₀ S₁) n₁ (mk v₂ S₂) := ht'.mono (by intro d z hz; omega)
    have htFinish := mn_release_exec_within_stock htLarge he₃' hn₃ hpFinish hbLarge
    have htSetup := mn_setup_exec_within_stock he₀ hn₀ hpSetup hbLarge htFinish
    simpa only [packedKeyComplexBatch,persistent,work,complexComponentFields_length,List.length_map,Nat.add_assoc,L] using htSetup

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
