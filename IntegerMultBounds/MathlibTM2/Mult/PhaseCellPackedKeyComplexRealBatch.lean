module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedKeyRealBatch
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedComponentSolutions
public import IntegerMultBounds.MathlibTM2.Host.ExtendStacks
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellExpandComplexStock

/-! Execute component expansion and the actual shared-factor packed numerical batch. -/
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

def packedKeyComplexReg : Fin 276 → Fin 277 := Fin.castLE (by decide)

theorem packedKeyComplexReg_injective : Function.Injective packedKeyComplexReg := by
  intro i j he
  exact Fin.ext (congrArg (fun k : Fin 277 => k.val) he)

theorem packedKeyComplexReg_off : ∀ i, packedKeyComplexReg i ≠ (276 : Fin 277) := by
  intro i he
  have hh := congrArg Fin.val he
  have hi := i.isLt
  change i.val = 276 at hh
  omega

noncomputable def packedKeyComplexRealBatch (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P 277 Q A U :=
  .seq (expandComplexKeyCounted 264 267 269 263 270 271 272 276)
    (embProg packedKeyComplexReg id (packedKeyRealBatch hR hQ))

/-- Expansion preserves the solver bank except its input queue and replica
counter. The original count is kept in the fresh register for later pairing. -/
theorem packedKeyComplexExpand_exec (bodyComplex : P → Pr P 277 Q A U)
    (hA : 4 ≤ A) {s : ℕ} (a L W : ℕ) (hfit : a+L ≤ s)
    (Fs : List (ZMod s → GaussianInt)) (tail : List (Fin (A+4)))
    (v : HS 277 Q A U) (M : Stacks 276 A)
    (hreplicas : (M.R 264).length = Fs.length)
    (hwidth : (M.R 267).length = L*W)
    (hsrc : M.R 263 = cstream A W ((Fs.map (packedInterval a L)).flatten)++tail)
    (hblank : ∀ i ∈ ([269,270,271,272] : List (Fin 276)), M.R i = []) :
    let queue := cstream A W (((complexComponentFields Fs).map (packedInterval a L)).flatten)++tail
    let M₁ : Stacks 276 A := {M with R := (Function.update (Function.update M.R 263 queue)
      264 (List.replicate Fs.length tick++M.R 264))}
    ∃ v' n G, v'.user = v.user ∧ n ≤ Fs.length*(26*(L*W)+17)+34 ∧
      Exec bodyComplex (expandComplexKeyCounted 264 267 269 263 270 271 272 276)
        (mk v (extendStacks (by decide : 276 ≤ 277) M)) n (mk v' G) ∧
      (∀ depth, ExecWithin bodyComplex
        (fun d z => mnSize z+d ≤ mnSize (mk v (extendStacks (by decide : 276 ≤ 277) M))+
          depth+2*(Fs.length*(26*(L*W)+17)+34)) depth
        (expandComplexKeyCounted 264 267 269 263 270 271 272 276)
        (mk v (extendStacks (by decide : 276 ≤ 277) M)) n (mk v' G)) ∧
      embStk packedKeyComplexReg G = M₁ ∧
      G.L 276 = [] ∧ G.R 276 = List.replicate Fs.length tick := by
  dsimp only
  let T₀ := extendStacks (by decide : 276 ≤ 277) M
  obtain ⟨v',n,hu,hn,he⟩ := expandComplexFields_exec (body := bodyComplex)
    (replicas := 264) (width := 267) (count := 269) (src := 263)
    (imag := 270) (saved := 271) (tmp := 272) (hold := 276)
    (by decide) hA a L W hfit Fs tail v T₀
    (by simpa [T₀,extendStacks] using hreplicas)
    (by simpa [T₀,extendStacks] using hwidth)
    (by simpa [T₀,extendStacks] using hsrc)
    (by simpa [T₀,extendStacks] using hblank 269 (by simp))
    (by simpa [T₀,extendStacks] using hblank 270 (by simp))
    (by simpa [T₀,extendStacks] using hblank 271 (by simp))
    (by simpa [T₀,extendStacks] using hblank 272 (by simp))
    (by simp [T₀,extendStacks])
  refine ⟨v',n,_,hu,hn,he,?_,?_,?_,?_⟩
  · intro depth
    exact expandComplexKeyCounted_within_stock he hn depth
  · refine Stacks.ext rfl rfl ?_ ?_
    · funext i
      simp [embStk,packedKeyComplexReg,T₀,extendStacks,i.isLt]
    · funext i
      have hoff : packedKeyComplexReg i ≠ (276 : Fin 277) := packedKeyComplexReg_off i
      have heq (j : Fin 276) : packedKeyComplexReg i = packedKeyComplexReg j ↔ i = j :=
        packedKeyComplexReg_injective.eq_iff
      change (Function.update (Function.update (Function.update T₀.R 276 _)
        (packedKeyComplexReg 263) _) (packedKeyComplexReg 264) _) (packedKeyComplexReg i) = _
      simp only [Function.update_apply,heq,hoff,ite_false]
      simp [T₀,extendStacks,packedKeyComplexReg,i.isLt]
  · simp [T₀,extendStacks]
  · simp

theorem packedKeyComplexRealBatch_exec
    (hbody : ∀ f, body' f = embProg packedBoundaryRecoveryBase id (body f))
    (hbody' : ∀ f, body'' f = embProg packedHaloBatchReg id (body' f))
    (hbody'' : ∀ f, bodyLarge f = embProg packedHaloPublishedReg id (body'' f))
    (bodyProtected : P → Pr P 276 Q A U)
    (hbodyProtected : ∀ f, bodyProtected f = embProg packedKeySolverReg id (bodyLarge f))
    (bodyComplex : P → Pr P 277 Q A U)
    (hbodyComplex : ∀ f, bodyComplex f = embProg packedKeyComplexReg id (bodyProtected f))
    (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {p l s t u boundaryTarget target finalTarget rhsExp a b V : ℕ} [NeZero s] {α gap : ℝ}
    (q W : ℕ) (hpq : p+1 ≤ q) (hW : 2*q+8 ≤ W)
    (hqSizing : q = executionPrecision p l target rhsExp)
    (Fs : List (ZMod s → GaussianInt)) (hF : ∀ F ∈ Fs, ∀ i, ‖value p (F i)‖ ≤ 1)
    (y : (ZMod s → GaussianInt) → ZMod s → ℝ) (C : ZMod s → GaussianInt)
    (tail : List (Fin (A+4))) (v : HS 277 Q A U)
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
    let queue := cstream A W (((complexComponentFields Fs).map (packedInterval a (b-a))).flatten)++tail
    let M₁ : Stacks 276 A := {M with R := (Function.update (Function.update M.R 263 queue)
      264 (List.replicate Fs.length tick++M.R 264))}
    let inputs := (complexComponentFields Fs).map (fun F => ((fun i => (2 : GaussianInt)^(q-p-1)*F i),y F))
    ∃ v' H G n, ∃ Ds : List (ZMod s → GaussianInt), v'.user = v.user ∧
      n ≤ Fs.length*(26*((b-a)*W)+17)+34+
        ((packedKeyInputCost p q W (complexComponentFields Fs).length (b-a)+(4*(complexComponentFields Fs).length+4))+
        packedHaloBatchCostFromSetup p u l s t a b V boundaryTarget finalTarget rhsExp coreWidth k radius (complexComponentFields Fs).length) ∧
      Exec bodyComplex (packedKeyComplexRealBatch hR hQ)
        (mk v (extendStacks (by decide : 276 ≤ 277) M)) n (mk v' H) ∧
      embStk packedKeyComplexReg H = G ∧
      H.L 276 = [] ∧ H.R 276 = List.replicate Fs.length tick ∧
      G.R 263 = tail ∧ G.R 110 = [] ∧
      G.R 132 = S.R 132 ∧ G.R 220 = S.R 220 ∧ G.R 248 = [] ∧ G.R 252 = [] ∧
      G.R 251 = List.replicate (complexComponentFields Fs).length tick ∧
      (∀ i ∈ packedFactorOwnedRegs, G.R (Fin.castLE (by decide : 248 ≤ 276) i) = []) ∧
      G.R 253 = (Ds.map (fun D => cstream A (2*q+8) (ownedCoreWords coreWidth k D))).flatten++M₁.R 253 ∧
      Ds.length = (complexComponentFields Fs).length ∧
      List.Forall₂ (fun x D => PhaseCellInterface.ErrorOn (ownedCore s coreWidth k)
        (fun i => (packedIntervalRead q (2*q+8) (coreStart coreWidth k)
          (cstream A (2*q+8) (ownedCoreWords coreWidth k D)++M₁.R 253) i).re)
        x.2 (1/(2 : ℝ)^finalTarget)) inputs Ds ∧
      (∀ j : Fin 276, 263 ≤ j.val → G.L j = M₁.L j ∧
        G.R j = if j = 263 then tail else M₁.R j) ∧
      ∀ c, mnProgPush (packedKeyComplexRealBatch (P := P) (U := U) (A := A) hR hQ) ≤ c →
        (∀ f, mnProgPush (bodyComplex f) ≤ c) → ∀ depth,
        ExecWithin bodyComplex (fun d z => mnSize z+d ≤
          mnSize (mk v (extendStacks (by decide : 276 ≤ 277) M))+
          ((complexComponentFields Fs).length*((b-a)*(2*q+8))+V)+depth+(c+1)*
            ((Fs.length*(26*((b-a)*W)+17)+34)+
              ((packedKeyInputCost p q W (complexComponentFields Fs).length (b-a)+(4*(complexComponentFields Fs).length+4))+
                packedHaloGeometryWorkspace p u l s t a b V boundaryTarget finalTarget rhsExp coreWidth k radius (complexComponentFields Fs).length)))
          depth (packedKeyComplexRealBatch hR hQ)
          (mk v (extendStacks (by decide : 276 ≤ 277) M)) n (mk v' H) := by
  dsimp only
  let queue := cstream A W (((complexComponentFields Fs).map (packedInterval a (b-a))).flatten)++tail
  let M₁ : Stacks 276 A := {M with R := (Function.update (Function.update M.R 263 queue)
    264 (List.replicate Fs.length tick++M.R 264))}
  have hfit : a+(b-a) ≤ s := by have := hsetup.hab; have := hsetup.hbs; omega
  obtain ⟨v₁,n₁,H₁,hu₁,hn₁,he₁,hstock₁,hview₁,hL₁,hR₁⟩ := packedKeyComplexExpand_exec
    bodyComplex (by omega) a (b-a) W hfit Fs tail v M hreplicas hpacket hsource
    (by intro i hi; exact hblank i (by simp only [List.mem_cons] at hi ⊢; tauto))
  have hviews₁ : PackedKeyBankViews M₁ B S₀ S :=
    (hviews.external_update 263 (by decide) queue).external_update 264 (by decide) _
  have hblank₁ : ∀ i ∈ ([110,268,269,270,271,272,273,274,275] : List (Fin 276)), M₁.R i = [] := by
    intro i hi
    have h263 : i ≠ 263 := by intro he; subst i; simp at hi
    have h264 : i ≠ 264 := by intro he; subst i; simp at hi
    simpa [M₁,h263,h264] using hblank i hi
  obtain ⟨v₂,G,n₂,Ds,hu₂,hn₂,he₂,hrest⟩ := packedKeyRealBatch_exec
    hbody hbody' hbody'' bodyProtected hbodyProtected hR hQ hA q W hpq hW hqSizing
    (complexComponentFields Fs) (complexComponentFields_norm_le p Fs hF) y C tail
    (embDn packedKeyComplexReg v₁) M₁ B S₀ S hviews₁ hsetup
    (by simpa [M₁] using hq) (by simpa [M₁] using hpHeader)
    (by simpa [M₁] using hcommon)
    (by simp [M₁,hreplicas,two_mul])
    (by simpa [M₁] using hpacket) (by simp [M₁,queue]) hblank₁
    (by simpa [M₁] using hcountBlank) hcounterBlank hscratch hcell hboundary
    coreWidth k radius haEq hbEq hleft hright h249 h250 hpublicationClean hradiusWord hy hcoeff
  obtain ⟨hsrc,h110,harchive,htable,hcounter,hwidth,hcount,hfactors,houtput,hDs,hgood,hframe,hrealStock⟩ := hrest
  obtain ⟨v₃,H₃,he₃,hv₃,hu₃,hview₃,hoff⟩ := exec_emb
    packedKeyComplexReg_injective hbodyComplex he₂ v₁ rfl H₁ hview₁
  have hhold := hoff 276 packedKeyComplexReg_off
  refine ⟨v₃,H₃,G,n₁+n₂,Ds,hu₃.trans (hu₂.trans hu₁),Nat.add_le_add hn₁ hn₂,
    Exec.seq he₁ he₃,hview₃,hhold.1.trans hL₁,hhold.2.trans hR₁,
    hsrc,h110,harchive,htable,hcounter,hwidth,hcount,hfactors,houtput,hDs,hgood,hframe,?_⟩
  intro c hpLarge hbLarge depth
  have hpParts := hpLarge
  simp only [packedKeyComplexRealBatch,mnProgPush,embProg_push] at hpParts
  have hbSmall : ∀ f, mnProgPush (bodyProtected f) ≤ c := by
    intro f
    simpa only [hbodyComplex f,embProg_push] using hbLarge f
  have ht := hrealStock c (Nat.le_trans (Nat.le_max_right _ _) hpParts) hbSmall depth
  let persistent := (complexComponentFields Fs).length*((b-a)*(2*q+8))+V
  let work := (packedKeyInputCost p q W (complexComponentFields Fs).length (b-a)+(4*(complexComponentFields Fs).length+4))+
    packedHaloGeometryWorkspace p u l s t a b V boundaryTarget finalTarget rhsExp coreWidth k radius (complexComponentFields Fs).length
  have htSmall : ExecWithin bodyProtected (fun d z => mnSize z+d ≤
      mnSize (mk (embDn packedKeyComplexReg v₁) M₁)+depth+(persistent+(c+1)*work))
      depth (packedKeyRealBatch hR hQ) (mk (embDn packedKeyComplexReg v₁) M₁) n₂ (mk v₂ G) :=
    ht.mono (by intro d z hz; dsimp only [persistent,work]; omega)
  obtain ⟨v',H',hv',hu',ht',hproj',hframe'⟩ := exec_emb_within_stock
    packedKeyComplexReg packedKeyComplexReg_injective hbodyComplex htSmall v₁ rfl H₁ hview₁
  have hout := (ht'.toExec.unique he₃).2
  rw [hout] at ht'
  have htLarge : ExecWithin bodyComplex (fun d z => mnSize z+d ≤
      mnSize (mk v₁ H₁)+persistent+depth+(c+1)*work)
      depth (embProg packedKeyComplexReg id (packedKeyRealBatch hR hQ))
      (mk v₁ H₁) n₂ (mk v₃ H₃) :=
    ht'.mono (by intro d z hz; omega)
  simpa only [packedKeyComplexRealBatch,persistent,work] using
    (mn_setup_exec_within_stock he₁ hn₁ (Nat.le_trans (Nat.le_max_left _ _) hpParts) hbLarge htLarge)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
