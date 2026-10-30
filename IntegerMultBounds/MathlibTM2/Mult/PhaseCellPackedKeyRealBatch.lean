module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedHaloBatchFromSetup
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedKeyFieldsInput

/-! Execute local input conversion, factor reuse and real core publication. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.BandFactor
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {P U : Type}
variable {body : P → Pr P 242 Q A U} {body' : P → Pr P 248 Q A U}
  {body'' : P → Pr P 249 Q A U} {bodyLarge : P → Pr P 263 Q A U}

noncomputable def packedKeyRealBatch (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P 276 Q A U :=
  .seq packedKeyInputCounted (embProg packedKeySolverReg id (packedHaloGeometryPublishedBatch hR hQ))

theorem packedKeyRealBatch_exec
    (hbody : ∀ f, body' f = embProg packedBoundaryRecoveryBase id (body f))
    (hbody' : ∀ f, body'' f = embProg packedHaloBatchReg id (body' f))
    (hbody'' : ∀ f, bodyLarge f = embProg packedHaloPublishedReg id (body'' f))
    (bodyProtected : P → Pr P 276 Q A U)
    (hbodyProtected : ∀ f, bodyProtected f = embProg packedKeySolverReg id (bodyLarge f))
    (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {p l s t u boundaryTarget target finalTarget rhsExp a b V : ℕ} [NeZero s] {α gap : ℝ}
    (q W : ℕ) (hpq : p+1 ≤ q) (hW : 2*q+8 ≤ W)
    (hqSizing : q = executionPrecision p l target rhsExp)
    (Fs : List (ZMod s → GaussianInt)) (hF : ∀ F ∈ Fs, ∀ i, ‖value p (F i)‖ ≤ 1)
    (y : (ZMod s → GaussianInt) → ZMod s → ℝ) (C : ZMod s → GaussianInt)
    (tail : List (Fin (A+4))) (v : HS 276 Q A U)
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
    (hy : ∀ F ∈ Fs, SchurDominance.Solves (realMatrix s t p u) (haloVertices s a b) (y F)
      (fun i => (value q ((2 : GaussianInt)^(q-p-1)*F i)).re))
    (hcoeff : ∀ j < b-a, ∀ z ∈ couplingCoefficientWords (2^15*p) q s t u (PhaseCellBand.width p u) (a+j),
      Fits (2*q+8) z ∧ z.im = 0) :
    let inputs := Fs.map (fun F => ((fun i => (2 : GaussianInt)^(q-p-1)*F i),y F))
    ∃ v' G n, ∃ Ds : List (ZMod s → GaussianInt), v'.user = v.user ∧
      n ≤ (packedKeyInputCost p q W Fs.length (b-a)+(4*Fs.length+4))+
        packedHaloBatchCostFromSetup p u l s t a b V boundaryTarget finalTarget rhsExp coreWidth k radius Fs.length ∧
      Exec bodyProtected (packedKeyRealBatch hR hQ) (mk v M) n (mk v' G) ∧
      G.inp = M.inp ∧ G.out = M.out ∧
      G.R 263 = tail ∧ G.R 110 = [] ∧
      G.R 132 = S.R 132 ∧ G.R 220 = S.R 220 ∧ G.R 248 = [] ∧ G.R 252 = [] ∧
      G.R 251 = List.replicate Fs.length tick ∧
      (∀ i ∈ packedFactorOwnedRegs, G.R (Fin.castLE (by decide : 248 ≤ 276) i) = []) ∧
      G.R 253 = (Ds.map (fun D => cstream A (2*q+8) (ownedCoreWords coreWidth k D))).flatten++M.R 253 ∧
      Ds.length = Fs.length ∧
      List.Forall₂ (fun x D => PhaseCellInterface.ErrorOn (ownedCore s coreWidth k)
        (fun i => (packedIntervalRead q (2*q+8) (coreStart coreWidth k)
          (cstream A (2*q+8) (ownedCoreWords coreWidth k D)++M.R 253) i).re)
        x.2 (1/(2 : ℝ)^finalTarget)) inputs Ds ∧
      (∀ j : Fin 276, 263 ≤ j.val → G.L j = M.L j ∧
        G.R j = if j = 263 then tail else M.R j) ∧
      ∀ c, mnProgPush (packedKeyRealBatch (P := P) (U := U) (A := A) hR hQ) ≤ c →
        (∀ f, mnProgPush (bodyProtected f) ≤ c) → ∀ depth,
        ExecWithin bodyProtected (fun d z => mnSize z+d ≤ mnSize (mk v M)+
          (Fs.length*((b-a)*(2*q+8))+V)+depth+(c+1)*
            ((packedKeyInputCost p q W Fs.length (b-a)+(4*Fs.length+4))+
              packedHaloGeometryWorkspace p u l s t a b V boundaryTarget finalTarget rhsExp coreWidth k radius Fs.length))
          depth (packedKeyRealBatch hR hQ) (mk v M) n (mk v' G) := by
  dsimp only
  let inputs := Fs.map (fun F => ((fun i => (2 : GaussianInt)^(q-p-1)*F i),y F))
  let rhs := (Fs.map (fun F => cstream A (2*q+8)
    (packedInterval a (b-a) (fun i => (2 : GaussianInt)^(q-p-1)*F i)))).flatten
  let M₁ : Stacks 276 A := {M with R := (Function.update
    (Function.update (Function.update M.R 263 tail) 110 rhs) 251 (List.replicate Fs.length tick))}
  let B₁ : Stacks 263 A := {B with R := (Function.update (Function.update B.R 110 rhs) 251 (List.replicate Fs.length tick))}
  let T₁ : Stacks 249 A := {S₀ with R := Function.update S₀.R 110 rhs}
  let S₁ : Stacks 242 A := {S with R := Function.update S.R 110 rhs}
  have hsetupM : PackedHaloSetup (p := p) (l := l) (t := t) (u := u) (target := finalTarget)
      (rhsExp := rhsExp) (a := a) (b := b) (V := V) α gap C (embStk packedKeySetupReg M) := by
    change PackedHaloSetup α gap C (embStk (Fin.castLE (by decide : 242 ≤ 276)) M)
    rw [hviews.factory_view]
    exact hsetup
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁,hsetupM₁,hbound⟩ := packedKeyFieldsInput_exec (body := bodyProtected)
    q W hpq hW Fs hF tail v M hsetupM hq hpHeader hcommon hreplicas hpacket hsource hblank hcountBlank
  have hviews₁ : PackedKeyBankViews M₁ B₁ T₁ S₁ := hviews.input_update tail rhs (List.replicate Fs.length tick)
  have hsetup₁ : PackedHaloSetup (p := p) (l := l) (t := t) (u := u) (target := finalTarget)
      (rhsExp := rhsExp) (a := a) (b := b) (V := V) α gap C S₁ := by
    change PackedHaloSetup α gap C (embStk (Fin.castLE (by decide : 242 ≤ 276)) M₁) at hsetupM₁
    rw [hviews₁.factory_view] at hsetupM₁
    exact hsetupM₁
  have hqs := (boundaryHaloTarget_sizing p u l boundaryTarget rhsExp
    (haloBoundary s t (PhaseCellBand.width p u) a b).card).1
  rw [←hcell] at hqs
  have hqn := hqs.symm.trans hqSizing.symm
  have hwidthSizing : executionWidth p l target rhsExp = 2*q+8 := by
    dsimp [executionWidth]
    have hh := hqSizing
    dsimp [executionPrecision] at hh
    omega
  have hwn : executionWidth p l (initialSchurTarget p u
      (boundaryTableBits p boundaryTarget rhsExp (haloBoundary s t (PhaseCellBand.width p u) a b).card) 2) 2 = 2*q+8 := by
    dsimp [executionWidth]
    have hh := hqn
    dsimp [executionPrecision] at hh
    omega
  obtain ⟨v₂,F,G,n₂,hu₂,hn₂,he₂,hinput,houtputFrame,hproj,hexternal,harchive,hsrc,htable,hcounter,hwidthClear,hfactors,hframe,Ds,houtput,hDs,hgood,hprotectedStock⟩ :=
    packedHaloBatch_from_setup_exec hbody hbody' hbody'' bodyProtected hbodyProtected hR hQ hA
      inputs C [] v₁ M₁ B₁ T₁ S₁ hviews₁
      (by simpa [T₁] using hcounterBlank) hsetup₁
      (by simp [S₁,rhs,inputs,hwidthSizing,List.map_map,Function.comp_def])
      (by
        intro i hi
        have hne : i ≠ (110 : Fin 242) := by
          intro he
          exact (show (110 : Fin 242) ∉ [125,127,128,129,130,131,133,134,135,136,138,139,140,143,153,158,166,167] by decide) (he ▸ hi)
        simpa [S₁,hne] using hscratch i hi)
      (by
        intro x hx i
        obtain ⟨F,hFmem,rfl⟩ := List.mem_map.mp hx
        rw [←hqSizing]
        exact hbound F hFmem i)
      hcell hboundary coreWidth k radius haEq hbEq hleft hright
      (by simpa [B₁] using h249) (by simpa [B₁] using h250)
      (by simp [B₁,inputs])
      (by
        intro i hi
        have hne : i ≠ (110 : Fin 263) ∧ i ≠ 251 := by
          constructor
          · intro he; exact (show (110 : Fin 263) ∉ [254,255,256,257,258,259,260,261,262] by decide) (he ▸ hi)
          · intro he; exact (show (251 : Fin 263) ∉ [254,255,256,257,258,259,260,261,262] by decide) (he ▸ hi)
        simpa [B₁,hne.1,hne.2] using hpublicationClean i hi)
      (by simpa [B₁] using hradiusWord)
      (by
        intro x hx
        obtain ⟨F,hFmem,rfl⟩ := List.mem_map.mp hx
        simpa only [hqn] using hy F hFmem)
      (by simpa only [hwn,hqn] using hcoeff)
  have h110 : G.R 110 = F.R 110 := congrArg (fun T : Stacks 263 A => T.R 110) hproj
  have hqueue := (hexternal 263 (by decide)).2
  have hread (i : Fin 263) : G.R (packedKeySolverReg i) = F.R i :=
    congrArg (fun T : Stacks 263 A => T.R i) hproj
  have h251 : G.R 251 = List.replicate Fs.length tick := by
    rw [show (251 : Fin 276) = packedKeySolverReg 251 by rfl,hread,
      hframe 251 (by decide) (by decide) (by decide)]
    simp [B₁]
  have houtput' := houtput
  simp only [hwn,hqn] at houtput' hgood
  refine ⟨v₂,G,n₁+n₂,Ds,hu₂.trans hu₁,?_,Exec.seq he₁ he₂,hinput,houtputFrame,?_,h110.trans hsrc,?_,?_,?_,?_,h251,?_,?_,?_,?_,?_,?_⟩
  · simpa only [inputs,List.length_map] using Nat.add_le_add hn₁ hn₂
  · simpa [M₁] using hqueue
  · exact (hread 132).trans (by simpa [S₁] using harchive)
  · exact (hread 220).trans (by simpa [S₁] using htable)
  · exact (hread 248).trans hcounter
  · exact (hread 252).trans hwidthClear
  · intro i hi
    exact (hread (Fin.castLE (by decide : 248 ≤ 263) i)).trans (hfactors i hi)
  · simpa [M₁] using houtput' 
  · simpa [inputs] using hDs
  · simpa only [M₁,Function.update_of_ne (by decide : (253 : Fin 276) ≠ 251),
      Function.update_of_ne (by decide : (253 : Fin 276) ≠ 110),
      Function.update_of_ne (by decide : (253 : Fin 276) ≠ 263)] using hgood
  · intro j hj
    have h110 : j ≠ (110 : Fin 276) := by intro he; have hv := congrArg Fin.val he; omega
    have h251 : j ≠ (251 : Fin 276) := by intro he; have hv := congrArg Fin.val he; omega
    simpa [M₁,h110,h251,Function.update_apply] using hexternal j hj

  · intro c hpLarge hbLarge depth
    have hpParts := hpLarge
    simp only [packedKeyRealBatch,mnProgPush] at hpParts
    have ht := hprotectedStock c (Nat.le_trans (Nat.le_max_right _ _) hpParts) hbLarge depth
    have ht' := mn_setup_exec_within_stock he₁ hn₁
      (Nat.le_trans (Nat.le_max_left _ _) hpParts) hbLarge ht
    simpa only [packedKeyRealBatch,inputs,List.length_map,hwn] using ht'

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
