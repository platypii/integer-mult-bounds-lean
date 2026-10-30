module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedKeyComplexBatch
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellNormalizeNativeBatch
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedComponentLocality

/-! One actual local numerical call, normalization, publication and dimension cleanup. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.BandFactor
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {T Q A : ℕ} {P U : Type}
variable {body : P → Pr P 242 Q A U} {body' : P → Pr P 248 Q A U}
  {body'' : P → Pr P 249 Q A U} {bodyLarge : P → Pr P 263 Q A U}

noncomputable def packedKeyNormalizedBatch (hT : 280 ≤ T) (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q)
    (rg : TblR 25 → Fin T) (ports : Fin 4 → Fin T) (headerSrc : Fin T) : Pr P T Q A U :=
  .seq (embProg (Fin.castLE hT) id (packedKeyComplexBatch hR hQ))
    (.seq (ordinaryNormalizePackedBatch rg ports headerSrc
      (Fin.castLE hT 266) (Fin.castLE hT 265) (Fin.castLE hT 278) (Fin.castLE hT 264)
      (Fin.castLE hT 279) (Fin.castLE hT 269) (Fin.castLE hT 253)
      (Fin.castLE hT 270) (Fin.castLE hT 271) (Fin.castLE hT 272)
      (Fin.castLE hT 273) (Fin.castLE hT 274) (Fin.castLE hT 275))
      (releasePackedCoreRows (Fin.castLE hT 278) (Fin.castLE hT 279)))

theorem packedKeyNormalizedBatch_exec
    (hbody : ∀ f, body' f = embProg packedBoundaryRecoveryBase id (body f))
    (hbody' : ∀ f, body'' f = embProg packedHaloBatchReg id (body' f))
    (hbody'' : ∀ f, bodyLarge f = embProg packedHaloPublishedReg id (body'' f))
    (bodyProtected : P → Pr P 276 Q A U)
    (hbodyProtected : ∀ f, bodyProtected f = embProg packedKeySolverReg id (bodyLarge f))
    (bodyComplex : P → Pr P 277 Q A U)
    (hbodyComplex : ∀ f, bodyComplex f = embProg packedKeyComplexReg id (bodyProtected f))
    (bodyFinal : P → Pr P 280 Q A U)
    (hbodyFinal : ∀ f, bodyFinal f = embProg complexBatchReg id (bodyComplex f))
    (hT : 280 ≤ T) (bodyOuter : P → Pr P T Q A U)
    (hbodyOuter : ∀ f, bodyOuter f = embProg (Fin.castLE hT) id (bodyFinal f))
    (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {p l s t u boundaryTarget target finalTarget rhsExp a b V : ℕ} [NeZero s] {α gap : ℝ}
    (Bcore : ℕ) (hsCore : s < 2^Bcore)
    (q W : ℕ) (hpq : p+1 ≤ q) (hW : 2*q+8 ≤ W)
    (hqSizing : q = executionPrecision p l target rhsExp)
    (Fs : List (ZMod s → GaussianInt)) (hF : ∀ F ∈ Fs, ∀ i, ‖value p (F i)‖ ≤ 1)
    (C : ZMod s → GaussianInt)
    (tail : List (Fin (A+4))) (v : HS T Q A U)
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
    (hcoeff : ∀ j < b-a, ∀ z ∈ couplingCoefficientWords (2^15*p) q s t u (PhaseCellBand.width p u) (a+j),
      Fits (2*q+8) z ∧ z.im = 0) 
    (targetOut : ℕ) (hfinal : finalTarget = targetOut+1) (hrhs : rhsExp = 2)
    (rg : TblR 25 → Fin T) (hrg : Function.Injective rg) (hrgHigh : ∀ r, 280 ≤ (rg r).val)
    (ports : Fin 4 → Fin T) (hports : Function.Injective ports)
    (headerSrc : Fin T) (hheaderHigh : 280 ≤ headerSrc.val)
    (hreg : [headerSrc,Fin.castLE hT 266,Fin.castLE hT 265,Fin.castLE hT 278,
      Fin.castLE hT 264,Fin.castLE hT 279,Fin.castLE hT 269,Fin.castLE hT 253,
      Fin.castLE hT 270,Fin.castLE hT 271,Fin.castLE hT 272,
      ports 0,ports 1,ports 2,ports 3,Fin.castLE hT 273,Fin.castLE hT 274,Fin.castLE hT 275].Nodup)
    (hsepPorts : ∀ i r, rg r ≠ ports i) (hsepHeader : ∀ r, rg r ≠ headerSrc)
    (hportsHigh : ∀ i, 280 ≤ (ports i).val)
    (hvaluesFit : ∀ i : Fin 8, ![p,u,l,targetOut,s,t,a,b] i < 2^Bcore)
    (wl : List (Fin (A+4))) (hwl : wl.length = Bcore)
    (hbandRoom : 64*(p+1)+u < 2^Bcore)
    (hgeometryRoom : 8*(t+1)^2+2*PhaseCellBand.width p u+8 < 2^Bcore)
    (hprecisionRoom : inversePrecisionRoom p l targetOut
      (haloBoundary s t (PhaseCellBand.width p u) a b).card (PhaseCellBand.width p u) < 2^Bcore)
    (headerTail : List (Fin (A+4))) (H₀ : Stacks T A)
    (hview₀ : embStk (Fin.castLE hT) H₀ = complexBatchInputBank M Bcore (coreLength s coreWidth k))
    (hwidth : H₀.R (rg .wr) = wl) (hbankBlank : ∀ r : TblR 25, r ≠ .wr → H₀.R (rg r) = [])
    (hparameters : H₀.R headerSrc = (inverseParameterWords p u l targetOut s t a b).flatMap
      (fun r => binSyms Bcore r.2)++headerTail)
    (hheaders : ∀ i, H₀.R (ports i) = [])
    (localityTarget : ℕ)
    (hhalo : haloVertices s a b = (PhaseCellInterface.generatedWindow s coreWidth p u localityTarget k).halo)
    (Y : (ZMod s → GaussianInt) → ZMod s → ℝ)
    (hY : ∀ F ∈ complexComponentFields Fs, SchurDominance.Solves (realMatrix s t p u) Finset.univ (Y F)
      (fun i => (value q ((2 : GaussianInt)^(q-p-1)*F i)).re)) :
    let L := coreLength s coreWidth k
    let j := inverseNormalizationShift p
    ∃ v' H n, ∃ Gs : List (ZMod s → GaussianInt), v'.user = v.user ∧ Gs.length = Fs.length ∧
      n ≤ (preparePackedCoreRowsCost Bcore q L+
        (Fs.length*(26*((b-a)*W)+17)+34+
          ((packedKeyInputCost p q W (2*Fs.length) (b-a)+(4*(2*Fs.length)+4))+
          packedHaloBatchCostFromSetup p u l s t a b V boundaryTarget finalTarget rhsExp coreWidth k radius (2*Fs.length)))+
        (Fs.length*(16*(L*(2*q+8))+19)+22))+
        (preparedNormalizePackedBatchCost Bcore p u l targetOut s t a b W Fs.length L+214*Bcore+217)+
        (2*L*((2*q+8)+1)+4) ∧
      Exec bodyOuter (packedKeyNormalizedBatch hT hR hQ rg ports headerSrc) (mk v H₀) n (mk v' H) ∧
      H.R (Fin.castLE hT 253) = (Gs.map (fun D => cstream A W (ownedCoreWords coreWidth k D))).flatten++M.R 253 ∧
      H.R headerSrc = headerTail ∧ H.R (Fin.castLE hT 278) = [] ∧ H.R (Fin.castLE hT 279) = [] ∧
      (∀ r, r ≠ TblR.wr → H.R (rg r) = []) ∧ H.R (rg .wr) = wl ∧
      List.Forall₂ (fun F D => PhaseCellInterface.ErrorOn (ownedCore s coreWidth k)
        (packedIntervalRead p W (coreStart coreWidth k)
          (cstream A W (ownedCoreWords coreWidth k D)++M.R 253))
        (fun i => ((2 : ℂ)^j)⁻¹*componentSolution Y F i)
        ((2/(2 : ℝ)^p+(1/(2 : ℝ)^targetOut)/(2 : ℝ)^j)+
          (1/(2 : ℝ)^localityTarget+1/(2 : ℝ)^localityTarget)/(2 : ℝ)^j)) Fs Gs := by
  dsimp only
  let L := coreLength s coreWidth k
  have hinj : Function.Injective (Fin.castLE hT) := by
    intro i j he
    exact Fin.ext (congrArg (fun k : Fin T => k.val) he)
  have hoff (i : Fin T) (hi : 280 ≤ i.val) : ∀ j, Fin.castLE hT j ≠ i := by
    intro j he
    have hv := congrArg Fin.val he
    change j.val = i.val at hv
    have := j.isLt
    omega
  have hpR : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by have := hsetup.hp; omega)
  have hdomLocal := SchurDominance.dominates_mono (realMatrix s t p u) Finset.univ
    (haloVertices s a b) (1/(8*(p : ℝ))) (Finset.subset_univ _) hsetup.hdom
  have hexists (F : ZMod s → GaussianInt) : ∃ x, SchurDominance.Solves (realMatrix s t p u)
      (haloVertices s a b) x (fun i => (value q ((2 : GaussianInt)^(q-p-1)*F i)).re) :=
    SchurDominance.solves_exists _ _ (1/(8*(p : ℝ))) (by positivity) hdomLocal _
  let y := fun F => Classical.choose (hexists F)
  have hy : ∀ F ∈ complexComponentFields Fs, SchurDominance.Solves (realMatrix s t p u)
      (haloVertices s a b) (y F) (fun i => (value q ((2 : GaussianInt)^(q-p-1)*F i)).re) := by
    intro F _
    exact Classical.choose_spec (hexists F)
  obtain ⟨v₁,H₁,n₁,Ds,hu₁,hDs,hn₁,he₁,houtput,hrep,h251,h276,hrows,hinputWidth,hcore,hframe,hmag,hgood⟩ :=
    packedKeyComplexBatch_exec hbody hbody' hbody'' bodyProtected hbodyProtected bodyComplex hbodyComplex
      bodyFinal hbodyFinal hR hQ hA Bcore hsCore q W hpq hW hqSizing Fs hF y C tail
      (embDn (Fin.castLE hT) v) M B S₀ S hviews hsetup hq hpHeader hcommon hreplicas hpacket hsource
      hblank hcountBlank hcounterBlank hscratch hcell hboundary coreWidth k radius haEq hbEq hleft hright
      h249 h250 hpublicationClean hradiusWord hy hcoeff
  obtain ⟨v₂,H₂,he₂,hv₂,hu₂,hproj,hexternal⟩ := exec_emb hinj hbodyOuter he₁ v rfl H₀ hview₀
  have hread (i : Fin 280) : H₂.R (Fin.castLE hT i) = H₁.R i :=
    congrArg (fun S : Stacks 280 A => S.R i) hproj
  have hext (i : Fin T) (hi : 280 ≤ i.val) : H₂.R i = H₀.R i := (hexternal i (hoff i hi)).2
  have hsep : ∀ i ∈ [Fin.castLE hT 266,Fin.castLE hT 265,Fin.castLE hT 278,Fin.castLE hT 264,
      Fin.castLE hT 279,Fin.castLE hT 269,Fin.castLE hT 253,Fin.castLE hT 270,Fin.castLE hT 271,
      Fin.castLE hT 272,Fin.castLE hT 273,Fin.castLE hT 274,Fin.castLE hT 275], ∀ r, rg r ≠ i := by
    intro i hi r
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact (hoff (rg r) (hrgHigh r) _).symm
  have hqNative : q = executionPrecision p l
      (boundaryHaloTarget p u (boundaryRecoveryTarget p (targetOut+1)) 2
        (haloBoundary s t (PhaseCellBand.width p u) a b).card) 2 := by
    simpa only [hcell,hboundary,hfinal,hrhs] using hqSizing
  have hWnorm : 2*p+13 ≤ W := by
    have hh := packedRound_dimensions p u l targetOut
      (haloBoundary s t (PhaseCellBand.width p u) a b).card
    dsimp only at hh
    rw [←hqNative] at hh
    omega
  have hinterval : coreStart coreWidth k+L ≤ s := by dsimp only [L]; omega
  have hactive : ∀ i ∈ ownedCore s coreWidth k,
      coreStart coreWidth k ≤ i.val ∧ i.val < coreStart coreWidth k+L := by
    intro i hi; exact (mem_haloVertices _ _ i).mp hi
  have hcover : ∀ i : ZMod s, coreStart coreWidth k ≤ i.val → i.val < coreStart coreWidth k+L →
      i ∈ ownedCore s coreWidth k := by intro i hi hj; exact (mem_haloVertices _ _ i).mpr ⟨hi,hj⟩
  have hblank₂ : ∀ i ∈ ([269,270,271,272,273,274,275] : List (Fin 280)), H₁.R i = [] := by
    intro i hi
    have hi' : i.val < 276 := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    let j : Fin 276 := ⟨i.val,hi'⟩
    have hj : 265 ≤ j.val := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only [j] <;> omega
    have hb : M.R j = [] := hblank j (by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢
      dsimp only [j]; rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp)
    exact (hframe j hj).trans hb
  obtain ⟨hlen,v₃,n₃,hu₃,hn₃,he₃,haccuracy⟩ := ordinaryNormalizeNativeBatch_exec (body := bodyOuter)
    (by omega) rg hrg ports hports hreg hsep hsepPorts hsepHeader
    (p := p) (u := u) (l := l) (target := targetOut) (s := s) (t := t) (a := a) (b := b)
    hvaluesFit wl hwl hsetup.hst hsetup.has hsetup.hbs hsetup.hband hbandRoom hgeometryRoom hprecisionRoom
    W (coreStart coreWidth k) L hWnorm hinterval (ownedCore s coreWidth k) hactive hcover q hqNative
    (Fs.map (componentSolution y)) Ds hmag (M.R 253) (M.R 253) headerTail v₂ H₂
    ((hext _ (hrgHigh .wr)).trans hwidth)
    (by intro r hr; exact (hext _ (hrgHigh r)).trans (hbankBlank r hr))
    ((hext _ hheaderHigh).trans hparameters)
    (by rw [hread 266]; exact (congrArg List.length (hframe 266 (by decide))).trans hpHeader)
    (by rw [hread 265]; exact (congrArg List.length (hframe 265 (by decide))).trans hcommon)
    (by rw [hread 278,hrows]; simp [L])
    (by rw [hread 264,hrep,hreplicas,hDs])
    (by intro i hi; simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
        rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl
        all_goals rw [hread]; apply hblank₂; simp)
    (by intro i; exact (hext _ (hportsHigh i)).trans (hheaders i))
    (by rw [hread 279,hinputWidth]; simp [L])
    (by rw [hread 253]; simpa only [ownedCoreWords,packedInterval,L] using houtput)
    (by simpa only [ownedCoreWords,packedInterval,L,hfinal] using hgood)
  let Gs := Ds.map (fun D i => finalRoundWord (2*q+8) q p (inverseNormalizationShift p) (D i))
  let H₃ : Stacks T A := {H₂ with R := (Function.update (Function.update H₂.R headerSrc headerTail)
    (Fin.castLE hT 253) ((Gs.map (fun D => cstream A W (packedInterval (coreStart coreWidth k) L D))).flatten++M.R 253))}
  have he₃' : Exec bodyOuter (ordinaryNormalizePackedBatch rg ports headerSrc
      (Fin.castLE hT 266) (Fin.castLE hT 265) (Fin.castLE hT 278) (Fin.castLE hT 264)
      (Fin.castLE hT 279) (Fin.castLE hT 269) (Fin.castLE hT 253)
      (Fin.castLE hT 270) (Fin.castLE hT 271) (Fin.castLE hT 272)
      (Fin.castLE hT 273) (Fin.castLE hT 274) (Fin.castLE hT 275))
      (mk v₂ H₂) n₃ (mk v₃ H₃) := he₃
  have hheaderOff (i : Fin 280) : Fin.castLE hT i ≠ headerSrc := hoff headerSrc hheaderHigh i
  obtain ⟨v₄,hu₄,he₄⟩ := releasePackedCoreRows_exec (body := bodyOuter)
    (rows := Fin.castLE hT 278) (rowWidth := Fin.castLE hT 279)
    (by exact fun he => (by decide : (278 : Fin 280) ≠ 279) (hinj he)) L (2*q+8) v₃ H₃
    (by simp [H₃,Function.update_of_ne (hheaderOff 278),hread 278,hrows,L])
    (by simp [H₃,Function.update_of_ne (hheaderOff 279),hread 279,hinputWidth,L])
  refine ⟨v₄,_,n₁+n₃+(2*L*((2*q+8)+1)+4),Gs,
    hu₄.trans (hu₃.trans (hu₂.trans hu₁)),hlen.trans hDs,?_,
    (Exec.seq he₂ (Exec.seq he₃' he₄)).cast (by omega) rfl,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [hDs] at hn₃
    dsimp only [L] at hn₃ ⊢
    omega
  · simp [H₃,ownedCoreWords,packedInterval,L]
  · have h278 := hheaderOff 278
    have h279 := hheaderOff 279
    have h253 := hheaderOff 253
    simp [H₃,Ne.symm h278,Ne.symm h279,Ne.symm h253]
  · simp
  · simp
  · intro r hr
    have hr253 := hoff (rg r) (hrgHigh r) 253
    have hr278 := hoff (rg r) (hrgHigh r) 278
    have hr279 := hoff (rg r) (hrgHigh r) 279
    simpa [H₃,Ne.symm hr253,Ne.symm hr278,Ne.symm hr279,hsepHeader r] using
      (hext _ (hrgHigh r)).trans (hbankBlank r hr)
  · have hr253 := hoff (rg .wr) (hrgHigh .wr) 253
    have hr278 := hoff (rg .wr) (hrgHigh .wr) 278
    have hr279 := hoff (rg .wr) (hrgHigh .wr) 279
    simpa [H₃,Ne.symm hr253,Ne.symm hr278,Ne.symm hr279,hsepHeader .wr] using
      (hext _ (hrgHigh .wr)).trans hwidth
  · apply normalizedPackedComponents_generated_accuracy hsetup.hst hsetup.hα
      coreWidth p u localityTarget k q (inverseNormalizationShift p) W hsetup.hp hpq
      hsetup.hwidth hsetup.hαu hsetup.hθ hsetup.hgap hsetup.hbudget Fs hF y Y
      (by intro F hmem; rw [←hhalo]; exact hy F hmem) hY Gs (M.R 253)
      (2/(2 : ℝ)^p+(1/(2 : ℝ)^targetOut)/(2 : ℝ)^inverseNormalizationShift p)
    simpa only [ownedCoreWords,packedInterval,L] using haccuracy

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
