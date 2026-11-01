module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRecoveryNormalizeReady
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedRecoveryCropWithWidth

/-! Crop actual complex recovery fields and normalize them with the generated
packet-width header. Source, queue and all owned controls restore. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
namespace RecoveryNormalizePlan
variable {T Q A s : ℕ} [NeZero s] {P U : Type} {body : P → Pr P T Q A U}

def cropProgram (plan : RecoveryNormalizePlan T) (queue : RecoveryParameterQueue plan)
    (link : RecoveryCropNormalizeLink plan queue) : Pr P T Q A U :=
  .seq (embProg link.reg Empty.elim recoveryCropWithWidth) (plan.fromUnaryProgram queue)

noncomputable def cropTimeCost (r : PackedNormalizedJob A s) (N : ℕ) : ℕ :=
  recoveryCropWithWidthCost r.q r.a r.b r.radius (coreLength s r.coreWidth r.k) N+queueTimeCost r+timeCost r N

noncomputable def cropStock (r : PackedNormalizedJob A s) (N : ℕ) : ℕ :=
  8*recoveryCropWithWidthCost r.q r.a r.b r.radius (coreLength s r.coreWidth r.k) N+
    (8*(2*(4*r.Bcore+4))+13*timeCost r N)

/-- Delayed crop-header retirement is already included in the old crop bill;
normalization adds only its original execution and ordinary queue setup. -/
theorem cropTimeCost_eq (r : PackedNormalizedJob A s) (N : ℕ) :
    cropTimeCost r N = generatedRecoveryCropCost r.q r.a r.b r.radius (coreLength s r.coreWidth r.k) N+
      queueTimeCost r+(preparedNormalizePackedBatchCost r.Bcore r.p r.u r.l r.targetOut s r.t r.a r.b r.W N
        (coreLength s r.coreWidth r.k)+214*r.Bcore+217) := by
  have h := recoveryCropWithWidthCost_retire r.q r.a r.b r.radius (coreLength s r.coreWidth r.k) N
  unfold cropTimeCost timeCost
  omega

theorem crop_exec (plan : RecoveryNormalizePlan T) (queue : RecoveryParameterQueue plan)
    (link : RecoveryCropNormalizeLink plan queue) (hA : 4 ≤ A) (r : PackedNormalizedJob A s)
    (Ds : List (ZMod s → GaussianInt)) (tail : List (Fin (A+4)))
    (wl : List (Fin (A+4))) (hwl : wl.length = r.Bcore) (v : HS T Q A U) (S : Stacks T A)
    (hready : plan.UnaryReady queue r Ds.length wl S)
    (hq : (S.R (link.reg 0)).length = r.q) (ha : (S.R (link.reg 1)).length = r.a)
    (hb : (S.R (link.reg 2)).length = r.b) (hoffset : (S.R (link.reg 3)).length = r.radius)
    (hrows : (S.R (link.reg 4)).length = coreLength s r.coreWidth r.k)
    (hN : (S.R (link.reg 5)).length = Ds.length)
    (hblank : ∀ k ∈ ([(6 : Fin 19),7,8,9,10,13,14,15,16,17,18]), S.R (link.reg k) = [])
    (hsrc : S.R (link.reg 11) = (Ds.map (fun D => cstream A (2*r.q+8) (packedInterval r.a (r.b-r.a) D))).flatten++tail)
    (hgood : List.Forall₂ (fun z D => PhaseCellInterface.ErrorOn (haloVertices s r.a r.b)
      (packedIntervalRead r.q (2*r.q+8) r.a
        (cstream A (2*r.q+8) (packedInterval r.a (r.b-r.a) D)++tail)) z (1/(2 : ℝ)^r.targetOut))
      (r.Fs.map (componentSolution r.localSolution)) Ds) :
    let Gs := Ds.reverse.map (fun D i => finalRoundWord (2*r.q+8) r.q r.p (inverseNormalizationShift r.p) (D i))
    Gs.length = Ds.length ∧
    ∃ v' n, v'.user = v.user ∧ n ≤ cropTimeCost r Ds.length ∧
      Exec body (plan.cropProgram queue link) (Host.mk v S) n
        (Host.mk v' {S with R := (Function.update (Function.update S.R (link.reg 11) tail) plan.src
          ((Gs.map (fun D => cstream A r.W (ownedCoreWords r.coreWidth r.k D))).flatten++S.R plan.src))}) ∧
      List.Forall₂ (fun F D => PhaseCellInterface.ErrorOn (ownedCore s r.coreWidth r.k)
        (packedIntervalRead r.p r.W (coreStart r.coreWidth r.k)
          (cstream A r.W (ownedCoreWords r.coreWidth r.k D)++S.R plan.src)) (r.rowTarget F) r.rowError) r.Fs.reverse Gs ∧
      ∀ depth, ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+cropStock r Ds.length)
        depth (plan.cropProgram queue link) (Host.mk v S) n
        (Host.mk v' {S with R := (Function.update (Function.update S.R (link.reg 11) tail) plan.src
          ((Gs.map (fun D => cstream A r.W (ownedCoreWords r.coreWidth r.k D))).flatten++S.R plan.src))}) := by
  dsimp only
  have hstart : r.a+r.radius = coreStart r.coreWidth r.k := by
    have := r.haEq; have := r.hleft; omega
  have hpart : r.radius+coreLength s r.coreWidth r.k ≤ r.b-r.a := by have := r.haloLength; omega
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁,haccuracy,htrace₁⟩ := placedRecoveryCropWithWidth_exec (body := body) link.reg link.injective
    r.q r.a r.b r.radius (coreLength s r.coreWidth r.k)
    (by have := r.bounds.hbs; have := r.bounds.hab; omega) hpart
    (r.Fs.map (componentSolution r.localSolution)) Ds (1/(2 : ℝ)^r.targetOut) tail v S hq ha hb hoffset hrows hN hblank hsrc
    (by simpa only [Nat.add_sub_of_le r.bounds.hab] using hgood)
  let F : Stacks T A := {S with R := (Function.update (Function.update (Function.update S.R (link.reg 9)
    (List.replicate (coreLength s r.coreWidth r.k*(2*r.q+8)) tick)) (link.reg 11) tail) (link.reg 12)
      ((Ds.reverse.map (fun D => cstream A (2*r.q+8)
        (packedInterval (r.a+r.radius) (coreLength s r.coreWidth r.k) D))).flatten++S.R (link.reg 12)))}
  have hframe (k : Fin T) (hk : plan.support queue k) : F.R k = S.R k := by
    have h := link.support_off k hk
    simp only [F,Function.update_of_ne h.2.2,Function.update_of_ne h.2.1,Function.update_of_ne h.1]
  have hreadyF := hready.of_frame hframe
  have h9s : link.reg 9 ≠ link.reg 11 := fun h => (by decide : (9 : Fin 19) ≠ 11) (link.injective h)
  have h9d : link.reg 9 ≠ link.reg 12 := fun h => (by decide : (9 : Fin 19) ≠ 12) (link.injective h)
  obtain ⟨hlen,v₂,n₂,hu₂,hn₂,he₂,hglobal,htrace₂⟩ := plan.fromUnary_exec queue hA r Ds.reverse
    (S.R plan.src) (S.R plan.src) wl hwl v₁ F hreadyF.width hreadyF.scalar hreadyF.values hreadyF.queueBlank
    hreadyF.precision hreadyF.wide hreadyF.rows (by simpa only [List.length_reverse] using hreadyF.replicas)
    hreadyF.scratch hreadyF.ports
    (by simp only [F,link.inputWidth,Function.update_of_ne h9d,Function.update_of_ne h9s,Function.update_self,List.length_replicate])
    (by simp only [F,link.source,Function.update_self,hstart,ownedCoreWords,packedInterval])
    (by simpa only [hstart,link.source,ownedCoreWords,packedInterval,ownedCore] using haccuracy)
  rw [List.length_reverse] at hlen hn₂
  let output := ((Ds.reverse.map (fun D i => finalRoundWord (2*r.q+8) r.q r.p (inverseNormalizationShift r.p) (D i))).map
    (fun D => cstream A r.W (ownedCoreWords r.coreWidth r.k D))).flatten++S.R plan.src
  have hfinal : {F with R := Function.update (Function.update F.R plan.inputWidth []) plan.src output} =
      {S with R := Function.update (Function.update S.R (link.reg 11) tail) plan.src output} := by
    refine Stacks.ext ?_ ?_ ?_ ?_
    · rfl
    · rfl
    · rfl
    funext k
    change Function.update (Function.update F.R plan.inputWidth []) plan.src output k = _
    by_cases hd : k = plan.src
    · subst k; simp only [Function.update_self]
    · by_cases hw : k = link.reg 9
      · subst k
        simp [link.inputWidth,link.source,h9d,h9s,hblank 9 (by simp)]
      · simp [F,Function.update_apply,link.inputWidth,hw,← link.source,hd]
  change Exec body _ _ _ (Host.mk v₂ {F with R := Function.update (Function.update F.R plan.inputWidth []) plan.src output}) at he₂
  rw [hfinal] at he₂
  refine ⟨hlen,v₂,n₁+n₂,hu₂.trans hu₁,?_,Exec.seq he₁ he₂,hglobal,?_⟩
  · unfold cropTimeCost
    omega
  · intro depth
    have ht₁ := htrace₁ 0
    have ht₂ := htrace₂ 0
    rw [List.length_reverse] at ht₂
    change ExecWithin body _ 0 _ _ n₂
      (Host.mk v₂ {F with R := Function.update (Function.update F.R plan.inputWidth []) plan.src output}) at ht₂
    rw [hfinal] at ht₂
    have ht := mn_seq_within_add ht₁ ht₂
    have hshift := ht.shift depth (J := fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+cropStock r Ds.length)
      (by intro d z hz; unfold cropStock; omega)
    simpa only [cropProgram,Nat.zero_add] using hshift

end RecoveryNormalizePlan
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
