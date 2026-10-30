module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellOrdinaryNormalizePackedBatch
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedComponentSolutions

/-! Normalize the actual paired native output at its computed precision and error target. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

theorem ordinaryNormalizeNativeBatch_exec (hA : 4 ≤ A)
    (rg : TblR 25 → Fin T) (hrg : Function.Injective rg)
    (ports : Fin 4 → Fin T) (hports : Function.Injective ports)
    {headerSrc precision wide rows replicas inputWidth count src work saved tmp sp sg cy : Fin T}
    (hreg : [headerSrc,precision,wide,rows,replicas,inputWidth,count,src,work,saved,tmp,
      ports 0,ports 1,ports 2,ports 3,sp,sg,cy].Nodup)
    (hsep : ∀ i ∈ [precision,wide,rows,replicas,inputWidth,count,src,work,saved,tmp,sp,sg,cy], ∀ r, rg r ≠ i)
    (hsepPorts : ∀ i r, rg r ≠ ports i) (hsepHeader : ∀ r, rg r ≠ headerSrc)
    {B p u l target s t a b : ℕ} [NeZero s]
    (hvaluesFit : ∀ i : Fin 8, ![p,u,l,target,s,t,a,b] i < 2^B)
    (wl : List (Fin (A+4))) (hwl : wl.length = B)
    (hst : s < t) (haS : a ≤ s) (hbS : b ≤ s) (hbandS : PhaseCellBand.width p u ≤ s)
    (hbandRoom : 64*(p+1)+u < 2^B)
    (hgeometryRoom : 8*(t+1)^2+2*PhaseCellBand.width p u+8 < 2^B)
    (hprecisionRoom : inversePrecisionRoom p l target (haloBoundary s t (PhaseCellBand.width p u) a b).card
      (PhaseCellBand.width p u) < 2^B)
    (W c L : ℕ) (hW : 2*p+13 ≤ W) (hinterval : c+L ≤ s)
    (active : Finset (ZMod s)) (hactive : ∀ i ∈ active, c ≤ i.val ∧ i.val < c+L)
    (hcover : ∀ i : ZMod s, c ≤ i.val → i.val < c+L → i ∈ active)
    (q : ℕ)
    (hq : q = executionPrecision p l (boundaryHaloTarget p u (boundaryRecoveryTarget p (target+1)) 2
      (haloBoundary s t (PhaseCellBand.width p u) a b).card) 2)
    (Zs : List (ZMod s → ℂ)) (Ds : List (ZMod s → GaussianInt)) 
    (hz : ∀ z ∈ Zs, ∀ i ∈ active, ‖z i‖ ≤ 4*(2 : ℝ)^(p+8))
    (oldTail tail headerTail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hwidth : S.R (rg .wr) = wl) (hbankBlank : ∀ r : TblR 25, r ≠ .wr → S.R (rg r) = [])
    (hparameters : S.R headerSrc = (inverseParameterWords p u l target s t a b).flatMap
      (fun r => binSyms B r.2)++headerTail)
    (hprecision : (S.R precision).length = p) (hwide : (S.R wide).length = W)
    (hrows : (S.R rows).length = L) (hreplicas : (S.R replicas).length = Ds.length)
    (hblank : ∀ r ∈ [count,work,saved,tmp,sp,sg,cy], S.R r = [])
    (hheaders : ∀ i, S.R (ports i) = []) :
    let j := inverseNormalizationShift p
    (S.R inputWidth).length = L*(2*q+8) →
    S.R src = (Ds.map (fun D => cstream A (2*q+8) (packedInterval c L D))).flatten++tail →
    List.Forall₂ (fun z D => PhaseCellInterface.ErrorOn active
      (packedIntervalRead q (2*q+8) c (cstream A (2*q+8) (packedInterval c L D)++oldTail)) z
      (1/(2 : ℝ)^(target+1)+1/(2 : ℝ)^(target+1))) Zs Ds →
    let Gs := Ds.map (fun D i => finalRoundWord (2*q+8) q p j (D i))
    Gs.length = Ds.length ∧
    ∃ v' n, v'.user = v.user ∧
      n ≤ preparedNormalizePackedBatchCost B p u l target s t a b W Ds.length L+214*B+217 ∧
      Exec body (ordinaryNormalizePackedBatch rg ports headerSrc precision wide rows replicas inputWidth count src work saved tmp sp sg cy)
        (mk v S) n (mk v' {S with R := (Function.update (Function.update S.R headerSrc headerTail) src
          ((Gs.map (fun D => cstream A W (packedInterval c L D))).flatten++tail))}) ∧
      List.Forall₂ (fun z D => PhaseCellInterface.ErrorOn active
        (packedIntervalRead p W c (cstream A W (packedInterval c L D)++tail)) z
          (2/(2 : ℝ)^p+(1/(2 : ℝ)^target)/(2 : ℝ)^j))
        (Zs.map (fun z i => ((2 : ℂ)^j)⁻¹*z i)) Gs := by
  dsimp only
  intro hinputWidth hsrc hgood
  have hq' : q = 4*inverseExecutionExponent p l target
      (haloBoundary s t (PhaseCellBand.width p u) a b).card (PhaseCellBand.width p u) := by
    rw [hq,packedRound_precision]
  have hw : 2*q+8 = 8*inverseExecutionExponent p l target
      (haloBoundary s t (PhaseCellBand.width p u) a b).card (PhaseCellBand.width p u)+8 := by omega
  have he : 1/(2 : ℝ)^target ≤ 1 :=
    (div_le_one (by positivity)).mpr (one_le_pow₀ (by norm_num))
  have hrun := ordinaryNormalizePackedBatch_exec (body := body) hA rg hrg ports hports
    hreg hsep hsepPorts hsepHeader (p := p) (u := u) (l := l) (target := target)
    (s := s) (t := t) (a := a) (b := b) hvaluesFit wl hwl
    hst haS hbS hbandS hbandRoom hgeometryRoom hprecisionRoom W c L hW hinterval
    active hactive hcover Zs Ds (1/(2 : ℝ)^target) he hz oldTail tail headerTail v S
    hwidth hbankBlank hparameters hprecision hwide hrows hreplicas hblank hheaders
  dsimp only at hrun
  rw [←hq',←hw] at hrun
  exact hrun hinputWidth hsrc (by simpa only [component_error_bit] using hgood)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
