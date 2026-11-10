module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedCoreArchiveFromDimensions
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellIntervalArchiveAccuracy

/-! The existing generated crop controller accepts complex normalized rows.
Cropping restores forward replica order and adds no arithmetic error. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
variable {T Q A s : ℕ} [NeZero s] {P U : Type} {body : P → Pr P T Q A U}

theorem packedIntervalCoreArchiveFromDimensions_complex_exec
    (radiusHeader coreHeader replicas clock skip count src dst savedSkip saved tmp rows width retireCount trash retireTmp : Fin T)
    (hreg : [radiusHeader,coreHeader,replicas,clock,skip,count,src,dst,savedSkip,saved,tmp,rows,width,retireCount,trash,retireTmp].Nodup)
    (v : HS T Q A U) (S : Stacks T A) (q w start coreRows radius : ℕ)
    (hleft : radius ≤ start)
    (hright : start+coreRows+radius ≤ s)
    (Ds : List (ZMod s → GaussianInt)) (tail : List (Fin (A+4)))
    (hsrc : S.R src = (Ds.reverse.map (fun D => cstream A w
      (packedInterval (start-radius) (coreRows+2*radius) D))).flatten++tail)
    (hR : (S.R radiusHeader).length = radius)
    (hL : (S.R coreHeader).length = coreRows)
    (hw : (S.R width).length = w) (hN : (S.R replicas).length = Ds.length)
    (hclean : ∀ i ∈ [clock,skip,count,rows,savedSkip,saved,tmp,retireCount,trash,retireTmp], S.R i = [])
    (Zs : List (ZMod s → ℂ)) (e : ℝ)
    (hgood : List.Forall₂ (fun z D => PhaseCellInterface.ErrorOn
      (haloVertices s (start-radius) (start+coreRows+radius))
      (packedIntervalRead q w (start-radius)
        (cstream A w (packedInterval (start-radius) (coreRows+2*radius) D)))
      z e) Zs Ds) :
    ∃ v' F n, v'.user = v.user ∧
      n ≤ packedCoreArchiveControlsCost radius (coreRows) w Ds.length+
        (Ds.length*(packedCoreArchiveStepCost radius (coreRows)
          (coreRows+2*radius) w+3)+2)+
        (2*(radius*w+coreRows*w+(coreRows+2*radius))+7) ∧
      Exec body (packedCoreArchiveFromDimensions radiusHeader coreHeader replicas clock skip count src dst savedSkip saved tmp rows width retireCount trash retireTmp)
        (mk v S) n (mk v' F) ∧
      F.R src = tail ∧ F.R dst = (Ds.map (fun D => cstream A w (packedInterval start coreRows D))).flatten++S.R dst ∧
      F.inp = S.inp ∧ F.out = S.out ∧ F.L = S.L ∧
      (∀ i, i ≠ src → i ≠ dst → F.R i = S.R i) ∧
      List.Forall₂ (fun z D => PhaseCellInterface.ErrorOn (haloVertices s start (start+coreRows))
        (packedIntervalRead q w (start) (cstream A w (packedInterval start coreRows D)++S.R dst))
        z e) Zs Ds := by
  obtain ⟨v',F,n,hu,hn,he,hs,hd,hi,ho,hl,hframe⟩ := packedIntervalCoreArchiveFromDimensions_run (body := body)
    radiusHeader coreHeader replicas clock skip count src dst savedSkip saved tmp rows width retireCount trash retireTmp
    hreg v S w start coreRows radius hleft hright Ds tail hsrc hR hL hw hN hclean
  refine ⟨v',F,n,hu,hn,he,hs,hd,hi,ho,hl,hframe,?_⟩
  apply List.Forall₂.imp (fun z D h => ?_) hgood
  have hend : (start-radius)+(coreRows+2*radius) =
      start+coreRows+radius := by omega
  have hc := packedInterval_crop_error q w (start-radius)
    (coreRows+2*radius) radius (coreRows)
    (by omega) (by omega) D [] (S.R dst) z e
    (by simpa only [hend,List.append_nil] using h)
  simpa only [Nat.sub_add_cancel hleft,packedInterval] using hc

theorem packedCoreArchiveFromDimensions_complex_exec
    (radiusHeader coreHeader replicas clock skip count src dst savedSkip saved tmp rows width retireCount trash retireTmp : Fin T)
    (hreg : [radiusHeader,coreHeader,replicas,clock,skip,count,src,dst,savedSkip,saved,tmp,rows,width,retireCount,trash,retireTmp].Nodup)
    (v : HS T Q A U) (S : Stacks T A) (q w coreWidth k radius : ℕ)
    (hleft : radius ≤ coreStart coreWidth k)
    (hright : coreStart coreWidth k+coreLength s coreWidth k+radius ≤ s)
    (Ds : List (ZMod s → GaussianInt)) (tail : List (Fin (A+4)))
    (hsrc : S.R src = (Ds.reverse.map (fun D => cstream A w
      (packedInterval (coreStart coreWidth k-radius) (coreLength s coreWidth k+2*radius) D))).flatten++tail)
    (hR : (S.R radiusHeader).length = radius)
    (hL : (S.R coreHeader).length = coreLength s coreWidth k)
    (hw : (S.R width).length = w) (hN : (S.R replicas).length = Ds.length)
    (hclean : ∀ i ∈ [clock,skip,count,rows,savedSkip,saved,tmp,retireCount,trash,retireTmp], S.R i = [])
    (Zs : List (ZMod s → ℂ)) (e : ℝ)
    (hgood : List.Forall₂ (fun z D => PhaseCellInterface.ErrorOn
      (haloVertices s (coreStart coreWidth k-radius) (coreStart coreWidth k+coreLength s coreWidth k+radius))
      (packedIntervalRead q w (coreStart coreWidth k-radius)
        (cstream A w (packedInterval (coreStart coreWidth k-radius) (coreLength s coreWidth k+2*radius) D)))
      z e) Zs Ds) :
    ∃ v' F n, v'.user = v.user ∧
      n ≤ packedCoreArchiveControlsCost radius (coreLength s coreWidth k) w Ds.length+
        (Ds.length*(packedCoreArchiveStepCost radius (coreLength s coreWidth k)
          (coreLength s coreWidth k+2*radius) w+3)+2)+
        (2*(radius*w+coreLength s coreWidth k*w+(coreLength s coreWidth k+2*radius))+7) ∧
      Exec body (packedCoreArchiveFromDimensions radiusHeader coreHeader replicas clock skip count src dst savedSkip saved tmp rows width retireCount trash retireTmp)
        (mk v S) n (mk v' F) ∧
      F.R src = tail ∧ F.R dst = (Ds.map (fun D => cstream A w (ownedCoreWords coreWidth k D))).flatten++S.R dst ∧
      F.inp = S.inp ∧ F.out = S.out ∧ F.L = S.L ∧
      (∀ i, i ≠ src → i ≠ dst → F.R i = S.R i) ∧
      List.Forall₂ (fun z D => PhaseCellInterface.ErrorOn (ownedCore s coreWidth k)
        (packedIntervalRead q w (coreStart coreWidth k) (cstream A w (ownedCoreWords coreWidth k D)++S.R dst))
        z e) Zs Ds := by
  simpa only [ownedCore,ownedCoreWords,packedInterval] using
    packedIntervalCoreArchiveFromDimensions_complex_exec (body := body)
      radiusHeader coreHeader replicas clock skip count src dst savedSkip saved tmp rows width retireCount trash retireTmp
      hreg v S q w (coreStart coreWidth k) (coreLength s coreWidth k) radius hleft hright
      Ds tail hsrc hR hL hw hN hclean Zs e hgood

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
