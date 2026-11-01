module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedRestoreReplicaOrder
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedRecoveryOutputCertificate

/-! Physically restore replica order and obtain the unchanged ordered-job
publication certificate on the actual destination prefix. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.PackedNormalizedJob
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {T Q A s : ℕ} [NeZero s] {P U : Type} {body : P → Pr P T Q A U}

theorem restoreReplicaOrder_exec (r : PackedNormalizedJob A s) (e : Fin 14 → Fin T) (he : Function.Injective e)
    (Ds : List (ZMod s → GaussianInt)) (tail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hrows : (S.R (e 0)).length = coreLength s r.coreWidth r.k)
    (hwidth : (S.R (e 1)).length = r.W) (hreplicas : (S.R (e 2)).length = Ds.length)
    (hblank : ∀ k ∈ ([(3 : Fin 14),4,5,8,9,10,11,12,13]), S.R (e k) = [])
    (hsrc : S.R (e 6) = (Ds.map (fun D => cstream A r.W (ownedCoreWords r.coreWidth r.k D))).flatten++tail)
    (hgood : List.Forall₂ (fun F D => PhaseCellInterface.ErrorOn (ownedCore s r.coreWidth r.k)
      (packedIntervalRead r.p r.W (coreStart r.coreWidth r.k)
        (cstream A r.W (ownedCoreWords r.coreWidth r.k D)++tail)) (r.rowTarget F) r.rowError) r.Fs.reverse Ds) :
    ∃ v' n, v'.user = v.user ∧ n ≤ restoreReplicaOrderCost Ds.length (coreLength s r.coreWidth r.k) r.W ∧
      Exec body (embProg e Empty.elim restoreReplicaOrder) (Host.mk v S) n
        (Host.mk v' {S with R := (Function.update (Function.update S.R (e 6) tail) (e 7)
          ((Ds.reverse.map (fun D => cstream A r.W (ownedCoreWords r.coreWidth r.k D))).flatten++S.R (e 7)))}) ∧
      r.output ((Ds.reverse.map (fun D => cstream A r.W (ownedCoreWords r.coreWidth r.k D))).flatten) ∧
      ∀ depth, ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+
        2*restoreReplicaOrderCost Ds.length (coreLength s r.coreWidth r.k) r.W) depth
        (embProg e Empty.elim restoreReplicaOrder) (Host.mk v S) n
        (Host.mk v' {S with R := (Function.update (Function.update S.R (e 6) tail) (e 7)
          ((Ds.reverse.map (fun D => cstream A r.W (ownedCoreWords r.coreWidth r.k D))).flatten++S.R (e 7)))}) := by
  have hfit : coreStart r.coreWidth r.k+coreLength s r.coreWidth r.k ≤ s := by have := r.hright; omega
  have hcert : List.Forall₂ (fun z D => PhaseCellInterface.ErrorOn
      (haloVertices s (coreStart r.coreWidth r.k) (coreStart r.coreWidth r.k+coreLength s r.coreWidth r.k))
      (packedIntervalRead r.p r.W (coreStart r.coreWidth r.k)
        (cstream A r.W (packedInterval (coreStart r.coreWidth r.k) (coreLength s r.coreWidth r.k) D)++tail)) z r.rowError)
      (r.Fs.reverse.map r.rowTarget) Ds := by
    simpa only [List.forall₂_map_left_iff,ownedCore,ownedCoreWords,packedInterval] using hgood
  obtain ⟨v',n,hu,hn,hex,haccuracy,htrace⟩ := placedRestoreReplicaOrder_exec (body := body) e he
    r.p r.W (coreStart r.coreWidth r.k) (coreLength s r.coreWidth r.k) hfit
    (r.Fs.reverse.map r.rowTarget) Ds r.rowError tail v S hrows hwidth hreplicas hblank hsrc hcert
  have hgood' : List.Forall₂ (fun F D => PhaseCellInterface.ErrorOn (ownedCore s r.coreWidth r.k)
      (packedIntervalRead r.p r.W (coreStart r.coreWidth r.k)
        (cstream A r.W (ownedCoreWords r.coreWidth r.k D)++S.R (e 7))) (r.rowTarget F) r.rowError) r.Fs Ds.reverse := by
    simpa only [List.map_reverse,List.reverse_reverse,List.forall₂_map_left_iff,ownedCore,ownedCoreWords,packedInterval] using haccuracy
  have hlen : Ds.reverse.length = r.Fs.length := by
    simpa only [List.length_reverse] using hgood.length_eq.symm
  exact ⟨v',n,hu,hn,hex,r.output_of_fields Ds.reverse hlen (S.R (e 7)) hgood',htrace⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.PackedNormalizedJob
