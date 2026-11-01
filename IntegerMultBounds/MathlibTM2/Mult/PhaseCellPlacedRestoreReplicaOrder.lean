module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRestoreReplicaOrder
public import IntegerMultBounds.MathlibTM2.Host.EmbedStock
public import IntegerMultBounds.MathlibTM2.Host.EmbedStream

/-! Place the whole-packet replica-order pass with its exact ambient frame. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
variable {T Q A s : ℕ} [NeZero s] {P U : Type} {body : P → Pr P T Q A U}

theorem placedRestoreReplicaOrder_exec (e : Fin 14 → Fin T) (he : Function.Injective e) (q W a L : ℕ) (hfit : a+L ≤ s)
    (Zs : List (ZMod s → ℂ)) (Ds : List (ZMod s → GaussianInt)) (ε : ℝ)
    (tail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hrows : (S.R (e 0)).length = L) (hwidth : (S.R (e 1)).length = W) (hreplicas : (S.R (e 2)).length = Ds.length)
    (hblank : ∀ k ∈ ([(3 : Fin 14),4,5,8,9,10,11,12,13]), S.R (e k) = [])
    (hsrc : S.R (e 6) = (Ds.map (fun D => cstream A W (packedInterval a L D))).flatten++tail)
    (hgood : List.Forall₂ (fun z D => PhaseCellInterface.ErrorOn (haloVertices s a (a+L))
      (packedIntervalRead q W a (cstream A W (packedInterval a L D)++tail)) z ε) Zs Ds) :
    ∃ v' n, v'.user = v.user ∧ n ≤ restoreReplicaOrderCost Ds.length L W ∧
      Exec body (embProg e Empty.elim restoreReplicaOrder) (Host.mk v S) n
        (Host.mk v' {S with R := (Function.update (Function.update S.R (e 6) tail) (e 7)
          ((Ds.reverse.map (fun D => cstream A W (packedInterval a L D))).flatten++S.R (e 7)))}) ∧
      List.Forall₂ (fun z D => PhaseCellInterface.ErrorOn (haloVertices s a (a+L))
        (packedIntervalRead q W a (cstream A W (packedInterval a L D)++S.R (e 7))) z ε) Zs.reverse Ds.reverse ∧
      ∀ depth, ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+
        2*restoreReplicaOrderCost Ds.length L W) depth (embProg e Empty.elim restoreReplicaOrder)
        (Host.mk v S) n
        (Host.mk v' {S with R := (Function.update (Function.update S.R (e 6) tail) (e 7)
          ((Ds.reverse.map (fun D => cstream A W (packedInterval a L D))).flatten++S.R (e 7)))}) := by
  obtain ⟨w,n,hu,hn,hex,haccuracy⟩ := restoreReplicaOrder_exec (body := fun f : Empty => nomatch f)
    q W a L hfit Zs Ds ε tail (embDn e v) (embStk e S) hrows hwidth hreplicas hblank hsrc hgood
  obtain ⟨v',_,hu',hex'⟩ := exec_emb_ovr (e := e) (ι := Empty.elim) (body' := body) he
    (fun f => nomatch f) hex v rfl S rfl
  rw [embOvr_two_streams e he] at hex'
  refine ⟨v',n,hu'.trans hu,hn,hex',haccuracy,fun depth => ?_⟩
  exact mn_native_exec_within hex' 2 (embProg_native e Empty.elim _ restoreReplicaOrder_native)
    depth _ (by omega)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
