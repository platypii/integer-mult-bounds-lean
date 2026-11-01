module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedRecoveryCrop
public import IntegerMultBounds.MathlibTM2.Host.EmbedStock
public import IntegerMultBounds.MathlibTM2.Host.EmbedStream

/-! Place the generated complex crop/archive lifecycle with its exact ambient
frame and same-run stock certificate. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {T Q A s : ℕ} [NeZero s] {P U : Type} {body : P → Pr P T Q A U}

theorem placedGeneratedRecoveryCrop_exec (e : Fin 19 → Fin T) (he : Function.Injective e) (q a b offset rows : ℕ)
    (hfit : a+(b-a) ≤ s) (hpart : offset+rows ≤ b-a)
    (Zs : List (ZMod s → ℂ)) (Ds : List (ZMod s → GaussianInt)) (ε : ℝ)
    (tail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hq : (S.R (e 0)).length = q) (ha : (S.R (e 1)).length = a) (hb : (S.R (e 2)).length = b)
    (hoffset : (S.R (e 3)).length = offset) (hrows : (S.R (e 4)).length = rows)
    (hN : (S.R (e 5)).length = Ds.length)
    (hblank : ∀ k ∈ ([(6 : Fin 19),7,8,9,10,13,14,15,16,17,18]), S.R (e k) = [])
    (hsrc : S.R (e 11) = (Ds.map (fun D => cstream A (2*q+8) (packedInterval a (b-a) D))).flatten++tail)
    (hgood : List.Forall₂ (fun z D => PhaseCellInterface.ErrorOn (haloVertices s a (a+(b-a)))
      (packedIntervalRead q (2*q+8) a (cstream A (2*q+8) (packedInterval a (b-a) D)++tail)) z ε) Zs Ds) :
    ∃ v' n, v'.user = v.user ∧ n ≤ generatedRecoveryCropCost q a b offset rows Ds.length ∧
      Exec body (embProg e Empty.elim generatedRecoveryCrop) (Host.mk v S) n
        (Host.mk v' {S with R := (Function.update (Function.update S.R (e 11) tail) (e 12)
          ((Ds.reverse.map (fun D => cstream A (2*q+8)
            (packedInterval (a+offset) rows D))).flatten++S.R (e 12)))}) ∧
      List.Forall₂ (fun z D => PhaseCellInterface.ErrorOn (haloVertices s (a+offset) (a+offset+rows))
        (packedIntervalRead q (2*q+8) (a+offset)
          (cstream A (2*q+8) (packedInterval (a+offset) rows D)++S.R (e 12))) z ε) Zs.reverse Ds.reverse ∧
      ∀ depth, ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+
        8*generatedRecoveryCropCost q a b offset rows Ds.length) depth
        (embProg e Empty.elim generatedRecoveryCrop) (Host.mk v S) n
        (Host.mk v' {S with R := (Function.update (Function.update S.R (e 11) tail) (e 12)
          ((Ds.reverse.map (fun D => cstream A (2*q+8)
            (packedInterval (a+offset) rows D))).flatten++S.R (e 12)))}) := by
  obtain ⟨w,n,hu,hn,hex,haccuracy⟩ := generatedRecoveryCrop_exec (body := fun f : Empty => nomatch f)
    q a b offset rows hfit hpart Zs Ds ε tail (embDn e v) (embStk e S)
    hq ha hb hoffset hrows hN hblank hsrc hgood
  obtain ⟨v',_,hu',hex'⟩ := exec_emb_ovr (e := e) (ι := Empty.elim) (body' := body) he
    (fun f => nomatch f) hex v rfl S rfl
  rw [embOvr_two_streams e he] at hex'
  refine ⟨v',n,hu'.trans hu,hn,hex',haccuracy,fun depth => ?_⟩
  exact mn_native_exec_within hex' 8 (embProg_native e Empty.elim _ generatedRecoveryCrop_native)
    depth _ (by omega)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
