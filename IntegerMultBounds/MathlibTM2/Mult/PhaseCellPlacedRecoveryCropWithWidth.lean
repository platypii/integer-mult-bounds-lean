module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRecoveryCropWithWidth
public import IntegerMultBounds.MathlibTM2.Host.EmbedStock
public import IntegerMultBounds.MathlibTM2.Host.EmbedStream

/-! Place cropping with its generated row-symbol header retained for the
normalization stage. The exact three-stream frame and stock bound are preserved. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {T Q A s : ℕ} [NeZero s] {P U : Type} {body : P → Pr P T Q A U}

theorem placedRecoveryCropWithWidth_exec (e : Fin 19 → Fin T) (he : Function.Injective e) (q a b offset rows : ℕ)
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
    ∃ v' n, v'.user = v.user ∧ n ≤ recoveryCropWithWidthCost q a b offset rows Ds.length ∧
      Exec body (embProg e Empty.elim recoveryCropWithWidth) (Host.mk v S) n
        (Host.mk v' {S with R := (Function.update (Function.update (Function.update S.R (e 9) (List.replicate (rows*(2*q+8)) tick)) (e 11) tail) (e 12)
          ((Ds.reverse.map (fun D => cstream A (2*q+8)
            (packedInterval (a+offset) rows D))).flatten++S.R (e 12)))}) ∧
      List.Forall₂ (fun z D => PhaseCellInterface.ErrorOn (haloVertices s (a+offset) (a+offset+rows))
        (packedIntervalRead q (2*q+8) (a+offset)
          (cstream A (2*q+8) (packedInterval (a+offset) rows D)++S.R (e 12))) z ε) Zs.reverse Ds.reverse ∧
      ∀ depth, ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+
        8*recoveryCropWithWidthCost q a b offset rows Ds.length) depth
        (embProg e Empty.elim recoveryCropWithWidth) (Host.mk v S) n
        (Host.mk v' {S with R := (Function.update (Function.update (Function.update S.R (e 9) (List.replicate (rows*(2*q+8)) tick)) (e 11) tail) (e 12)
          ((Ds.reverse.map (fun D => cstream A (2*q+8)
            (packedInterval (a+offset) rows D))).flatten++S.R (e 12)))}) := by
  obtain ⟨w,n,hu,hn,hex,haccuracy⟩ := recoveryCropWithWidth_exec (body := fun f : Empty => nomatch f)
    q a b offset rows hfit hpart Zs Ds ε tail (embDn e v) (embStk e S)
    hq ha hb hoffset hrows hN hblank hsrc hgood
  obtain ⟨v',_,hu',hex'⟩ := exec_emb_ovr (e := e) (ι := Empty.elim) (body' := body) he
    (fun f => nomatch f) hex v rfl S rfl
  have hfinal : embOvr e ({embStk e S with R := (Function.update
      (Function.update (Function.update (embStk e S).R 9 (List.replicate (rows*(2*q+8)) tick)) 11 tail) 12
      ((Ds.reverse.map (fun D => cstream A (2*q+8) (packedInterval (a+offset) rows D))).flatten++S.R (e 12)))}
        : Stacks 19 A).get S =
      {S with R := (Function.update (Function.update (Function.update S.R (e 9)
        (List.replicate (rows*(2*q+8)) tick)) (e 11) tail) (e 12)
        ((Ds.reverse.map (fun D => cstream A (2*q+8) (packedInterval (a+offset) rows D))).flatten++S.R (e 12)))} := by
    have hL : embExt e (S.L ∘ e) S.L = S.L := embExt_comp (e := e) S.L
    have hR : embExt e (Function.update (Function.update (Function.update (S.R ∘ e) 9
        (List.replicate (rows*(2*q+8)) tick)) 11 tail) 12
        ((Ds.reverse.map (fun D => cstream A (2*q+8) (packedInterval (a+offset) rows D))).flatten++S.R (e 12))) S.R =
        Function.update (Function.update (Function.update S.R (e 9)
          (List.replicate (rows*(2*q+8)) tick)) (e 11) tail) (e 12)
          ((Ds.reverse.map (fun D => cstream A (2*q+8) (packedInterval (a+offset) rows D))).flatten++S.R (e 12)) := by
      rw [embExt_update e he,embExt_update e he,embExt_update_stream e he]
    simp only [embOvr,embStk,Stacks.get,hL,hR]
  simp only [embStk,Function.comp_apply] at hfinal hex'
  rw [hfinal] at hex'
  refine ⟨v',n,hu'.trans hu,hn,hex',haccuracy,fun depth => ?_⟩
  exact mn_native_exec_within hex' 8 (embProg_native e Empty.elim _ recoveryCropWithWidth_native)
    depth _ (by omega)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
