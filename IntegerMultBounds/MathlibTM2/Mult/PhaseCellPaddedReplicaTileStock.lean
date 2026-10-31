module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPaddedReplicaTile
public import IntegerMultBounds.MathlibTM2.StackResources
public import IntegerMultBounds.MathlibTM2.StackExecutionUnique

/-! Prefix padding is linear native work. The generated exponent is charged
separately so its variable push count does not multiply the payload volume. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Layer
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

private theorem pushN_push (b : Fin T) (f : HS T Q A U → Fin (A+4)) (n : ℕ) (act : Act T Q A U) :
    mnActPush (pushN b f n act) = n+mnActPush act := by
  induction n with
  | zero => simp [pushN]
  | succ n ih => simp [pushN,mnActPush,ih,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

private theorem emptyWhile_within (a : Fin T) (act : Act T Q A U)
    (v : HS T Q A U) (S : Stacks T A) (ha : S.R a = []) (depth B : ℕ)
    (hb : mnSize (mk v S)+depth ≤ B) :
    ExecWithin body (fun z state => mnSize state+z ≤ B) depth (whileR a act)
      (mk v S) 2 (mk {v with flag := false} S) := by
  have he := mn_native_exec_within (Exec.act (body := body) (peekR a) (mk v S)) 0
    (by simp [peekR,mnActPush,mnNativePushBound]) depth B (by simpa using hb)
  rw [peekR_run,ha] at he
  exact ExecWithin.seq he (ExecWithin.loop_false rfl he.final)

private theorem emptyMul_within (c : ℕ) (a b tmp : Fin T) (y : Fin (A+4))
    (v : HS T Q A U) (S : Stacks T A) (ha : S.R a = []) (htmp : S.R tmp = []) (depth B : ℕ)
    (hb : mnSize (mk v S)+depth ≤ B) :
    ExecWithin body (fun z state => mnSize state+z ≤ B) depth (umulSym c y a b tmp)
      (mk v S) 4 (mk {v with flag := false} S) := by
  have h₁ := emptyWhile_within (body := body) a (popDo a (keepIn tmp (pushN b (fun _ => y) c))) v S ha depth B hb
  have h₂ := emptyWhile_within (body := body) tmp (moveStep tmp a id) {v with flag := false} S htmp depth B h₁.final
  exact ExecWithin.seq h₁ h₂

private theorem ownedPrefixPadding_native (exponent width src pad tmp saved : Fin T) (fill : Fin (A+4)) :
    mnNativePushBound 2 (ownedPrefixPadding (P := P) (Q := Q) (A := A) (U := U)
      exponent width src pad tmp saved fill) := by
  simp [ownedPrefixPadding,padding,ucopy,umulSym,scanR,drainR,popDo,keepIn,pushN,
    upow2,scanP,popPush,udbl,usub,dropTop,moveR,whileR,moveStep,peekR,
    mnNativePushBound,mnActPush]

theorem generatedReplicaTilePadding_exec_within {N : ℕ}
    (c : ℕ) (exponent width src totalExponent pad tmp saved : Fin T)
    (hreg : [exponent,width,src,totalExponent,pad,tmp,saved].Nodup)
    (d w : ℕ) (hw : 0 < w) (hN : N ≤ (2^d)^c)
    (realBits imagBits : Fin N → Fin (2^d) → Fin w → Bool)
    (v : HS T Q A U) (S : Stacks T A)
    (hd : (S.R exponent).length = d) (hwidth : (S.R width).length = w)
    (hsrc : S.R src = replicaKeyWords (fun r k b => pairSym A (realBits r k b) (imagBits r k b)))
    (htotal : S.R totalExponent = []) (hpad : S.R pad = []) (htmp : S.R tmp = []) (hsaved : S.R saved = [])
    (depth : ℕ) :
    let V := (2^d)^c*(2^d*w)
    ∃ (r i : Fin ((2^d)^c) → Fin (2^d) → Fin w → Bool), ∃ v' n,
      v'.user = v.user ∧ n ≤ 29*V+20 ∧
      ExecWithin body (fun z state => mnSize state+z ≤ mnSize (mk v S)+depth+74*V+56) depth
        (generatedTilePrefixPadding c exponent width src totalExponent pad tmp saved (pairSym A false false))
        (mk v S) n (mk v' {S with R := (Function.update S.R src
          (replicaKeyWords (fun a k b => pairSym A (r a k b) (i a k b))))}) ∧
      (replicaKeyWords (fun a k b => pairSym A (r a k b) (i a k b))).drop
        (((2^d)^c-N)*(2^d*w)) = S.R src := by
  dsimp only
  let V := (2^d)^c*(2^d*w)
  obtain ⟨r,i,v',n,hu,hn,he,hreal⟩ := generatedReplicaTilePadding_exec (body := body)
    c exponent width src totalExponent pad tmp saved hreg d w hw hN realBits imagBits
    v S hd hwidth hsrc htotal hpad htmp hsaved
  refine ⟨r,i,v',n,hu,hn,?_,hreal⟩
  change Exec body (.seq (umulSym (c+1) tick exponent totalExponent tmp) (.seq _ _)) _ _ _ at he
  cases he with
  | seq hmul hrest =>
    have hregs := hreg
    regs_ne hregs
    obtain ⟨vm,hum,hem⟩ := umulSym_exec (body := body) (c+1) tick
      ‹exponent ≠ totalExponent› ‹exponent ≠ tmp› ‹totalExponent ≠ tmp› v S htmp
    rw [hd] at hem
    obtain ⟨hsteps,hfinal⟩ := hmul.unique hem
    rw [hsteps] at hmul hn ⊢
    rw [hfinal] at hmul hrest
    have hm : ExecWithin body (fun z state => mnSize state+z ≤ mnSize (mk v S)+depth+16*V+16)
        depth (umulSym (c+1) tick exponent totalExponent tmp) (mk v S) (4*d+4)
        (mk vm {S with R := (Function.update S.R totalExponent
          (List.replicate ((c+1)*d) tick++S.R totalExponent))}) := by
      by_cases hd0 : d = 0
      · have ha : S.R exponent = [] := List.eq_nil_of_length_eq_zero (hd.trans hd0)
        have he := emptyMul_within (body := body) (c+1) exponent totalExponent tmp tick v S ha htmp depth
          (mnSize (mk v S)+depth+16*V+16) (by omega)
        obtain ⟨hs,hf⟩ := he.toExec.unique hmul
        rw [hs,hf] at he
        exact he
      · apply mn_native_exec_within hmul (c+2)
        · simp [umulSym,scanR,drainR,popDo,keepIn,pushN_push,moveR,whileR,moveStep,peekR,
            mnNativePushBound,mnActPush]
        · have hq : (c+1)*d ≤ V := by
            change (c+1)*d ≤ (2^d)^c*(2^d*w)
            rw [←dyadicTileVolume_eq c d w]
            exact (Nat.lt_two_pow_self (n := (c+1)*d)).le.trans (Nat.le_mul_of_pos_right _ hw)
          have hdpos : 1 ≤ d := by omega
          have hc : c+2 ≤ 2*((c+1)*d) := by nlinarith
          have hcd : (c+2)*d ≤ 2*((c+1)*d) := by nlinarith
          nlinarith
    cases hrest with
    | seq hbody hclear =>
      let bound := mnSize (mk v S)+depth+74*V+56
      have hm' := hm.mono (J := fun z state => mnSize state+z ≤ bound) (by
        intro z state hs
        dsimp only [bound]
        omega)
      have hb := mn_native_exec_within hbody 2 (ownedPrefixPadding_native _ _ _ _ _ _ _)
        depth bound (by have hs := hm.final; dsimp only [bound]; omega)
      have hc := mn_native_exec_within hclear 0
        (by simp [uclear,drainR,popDo,peekR,mnNativePushBound,mnActPush])
        depth bound (by have hs := hb.final; simpa using hs)
      exact ExecWithin.seq hm' (ExecWithin.seq hb hc)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
