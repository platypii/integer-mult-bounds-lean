module

public import IntegerMultBounds.MathlibTM2.Mult.ShortConvPadding

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

/-- Pad an owned word at its front, retaining the original payload order. -/
def ownedPrefixPadding (exponent width src pad tmp saved : Fin T) (fill : Fin (A+4)) : Pr P T Q A U :=
  .seq (padding exponent width src pad tmp saved) (moveR pad src (fun _ => fill))

theorem ownedPrefixPadding_exec (exponent width src pad tmp saved : Fin T)
    (hreg : [exponent,width,src,pad,tmp,saved].Nodup) (fill : Fin (A+4))
    (l w : ℕ) (v : HS T Q A U) (S : Stacks T A)
    (hl : (S.R exponent).length = l) (hw : (S.R width).length = w)
    (hpad : S.R pad = []) (htmp : S.R tmp = []) (hsaved : S.R saved = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ 6*(2^l*w)+4*(S.R src).length+4*w+9*l+14 ∧
      Exec body (ownedPrefixPadding exponent width src pad tmp saved fill) (mk v S) n
        (mk v' {S with R := (Function.update S.R src
          (List.replicate (2^l*w-(S.R src).length) fill++S.R src))}) := by
  have hr := hreg
  regs_ne hr
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := padding_exec (body := body) hreg v S hpad htmp hsaved
  rw [hl,hw] at hn₁ he₁
  let missing := 2^l*w-(S.R src).length
  let M : Stacks T A := {S with R := Function.update S.R pad (List.replicate missing tick)}
  obtain ⟨v₂,hu₂,he₂⟩ := moveR_exec (body := body) pad src ‹src ≠ pad›.symm (fun _ => fill) v₁ M
  have hcost : 2*(M.R pad).length+2 = 2*missing+2 := by simp [M]
  refine ⟨v₂,n₁+(2*missing+2),hu₂.trans hu₁,?_,(Exec.seq he₁ he₂).cast (by rw [hcost]) ?_⟩
  · have hh : missing ≤ 2^l*w := Nat.sub_le _ _
    omega
  · apply congrArg (mk v₂)
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    by_cases his : i = src
    · subst i
      simp [movedR,M,missing,‹src ≠ pad›]
    by_cases hip : i = pad
    · subst i
      simp [movedR,M,his,hpad]
    · simp [movedR,M,his,hip]

/-- A tile with `2^d` keys and `(2^d)^c` replicas has one dyadic symbol capacity. -/
theorem dyadicTileVolume_eq (c d w : ℕ) :
    2^((c+1)*d)*w = (2^d)^c*(2^d*w) := by
  rw [show (c+1)*d = d*c+d by ring,pow_add,pow_mul]
  ring

def generatedTilePrefixPadding (c : ℕ) (exponent width src totalExponent pad tmp saved : Fin T)
    (fill : Fin (A+4)) : Pr P T Q A U :=
  .seq (umulSym (c+1) tick exponent totalExponent tmp)
    (.seq (ownedPrefixPadding totalExponent width src pad tmp saved fill) (uclear totalExponent))

/-- Generate the total tile exponent, pad from the actual payload length, and
erase all generated counters. Only the owned payload changes. -/
theorem generatedTilePrefixPadding_exec (c : ℕ) (exponent width src totalExponent pad tmp saved : Fin T)
    (hreg : [exponent,width,src,totalExponent,pad,tmp,saved].Nodup) (fill : Fin (A+4))
    (d w : ℕ) (v : HS T Q A U) (S : Stacks T A)
    (hd : (S.R exponent).length = d) (hw : (S.R width).length = w)
    (htotal : S.R totalExponent = []) (hpad : S.R pad = []) (htmp : S.R tmp = []) (hsaved : S.R saved = []) :
    let V := (2^d)^c*(2^d*w)
    ∃ v' n, v'.user = v.user ∧
      n ≤ 6*V+4*(S.R src).length+4*w+11*((c+1)*d)+4*d+20 ∧
      Exec body (generatedTilePrefixPadding c exponent width src totalExponent pad tmp saved fill) (mk v S) n
        (mk v' {S with R := (Function.update S.R src (List.replicate (V-(S.R src).length) fill++S.R src))}) := by
  dsimp only
  have hr := hreg
  regs_ne hr
  obtain ⟨v₁,hu₁,he₁⟩ := umulSym_exec (body := body) (c+1) tick
    ‹exponent ≠ totalExponent› ‹exponent ≠ tmp› ‹totalExponent ≠ tmp› v S htmp
  rw [hd,htotal,List.append_nil] at he₁
  let q := (c+1)*d
  let M : Stacks T A := {S with R := Function.update S.R totalExponent (List.replicate q tick)}
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := ownedPrefixPadding_exec (body := body) totalExponent width src pad tmp saved
    (by regs_nodup) fill q w v₁ M (by simp [M])
    (by simpa [M,‹width ≠ totalExponent›] using hw)
    (by simpa [M,‹totalExponent ≠ pad›.symm] using hpad)
    (by simpa [M,‹totalExponent ≠ tmp›.symm] using htmp)
    (by simpa [M,‹totalExponent ≠ saved›.symm] using hsaved)
  let ys := List.replicate (2^q*w-(S.R src).length) fill++S.R src
  let F : Stacks T A := {M with R := Function.update M.R src ys}
  have he₂' : Exec body (ownedPrefixPadding totalExponent width src pad tmp saved fill) (mk v₁ M) n₂ (mk v₂ F) := by
    simpa only [M,Function.update_of_ne ‹src ≠ totalExponent›] using he₂
  have hsource : M.R src = S.R src := Function.update_of_ne ‹src ≠ totalExponent› _ _
  rw [hsource] at hn₂
  obtain ⟨v₃,hu₃,he₃⟩ := uclear_exec (body := body) totalExponent v₂ F
  have hlength : (F.R totalExponent).length = q := by simp [F,M,‹src ≠ totalExponent›.symm]
  rw [hlength] at he₃
  refine ⟨v₃,(4*d+4)+(n₂+(2*q+2)),hu₃.trans (hu₂.trans hu₁),?_,
    (Exec.seq he₁ (Exec.seq he₂' he₃)).cast rfl ?_⟩
  · rw [←dyadicTileVolume_eq c d w]
    change _ ≤ 6*(2^q*w)+4*(S.R src).length+4*w+11*q+4*d+20
    omega
  · apply congrArg (mk v₃)
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    by_cases hit : i = totalExponent
    · subst i
      simp [F,M,‹src ≠ totalExponent›.symm,htotal]
    by_cases his : i = src
    · subst i
      simp only [Function.update_of_ne hit,Function.update_self]
      simp only [F,Function.update_self,ys,q,dyadicTileVolume_eq,M]
    · simp only [Function.update_of_ne hit,Function.update_of_ne his,F,M]

/-- On a short tile, every scalar and counter cost is paid by the padded volume. -/
theorem generatedTilePrefixPaddingCost_le (c d w n : ℕ) (hw : 0 < w)
    (hfit : n ≤ (2^d)^c*(2^d*w)) :
    6*((2^d)^c*(2^d*w))+4*n+4*w+11*((c+1)*d)+4*d+20 ≤
      29*((2^d)^c*(2^d*w))+20 := by
  rw [←dyadicTileVolume_eq c d w] at hfit ⊢
  have hq : (c+1)*d ≤ 2^((c+1)*d)*w :=
    (Nat.lt_two_pow_self (n := (c+1)*d)).le.trans (Nat.le_mul_of_pos_right _ hw)
  have hd : d ≤ (c+1)*d := Nat.le_mul_of_pos_left d (by omega)
  have hwidth : w ≤ 2^((c+1)*d)*w := Nat.le_mul_of_pos_left _ (pow_pos (by decide) _)
  omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
