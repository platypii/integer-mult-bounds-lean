module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGatherCounterSetup
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPrefixPadRows
public import IntegerMultBounds.MathlibTM2.StackStockComposition

/-! Physical row padding from retained dimensions, with both generated counters retired. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Fast.Main
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def generatedPrefixPadRows (rows capacity width rowSymbols padSymbols missing src acc saved tmp replicas savedReplicas : Fin T)
    (fill : Fin (A+4)) : Pr P T Q A U :=
  .seq (gatherCounterSetup rows capacity width rowSymbols padSymbols missing saved tmp)
    (.seq (prefixPadRows rowSymbols padSymbols src acc saved tmp replicas savedReplicas fill)
      (.seq (uclear rowSymbols) (uclear padSymbols)))

theorem generatedPrefixPadRows_exec_within
    (rows capacity width rowSymbols padSymbols missing src acc saved tmp replicas savedReplicas : Fin T)
    (hreg : [rows,capacity,width,rowSymbols,padSymbols,missing,src,acc,saved,tmp,replicas,savedReplicas].Nodup)
    (fill : Fin (A+4)) (M C W : ℕ) (hfit : M ≤ C)
    (xs : List (List (Fin (A+4)))) (hlen : ∀ x ∈ xs, x.length = M*W)
    (tail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hrows : (S.R rows).length = M) (hcapacity : (S.R capacity).length = C) (hwidth : (S.R width).length = W)
    (hrow : S.R rowSymbols = []) (hpad : S.R padSymbols = []) (hmissing : S.R missing = [])
    (hsrc : S.R src = xs.flatten++tail) (hacc : S.R acc = [])
    (hreplicas : (S.R replicas).length = xs.length) (hsavedReplicas : S.R savedReplicas = [])
    (hsaved : S.R saved = []) (htmp : S.R tmp = []) (depth : ℕ) :
    ∃ v' n, v'.user = v.user ∧
      n ≤ gatherCounterSetupCost M C W + (xs.length*(6*(C*W)+13)+6) + (2*(C*W)+4) ∧
      ExecWithin body (fun z state => mnSize state+z ≤ mnSize (Host.mk v S)+depth+
        (2*gatherCounterSetupCost M C W + (xs.length*((C-M)*W)+2*(4*(C*W)+10)))) depth
        (generatedPrefixPadRows rows capacity width rowSymbols padSymbols missing src acc saved tmp replicas savedReplicas fill)
        (Host.mk v S) n (Host.mk v' {S with R := (Function.update S.R src
          (xs.flatMap (fun x => List.replicate ((C-M)*W) fill++x)++tail))}) := by
  have hr := hreg
  regs_ne hr
  have hsplit : M*W+(C-M)*W = C*W := by rw [← Nat.add_mul,Nat.add_sub_of_le hfit]
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := gatherCounterSetup_exec_within rows capacity width rowSymbols padSymbols missing saved tmp
    (by regs_nodup) v S hrow hpad hmissing hsaved htmp depth
  simp only [hrows,hcapacity,hwidth] at hn₁ he₁
  let F : Stacks T A := {S with R := (Function.update
    (Function.update S.R rowSymbols (List.replicate (M*W) tick)) padSymbols (List.replicate ((C-M)*W) tick))}
  change ExecWithin _ _ _ _ _ _ (Host.mk v₁ F) at he₁
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := prefixPadRows_exec_within rowSymbols padSymbols src acc saved tmp replicas savedReplicas
    (by regs_nodup) fill (M*W) ((C-M)*W) xs hlen tail v₁ F
    (by simp [F,‹rowSymbols ≠ padSymbols›]) (by simp [F])
    (by simpa [F,‹padSymbols ≠ src›.symm,‹rowSymbols ≠ src›.symm] using hsrc)
    (by simp [F,hacc,‹padSymbols ≠ acc›.symm,‹rowSymbols ≠ acc›.symm])
    (by simpa [F,‹padSymbols ≠ replicas›.symm,‹rowSymbols ≠ replicas›.symm] using hreplicas)
    (by simp [F,hsavedReplicas,‹padSymbols ≠ savedReplicas›.symm,‹rowSymbols ≠ savedReplicas›.symm])
    (by simp [F,hsaved,‹padSymbols ≠ saved›.symm,‹rowSymbols ≠ saved›.symm])
    (by simp [F,htmp,‹padSymbols ≠ tmp›.symm,‹rowSymbols ≠ tmp›.symm]) depth
  rw [hsplit] at hn₂ he₂
  let G : Stacks T A := {F with R := (Function.update F.R src
    (xs.flatMap (fun x => List.replicate ((C-M)*W) fill++x)++tail))}
  change ExecWithin _ _ _ _ _ _ (Host.mk v₂ G) at he₂
  obtain ⟨v₃,hu₃,he₃⟩ := uclear_exec (body := body) rowSymbols v₂ G
  let H : Stacks T A := {G with R := Function.update G.R rowSymbols []}
  obtain ⟨v₄,hu₄,he₄⟩ := uclear_exec (body := body) padSymbols v₃ H
  have hrowlen : (G.R rowSymbols).length = M*W := by
    simp [G,F,‹rowSymbols ≠ src›,‹rowSymbols ≠ padSymbols›]
  have hpadlen : (H.R padSymbols).length = (C-M)*W := by
    simp [H,G,F,‹rowSymbols ≠ padSymbols›.symm,‹padSymbols ≠ src›]
  have hclean := Exec.seq he₃ he₄
  have hnative : mnNativePushBound 0 (.seq (uclear rowSymbols) (uclear padSymbols) : Pr P T Q A U) := by
    simp [uclear,drainR,popDo,peekR,mnNativePushBound,mnActPush]
  have hwclean := mn_native_exec_within hclean 0 hnative depth (mnSize (Host.mk v₂ G)+depth+0) (by omega)
  have hwhole := mn_seq_within_add he₁ (mn_seq_within_add he₂ hwclean)
  have hend : {H with R := Function.update H.R padSymbols []} =
      {S with R := (Function.update S.R src
        (xs.flatMap (fun x => List.replicate ((C-M)*W) fill++x)++tail))} := by
    congr 1
    funext k
    by_cases hk : k = rowSymbols
    · subst k
      simp [H,G,F,‹rowSymbols ≠ padSymbols›,‹rowSymbols ≠ src›,hrow]
    · by_cases hp : k = padSymbols
      · subst k
        simp [H,G,F,‹padSymbols ≠ src›,hpad]
      · by_cases hx : k = src
        · subst k
          simp [H,G,F,‹rowSymbols ≠ src›.symm,‹padSymbols ≠ src›.symm]
        · simp [H,G,F,hk,hp,hx]
  refine ⟨v₄,n₁+(n₂+(2*(G.R rowSymbols).length+2+(2*(H.R padSymbols).length+2))),hu₄.trans (hu₃.trans (hu₂.trans hu₁)),?_,?_⟩
  · rw [hrowlen,hpadlen]
    omega
  · simpa only [generatedPrefixPadRows,Nat.add_zero,hend,Nat.add_assoc] using hwhole
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
