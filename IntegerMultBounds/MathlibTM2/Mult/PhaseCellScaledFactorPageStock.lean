module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFactorPageStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellScaledFactorPageSetup
public import IntegerMultBounds.MathlibTM2.Host.EmbedStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellScaledBandControls
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellTableWorkspace

/-! Reuse the generic factor-page kernel at any constant multiple of the retained bandwidth. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellMatrix
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 154 Q A U}

@[irreducible] def scaledGeneratedFactorPageWorkspace (factor q band N : ℕ) : ℕ :=
  (factor+2)*(4*band+5)+factorPageWorkspace q (factor*band+1) N

theorem scaledGeneratedFactorPage_exec_within {s : ℕ} [NeZero s] (B : Finset (ZMod s)) (factor q band : ℕ)
    (columns : List (ZMod s → GaussianInt)) (hlen : columns.length = B.card)
    (hformat : ColumnFamilyFormat (2*q+8) columns) (hA : 4 ≤ A)
    (tail : List (Fin (A+4))) (v : HS 154 Q A U) (S : Stacks 154 A)
    (hq : (S.R 119).length = q) (hband : (S.R 124).length = band) (hN : (S.R 116).length = B.card)
    (hsource : S.R 132 = bandTableWords A (2*q+8) B (factor*band+1) columns 0++tail)
    (h0 : S.R 0 = []) (h94 : S.R 94 = [])
    (hcontrols : ∀ k ∈ [(105 : Fin 154),106,107,108,111,112], S.R k = [])
    (hfresh : ∀ k ∈ [(131 : Fin 154),134,135,136,137,138,151,152,153], S.R k = [])
    (hblank : ∀ r : Fin 154, 1 ≤ r.val → r.val < 7 → S.R r = []) (depth : ℕ) :
    ∃ v' steps, v'.user = v.user ∧ steps ≤ scaledGeneratedFactorPageCost factor q band B.card ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+scaledGeneratedFactorPageWorkspace factor q band B.card)
        depth (scaledGeneratedFactorPage factor) (mk v S) steps
        (mk v' {S with R := (Function.update S.R 140
          (cstream A (2*q+8) ((factorWindowValues B (factor*band+1) columns).flatten++
            (factorInputValues B (factor*band+1) B.card columns).flatten)++S.R 140))}) := by
  let W := factor*band+1
  obtain ⟨v₁,hu₁,he₁⟩ := scaledFactorBandWidth_exec (body := body) factor band v S hband h94 (hfresh 135 (by simp))
  let S₁ : Stacks 154 A := {S with R := Function.update S.R 94 (List.replicate W tick)}
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := factorPage_exec_within (body := body) B q W columns hlen hformat hA tail v₁ S₁
    (by simpa [S₁] using hq) (by simp [S₁]) (by simpa [S₁] using hN)
    (by simpa [S₁,W] using hsource) (by simpa [S₁] using h0)
    (by
      intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> simpa [S₁] using hcontrols _ (by simp))
    (by
      intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simpa [S₁] using hfresh _ (by simp)) (by
      intro r hr1 hr7
      have hr94 : r ≠ 94 := by omega
      simpa [S₁,hr94] using hblank r hr1 hr7) depth
  let output := cstream A (2*q+8) ((factorWindowValues B W columns).flatten++
    (factorInputValues B W B.card columns).flatten)++S.R 140
  let S₂ : Stacks 154 A := {S₁ with R := Function.update S₁.R 140 output}
  have he₂' : ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v₁ S₁)+depth+factorPageWorkspace q W B.card)
      depth factorPage (mk v₁ S₁) m₂ (mk v₂ S₂) := he₂
  obtain ⟨v₃,hu₃,he₃⟩ := uclear_exec body 94 v₂ S₂
  have hlen94 : (S₂.R 94).length = W := by simp [S₂,S₁]
  have hn : mnNativePushBound (factor+2) (scaledFactorBandWidth (P := P) (Q := Q) (A := A) (U := U) factor) := by
    unfold scaledFactorBandWidth
    apply embProg_native
    have hpush (k : ℕ) (a : Act 151 Q A U) :
        mnActPush (pushN 94 (fun _ => tick) k a) = k+mnActPush a := by
      induction k with
      | zero => simp [pushN]
      | succ k ih => simp [pushN,mnActPush,ih,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
    simp [scaledBandWidth,umul,umulSym,scanR,drainR,popDo,keepIn,moveR,moveStep,
      whileR,peekR,mnNativePushBound,hpush,mnActPush]
  have ht₁ := mn_native_exec_within he₁ (factor+2) hn depth _ (Nat.le_refl _)
  have ht₃ := mn_native_exec_within he₃ 0 (by
    simp [uclear,drainR,popDo,peekR,mnNativePushBound,mnActPush]) depth
    (mnSize (mk v₁ S₁)+depth+factorPageWorkspace q W B.card)
    (by simpa only [Nat.zero_mul,Nat.add_zero] using he₂'.final)
  have ht := (mn_seq_within_add ht₁ (ExecWithin.seq he₂' ht₃)).mono
    (J := fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+scaledGeneratedFactorPageWorkspace factor q band B.card)
    (by intro d z hz; unfold scaledGeneratedFactorPageWorkspace; exact hz)
  refine ⟨v₃,(4*band+5)+(m₂+(2*W+2)),hu₃.trans (hu₂.trans hu₁),
    Nat.add_le_add_left (Nat.add_le_add_right hm₂ _) _,
    ht.cast (by rw [hlen94]) ?_⟩
  apply congrArg (mk v₃)
  refine Stacks.ext rfl rfl rfl ?_
  funext k
  by_cases hk94 : k = 94 <;> by_cases hk140 : k = 140 <;> simp [S₂,S₁,output,W,hk94,hk140,h94]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
