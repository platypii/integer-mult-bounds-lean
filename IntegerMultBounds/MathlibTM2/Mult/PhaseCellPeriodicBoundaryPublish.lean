module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedRecoveryDestination
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellMaskedPackedBoundaryPublish

/-! Publish the full boundary field after the iterate archive has been consumed.
No old interior line is retired: the existing archive is an arbitrary suffix. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 248 Q A U}

def periodicBoundaryPublish : Pr P 248 Q A U :=
  .seq (toUnary 165 246 0 1 2) maskedPackedBoundaryPublish

theorem periodicBoundaryPublish_exec {s t : ℕ} [NeZero s]
    (hst : s < t) (hA : 4 ≤ A) (V band w : ℕ) (hsV : s < 2^V)
    (G : ZMod s → GaussianInt) (hoff : ∀ i ∉ haloBoundary s t band 0 s, G i = 0)
    (v : HS 248 Q A U) (S : Stacks 248 A)
    (hN : S.R 165 = binSyms V s) (hw : (S.R 174).length = w)
    (hsrc : S.R 245 = cstream A w ((bOrder s (haloBoundary s t band 0 s)).map G))
    (hmask : S.R 167 = couplingSourceIntervalMaskSymbols true A s t band 0 s 0 s)
    (hclean : ∀ k ∈ ([0,1,2,246,242,243,244] : List (Fin 248)), S.R k = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ (6*s+11*V+6)+(s*(6*w+10)+6) ∧
      Exec body periodicBoundaryPublish (mk v S) n
        (mk v' {S with R := (Function.update (Function.update (Function.update S.R
          246 (List.replicate s tick)) 245 []) 132 (cstream A w (packedInterval 0 s G)++S.R 132))}) := by
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := toUnary_exec_linear (body := body)
    (a := 165) (z := 246) (w := 0) (t := 1) (t₂ := 2) (by decide) hsV v S hN
    (hclean 0 (by decide)) (hclean 1 (by decide)) (hclean 2 (by decide))
  let T : Stacks 248 A := {S with R := Function.update S.R 246 (List.replicate s tick)}
  have he₁' : Exec body (toUnary 165 246 0 1 2) (mk v S) n₁ (mk v₁ T) := by
    simpa only [hclean 246 (by decide),List.append_nil] using he₁
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := maskedPackedBoundaryPublish_exec (body := body) (origin := 0) (N := s)
    hst hA band 0 s (by omega) (by omega)
    (by intro i _; exact ⟨Nat.zero_le _,by simpa only [Nat.zero_add] using ZMod.val_lt i⟩)
    G hoff w [] v₁ T (by simpa [T] using hsrc) (by simpa [T] using hmask)
    (by simpa [T] using hw)
    (by intro k hk
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
        rcases hk with rfl | rfl | rfl
        · simpa [T] using hclean 242 (by decide)
        · simpa [T] using hclean 243 (by decide)
        · simpa [T] using hclean 244 (by decide))
  refine ⟨v₂,n₁+n₂,hu₂.trans hu₁,Nat.add_le_add hn₁ hn₂,(Exec.seq he₁' he₂).cast rfl ?_⟩
  apply congrArg (mk v₂)
  rfl

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
