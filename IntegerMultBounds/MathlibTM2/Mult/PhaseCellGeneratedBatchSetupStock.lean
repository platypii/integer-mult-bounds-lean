module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedBatchSetup
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBatchWeightedSetupStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPrepareBatchRuntimeStock

/-! Complete generated batch setup keeps shared numerical reserves and native routing separate. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

@[irreducible] def generatedBatchSetupWorkspace (C P N q s t u band l L B : ℕ) : ℕ :=
  batchWeightedSetupWorkspace C P N q s t u band L B+
    4*prepareBatchRuntimeCost P N q l B L (2*q+8)

/-- Additional cells pay linear encoded storage/traffic; all numerical construction is shared. -/
theorem generatedBatchSetupWorkspace_affine (C P N q s t u band l L B : ℕ) :
    generatedBatchSetupWorkspace C P N q s t u band l L B =
      generatedBatchSetupWorkspace C P N q s t u band l L 0+
        B*(640*(L*(2*q+8))+60*L+569) := by
  unfold generatedBatchSetupWorkspace batchWeightedSetupWorkspace
  rw [batchInverseSetupWorkspace_affine C P N q s t u band L B]
  unfold sharedBatchWeightSetupWorkspace
  simp only [packWeightBatchCost,prepareBatchRuntimeCost,swapBatchPayloadCost,installBatchHeadersCost]
  ring

theorem generatedBatchSetup_trace_within (hQ : SS.states ≤ Q) (C P N q s t u band l L B m₁ m₂ : ℕ)
    (v₀ v₁ v₂ : HS 117 Q A U) (S₀ S₁ S₂ : Stacks 117 A)
    (h₁ : ∀ depth, ExecWithin body
      (fun d z => mnSize z+d ≤ mnSize (mk v₀ S₀)+depth+batchWeightedSetupWorkspace C P N q s t u band L B)
      depth (batchWeightedSetup hQ) (mk v₀ S₀) m₁ (mk v₁ S₁))
    (h₂ : Exec body prepareBatchRuntime (mk v₁ S₁) m₂ (mk v₂ S₂))
    (hm₂ : m₂ ≤ prepareBatchRuntimeCost P N q l B L (2*q+8)) (depth : ℕ) :
    ExecWithin body
      (fun d z => mnSize z+d ≤ mnSize (mk v₀ S₀)+depth+generatedBatchSetupWorkspace C P N q s t u band l L B)
      depth (generatedBatchSetup hQ) (mk v₀ S₀) (m₁+m₂) (mk v₂ S₂) := by
  have ht₂ := mn_native_exec_within h₂ 4 prepareBatchRuntime_native depth
    (mnSize (mk v₁ S₁)+depth+4*prepareBatchRuntimeCost P N q l B L (2*q+8)) (by omega)
  exact (mn_seq_within_add (h₁ depth) ht₂).mono (by
    intro d z hz; simpa only [generatedBatchSetupWorkspace] using hz)

theorem generatedBatchSetup_exec_within (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {P s t u band L q N l B : ℕ} (lo : ℕ → ℕ)
    (hP : 13 ≤ P) (hqMax : q ≤ 2*(N+1)) (hs : 0 < s) (hst : s < t) (hu : 1 ≤ u)
    (hL : 0 < L) (hLs : L ≤ s) (hlo : ∀ i < B, lo i < s)
    (C : ℕ) (hpush : mnProgPush (rmulOne (P := P₀) (Q := Q) (A := A) (U := U)
      mul mul_injective (by decide) hQ cr) ≤ C)
    (v : HS 117 Q A U) (S : Stacks 117 A) (rhs borrowed control : List (Fin (A+4)))
    (hprecision : (S.R 114).length = P) (hsR : (S.R 97).length = s) (htR : (S.R 98).length = t)
    (huR : (S.R 99).length = u) (hband : (S.R 100).length = band)
    (hrows : (S.R 102).length = L) (hcount : (S.R 103).length = L)
    (hq : (S.R 112).length = q) (hN : (S.R 101).length = N)
    (hB : S.R 116 = List.replicate B tick) (hl : control.length = l)
    (hpacket : S.R 109 = (List.range B).flatMap (fun i => binSyms (weightWorkspaceWidth P q (2*q+8) t u) (lo i)) ++ control)
    (hsrc : S.R 110 = rhs ++ borrowed) (hrhs : rhs.length = B*L*(2*q+8))
    (hclean : CClean mul S) (hblank : ∀ r, S.R (cr r) = [])
    (hfresh : ∀ k ∈ [(64 : Fin 117), 65, 94, 96, 104, 105, 106, 107, 108, 111, 113, 115], S.R k = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ generatedBatchSetupCost P N q s t u band l L B ∧
      (∀ depth, ExecWithin body
        (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+generatedBatchSetupWorkspace C P N q s t u band l L B)
        depth (generatedBatchSetup hQ) (mk v S) m
        (mk v' (generatedBatchBank S P s t u band L q N l B lo rhs borrowed control))) := by
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := batchWeightedSetup_exec_within (body := body) (band := band)
    hQ hA lo hP hqMax hs hst hu hL hLs hlo C hpush v S control hprecision hsR htR huR hband
    hrows hcount hq hN hB hpacket hclean hblank hfresh
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := weightedBatchRuntime_exec (body := body)
    P N q l s t u band L B lo v₁ S rhs borrowed control hprecision hN hq hcount hl hsrc hrhs
    (by
      intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl
      all_goals exact hfresh _ (by simp))
  exact ⟨v₂,m₁+m₂,hu₂.trans hu₁,by dsimp only [generatedBatchSetupCost]; omega,(fun depth => generatedBatchSetup_trace_within hQ C P N q s t u band l L B m₁ m₂
    v v₁ v₂ S _ _ he₁ he₂ hm₂ depth)⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
