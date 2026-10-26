module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRepeatedBatchWeightedSetup
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedBatchSetup

/-! Equal-origin batch setup: generate weights and inverse once, replicate
ordinary words, then route each raw RHS into the existing arithmetic ABI. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

noncomputable def repeatedGeneratedBatchSetup (hQ : SS.states ≤ Q) : Pr P₀ 117 Q A U :=
  .seq (repeatedBatchWeightedSetup hQ) prepareBatchRuntime

def repeatedGeneratedBatchSetupCost (P N q s t u band l L lo B : ℕ) : ℕ :=
  repeatedBatchWeightedSetupCost P N q s t u band L lo B+prepareBatchRuntimeCost P N q l B L (2*q+8)

theorem repeatedGeneratedBatchSetup_exec (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {P s t u band L q N l lo B : ℕ}
    (hP : 13 ≤ P) (hqMax : q ≤ 2*(N+1)) (hs : 0 < s) (hst : s < t) (hu : 1 ≤ u)
    (hL : 0 < L) (hLs : L ≤ s) (hlo : lo < s)
    (v : HS 117 Q A U) (S : Stacks 117 A) (rhs borrowed : List (Fin (A+4)))
    (hprecision : (S.R 114).length = P) (hsR : (S.R 97).length = s) (htR : (S.R 98).length = t)
    (huR : (S.R 99).length = u) (hband : (S.R 100).length = band)
    (hrows : (S.R 102).length = L) (hcount : (S.R 103).length = L)
    (hq : (S.R 112).length = q) (hN : (S.R 101).length = N)
    (hB : S.R 116 = List.replicate B tick) (hloR : (S.R 111).length = lo) (hl : (S.R 109).length = l)
    (hsrc : S.R 110 = rhs++borrowed) (hrhs : rhs.length = B*L*(2*q+8))
    (hclean : CClean mul S) (hblank : ∀ r, S.R (cr r) = [])
    (hfresh : ∀ k ∈ [(64 : Fin 117),65,94,96,104,105,106,107,108,113,115], S.R k = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ repeatedGeneratedBatchSetupCost P N q s t u band l L lo B ∧
      Exec body (repeatedGeneratedBatchSetup hQ) (mk v S) n
        (mk v' (generatedBatchBank { S with R := Function.update S.R 111 [] }
          P s t u band L q N l B (fun _ => lo) rhs borrowed (S.R 109))) := by
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := repeatedBatchWeightedSetup_exec (body := body) (band := band)
    hQ hA hP hqMax hs hst hu hL hLs hlo v S hprecision hsR htR huR hband
    hrows hcount hq hN hB hloR hclean hblank hfresh
  let S₀ : Stacks 117 A := { S with R := Function.update S.R 111 [] }
  let W := batchWeightedBank S₀ P s t u band L q N B (fun _ => lo) (S.R 109)
  let outs := (List.range B).flatMap (fun i => outputWeightRow A (2*q+8) q P s t u L lo)
  let factors := (List.range B).flatMap (fun i => inputWeightRow A (2*q+8) q P s t u L lo)
  let pre := batchGeneratorPage A B P s t u band L q (N+1) ++ outs
  have hpre : pre.length = (3*(B*L)+1)*(2*q+8) := by
    simp [pre, outs, List.length_flatMap]
    ring
  have hfactors : factors.length = B*L*(2*q+8) := by
    simp [factors, List.length_flatMap, Nat.mul_assoc]
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := prepareBatchRuntime_exec (body := body)
    P N q l B L (2*q+8) pre factors rhs borrowed v₁ W
    (by simpa [W,S₀, batchWeightedBank, batchInverseBank, batchWeightedBase, consumedGeometryBank,
      geometryHeaderPorts] using hprecision)
    (by simpa [W,S₀, batchWeightedBank, batchInverseBank, batchWeightedBase, consumedGeometryBank,
      geometryHeaderPorts] using hN)
    (by simpa [W,S₀, batchWeightedBank, batchInverseBank, batchWeightedBase, consumedGeometryBank,
      geometryHeaderPorts] using hq)
    (by simpa [W,S₀, batchWeightedBank, batchInverseBank] using hl)
    (by simp [W,S₀, batchWeightedBank, batchInverseBank])
    (by simpa [W,S₀, batchWeightedBank, batchInverseBank, batchWeightedBase, consumedGeometryBank,
      geometryHeaderPorts] using hcount)
    (by simp [W,S₀, batchWeightedBank, batchInverseBank]) hpre hfactors hrhs
    (by simp [W,S₀, batchWeightedBank, batchInverseBank, batchWeightedBase, batchWeightPage,
      pre, outs, factors, hsrc, List.append_assoc]) (by
      intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · simp [W,S₀, batchWeightedBank, batchInverseBank, consumedGeometryBank, geometryHeaderPorts]
      · simp [W,S₀, batchWeightedBank, batchInverseBank, consumedGeometryBank, geometryHeaderPorts]
      · simp [W,S₀, batchWeightedBank, batchInverseBank, consumedGeometryBank, geometryHeaderPorts]
      · simp [W,S₀, batchWeightedBank, batchInverseBank, consumedGeometryBank, geometryHeaderPorts]
      all_goals simpa [W,S₀, batchWeightedBank, batchInverseBank, batchWeightedBase,
        consumedGeometryBank, geometryHeaderPorts] using hfresh _ (by simp))
  refine ⟨v₂, m₁+m₂, hu₂.trans hu₁, by dsimp only [repeatedGeneratedBatchSetupCost]; omega,
    (Exec.seq he₁ he₂).cast rfl ?_⟩
  congr 1
  simp only [generatedBatchBank, W, S₀, pre, outs, factors, List.append_assoc]

/-- All numerical construction is shared; replicas pay only word transport. -/
theorem repeatedGeneratedBatchSetupCost_affine (P N q s t u band l L lo B : ℕ) :
    repeatedGeneratedBatchSetupCost P N q s t u band l L lo B =
      repeatedGeneratedBatchSetupCost P N q s t u band l L lo 0+
        B*(154*(L*(2*q+8))+15*L+141) := by
  simp only [repeatedGeneratedBatchSetupCost,repeatedBatchWeightedSetupCost,
    repeatedWeightSetupCost,replicateWeightPageCost,finishBatchSetupCost,
    prepareBatchRuntimeCost,swapBatchPayloadCost,installBatchHeadersCost]
  rw [batchInverseSetupCost_affine]
  ring

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
