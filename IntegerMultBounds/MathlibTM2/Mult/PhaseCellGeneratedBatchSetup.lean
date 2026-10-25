module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBatchWeightedSetup
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPrepareBatchRuntime

/-! Generate the inverse and all weight rows, route raw RHS blocks and install
runtime controls in one fixed 117-tape program. No numerical page is an input. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

noncomputable def generatedBatchSetup (hQ : SS.states ≤ Q) : Pr P₀ 117 Q A U :=
  .seq (batchWeightedSetup hQ) prepareBatchRuntime

def generatedBatchSetupCost (P N q s t u band l L B : ℕ) : ℕ :=
  batchWeightedSetupCost P N q s t u band L B + prepareBatchRuntimeCost P N q l B L (2*q+8)

def generatedBatchBank {A : ℕ} (S : Stacks 117 A) (P s t u band L q N l B : ℕ)
    (lo : ℕ → ℕ) (rhs borrowed control : List (Fin (A+4))) : Stacks 117 A :=
  let W := batchWeightedBank S P s t u band L q N B lo control
  batchHeaderBank { W with R := (Function.update W.R 110
    (batchGeneratorPage A B P s t u band L q (N+1) ++
      (List.range B).flatMap (fun i => outputWeightRow A (2*q+8) q P s t u L (lo i)) ++
      rhs ++ (List.range B).flatMap (fun i => inputWeightRow A (2*q+8) q P s t u L (lo i)) ++ borrowed)) } q l B

theorem generatedBatchSetup_exec (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {P s t u band L q N l B : ℕ} (lo : ℕ → ℕ)
    (hP : 13 ≤ P) (hqMax : q ≤ 2*(N+1)) (hs : 0 < s) (hst : s < t) (hu : 1 ≤ u)
    (hL : 0 < L) (hLs : L ≤ s) (hlo : ∀ i < B, lo i < s)
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
      Exec body (generatedBatchSetup hQ) (mk v S) m
        (mk v' (generatedBatchBank S P s t u band L q N l B lo rhs borrowed control)) := by
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := batchWeightedSetup_exec (body := body) (band := band)
    hQ hA lo hP hqMax hs hst hu hL hLs hlo v S control hprecision hsR htR huR hband
    hrows hcount hq hN hB hpacket hclean hblank hfresh
  let W := batchWeightedBank S P s t u band L q N B lo control
  let outs := (List.range B).flatMap (fun i => outputWeightRow A (2*q+8) q P s t u L (lo i))
  let factors := (List.range B).flatMap (fun i => inputWeightRow A (2*q+8) q P s t u L (lo i))
  let pre := batchGeneratorPage A B P s t u band L q (N+1) ++ outs
  have hpre : pre.length = (3*(B*L)+1)*(2*q+8) := by
    simp [pre, outs, List.length_flatMap]
    ring
  have hfactors : factors.length = B*L*(2*q+8) := by
    simp [factors, List.length_flatMap, Nat.mul_assoc]
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := prepareBatchRuntime_exec (body := body)
    P N q l B L (2*q+8) pre factors rhs borrowed v₁ W
    (by simpa [W, batchWeightedBank, batchInverseBank, batchWeightedBase, consumedGeometryBank,
      geometryHeaderPorts] using hprecision)
    (by simpa [W, batchWeightedBank, batchInverseBank, batchWeightedBase, consumedGeometryBank,
      geometryHeaderPorts] using hN)
    (by simpa [W, batchWeightedBank, batchInverseBank, batchWeightedBase, consumedGeometryBank,
      geometryHeaderPorts] using hq)
    (by simpa [W, batchWeightedBank, batchInverseBank] using hl)
    (by simp [W, batchWeightedBank, batchInverseBank])
    (by simpa [W, batchWeightedBank, batchInverseBank, batchWeightedBase, consumedGeometryBank,
      geometryHeaderPorts] using hcount)
    (by simp [W, batchWeightedBank, batchInverseBank]) hpre hfactors hrhs
    (by simp [W, batchWeightedBank, batchInverseBank, batchWeightedBase, batchWeightPage,
      pre, outs, factors, hsrc, List.append_assoc]) (by
      intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · simp [W, batchWeightedBank, batchInverseBank, consumedGeometryBank, geometryHeaderPorts]
      · simp [W, batchWeightedBank, batchInverseBank, consumedGeometryBank, geometryHeaderPorts]
      · simp [W, batchWeightedBank, batchInverseBank, consumedGeometryBank, geometryHeaderPorts]
      · simp [W, batchWeightedBank, batchInverseBank, consumedGeometryBank, geometryHeaderPorts]
      all_goals simpa [W, batchWeightedBank, batchInverseBank, batchWeightedBase,
        consumedGeometryBank, geometryHeaderPorts] using hfresh _ (by simp))
  refine ⟨v₂, m₁+m₂, hu₂.trans hu₁, by dsimp only [generatedBatchSetupCost]; omega,
    (Exec.seq he₁ he₂).cast rfl ?_⟩
  congr 1
  simp only [generatedBatchBank, W, pre, outs, factors, List.append_assoc]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
