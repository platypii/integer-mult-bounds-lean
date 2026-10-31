module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCachedBatchInputBank
public import IntegerMultBounds.MathlibTM2.Host.ClosedProgramStock

/-! Shared numerical setup is generated once; its remaining batch charges are
linear encoded traffic. Closed-program structure avoids expanding the compiler. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 121 Q A U}

theorem cachedGeneratedBatchSetup_native (hQ : SS.states ≤ Q) :
    mnNativePushBound (mnProgPush (cachedGeneratedBatchSetup (P₀ := P₀) (A := A) (U := U) hQ))
      (cachedGeneratedBatchSetup (P₀ := P₀) (A := A) (U := U) hQ) := by
  apply WordCmd.native_of_noCalls ?_ le_rfl
  change (WordCmd.NoCalls (copyPrefix 118 117 110 119 120) ∧
    WordCmd.NoCalls (embProg weightCacheCoreReg Empty.elim (preparedBatchWeightedSetup (P₀ := Empty) hQ))) ∧
    WordCmd.NoCalls (embProg weightCacheCoreReg Empty.elim (prepareBatchRuntime (P₀ := Empty)))
  refine ⟨⟨?_,?_⟩,?_⟩
  · simp [copyPrefix,copyR,copyStep,transfer,moveR,moveStep,whileR,
      scanR,drainR,WordCmd.NoCalls]
  · exact WordCmd.noCalls_of_native (embProg_native weightCacheCoreReg Empty.elim _
      (WordCmd.empty_native _))
  · exact WordCmd.noCalls_of_native (embProg_native weightCacheCoreReg Empty.elim _
      (WordCmd.empty_native _))

noncomputable def cachedSetupWorkspace (hQ : SS.states ≤ Q)
    (P N q s t u band l L B : ℕ) : ℕ :=
  mnProgPush (cachedGeneratedBatchSetup (P₀ := P₀) (A := A) (U := U) hQ) *
    cachedGeneratedBatchSetupCost P N q s t u band l L B

/-- Numerical generation is shared; every additional cell pays only linear traffic. -/
theorem cachedSetupWorkspace_affine (hQ : SS.states ≤ Q) (P N q s t u band l L B : ℕ) :
    cachedSetupWorkspace (P₀ := P₀) (A := A) (U := U) hQ P N q s t u band l L B =
      cachedSetupWorkspace (P₀ := P₀) (A := A) (U := U) hQ P N q s t u band l L 0 +
        B * (mnProgPush (cachedGeneratedBatchSetup (P₀ := P₀) (A := A) (U := U) hQ) *
          (104 * (L * (2*q+8)) + 15*L + 64)) := by
  simp only [cachedSetupWorkspace,cachedGeneratedBatchSetupCost,cachedBatchWeightedSetupCost,
    preparedBatchWeightedSetupCost,batchInverseSetupCost,prepareBatchGeneratorPageCost,
    replicateGeneratorsCost,prepareBatchRuntimeCost,swapBatchPayloadCost,installBatchHeadersCost]
  ring

theorem cachedBatchInputBank_setup_exec_within (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    (P N q l s t u band L B : ℕ) (lo : ℕ → ℕ) (hP : 13 ≤ P) (hqMax : q ≤ 2*(N+1))
    (hs : 0 < s) (hst : s < t) (hu : 1 ≤ u) (hL : 0 < L)
    (rhs borrowed outTail cacheTail : List (Fin (A+4))) (inp : List (Bool ⊕ Bool)) (out : List Bool)
    (v : HS 121 Q A U) (S : Stacks 121 A) (hrhs : rhs.length = B*L*(2*q+8))
    (hinput : embStk weightCacheCoreReg S =
      cachedCoreInputBank P N q l s t u band L B lo rhs borrowed outTail inp out)
    (hcache : S.R 117 = batchWeightPage A (2*q+8) q P s t u B L lo++cacheTail)
    (hcacheCount : (S.R 118).length = 2*(B*(L*(2*q+8))))
    (h119 : S.R 119 = []) (h120 : S.R 120 = []) (depth : ℕ) :
    ∃ v' S' m, v'.user = v.user ∧ m ≤ cachedGeneratedBatchSetupCost P N q s t u band l L B ∧
      ExecWithin body (fun level z => mnSize z + level ≤ mnSize (mk v S) + depth +
        cachedSetupWorkspace (P₀ := P₀) (A := A) (U := U) hQ P N q s t u band l L B)
        depth (cachedGeneratedBatchSetup hQ) (mk v S) m (mk v' S') ∧
      embStk weightCacheCoreReg S' =
        generatedBatchBank (batchInputBank P N q l s t u band L B lo rhs borrowed outTail inp out)
          P s t u band L q N l B lo rhs borrowed (List.replicate l tick) ∧
      ∀ i, 117 ≤ i.val → S'.L i = S.L i ∧ S'.R i = S.R i := by
  obtain ⟨v',S',m,hu,hm,he,hproj,hoff⟩ := cachedBatchInputBank_setup_exec (body := body)
    hQ hA P N q l s t u band L B lo hP hqMax hs hst hu hL
    rhs borrowed outTail cacheTail inp out v S hrhs hinput hcache hcacheCount h119 h120
  exact ⟨v',S',m,hu,hm,mn_native_exec_within he _ (cachedGeneratedBatchSetup_native hQ)
    depth _ (Nat.add_le_add_left (Nat.mul_le_mul_left _ hm) _),hproj,hoff⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
