module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpBatchLayout

/-! # Correctness of the actual generated-operand batch destination

Attach the correlation error bound to the actual destination tape returned by execution.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds.NLogN

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.Spec.SignedRingProduct

variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U}
  {rg : RpReg → Fin T} {ι : Fin 91 → Fin T}

/-- Actual tape execution and decoded correlation error, with complete restoration. -/
theorem chirpGeneratedBatch_correct (h : RpLayout rg ι) (hT : 91 ≤ T) (hQ : rpStates ≤ Q) (hA : 4 ≤ A)
    (j : SetupReg → Fin T) (records recordSaved srcX srcY saved acc buf savedBlock tmp : Fin T)
    (e : CorrelationReg → Fin T)
    (layout : ChirpBatchLayout j rg ι e records recordSaved srcX srcY saved acc buf savedBlock tmp)
    {s t α q l w M m : ℕ} [NeZero s] [NeZero t]
    (hst : s < t) (hα : 0 < α) (hq : 13 ≤ q) (hw : q + 1 + 2 ≤ w) (hm : 1 ≤ m) (hl : 7 * m ≤ 2 ^ l)
    (u : ZMod s → GaussianInt) (hu : ∀ j, ‖value q (u j)‖ ≤ 1)
    (v : HS T Q A U) (S : Stacks T A)
    (state : ChirpBatchState j rg ι e records recordSaved saved acc buf savedBlock tmp q l w M m S)
    (hsrcX : S.R srcX = cstream A w ((List.range M).flatMap fun n =>
      chirpOperandX s t q m n (chirpInputNumerators s t α q m) u))
    (hsrcY : S.R srcY = chirpBlockStream M (fun n => chirpEntryStream A w (4 * m)
      (fun a => chirpNegativeNumerator true s t α q (2 * m - 1) (n * m) a))) :
    ∃ v' S' n, v'.user = v.user ∧ n ≤ chirpBatchProductCost (q + 1) l w m M ∧
      Exec body (chirpBatchProduct j rg ι h hT hQ records recordSaved srcX srcY saved acc buf savedBlock tmp e)
        (mk v S) n (mk v' S') ∧
      S' = { S with R := (Function.update S.R (e .dst)
        (cstream A w (correlationStream M m (fun n => coeff (q + 1) l
          (chirpOperandX s t q m n (chirpInputNumerators s t α q m) u)
          (chirpOperandY m n (chirpKernelNumerators s t α q m)))) ++ S.R (e .dst))) } ∧
      ∀ k < M, ∀ b : Fin m,
        ‖(4 * (2 ^ l : ℕ) : ℂ) * value (q + 1) (decodeWord
          (((S'.R (e .dst)).drop ((k * m + b.val) * w)).take w)) -
          chirpCorr (t := t) m (rhoC q)
            (fun k0 a => (chirpTableG s t α q m k0 a : ℝ) / 2 ^ q)
            (fun k0 a => (chirpTableK s t α q m k0 a : ℝ) / 2 ^ q)
            (fun j => value q (u j)) (k * m) b.val‖ ≤
          8 * (2 : ℝ) ^ l / (2 : ℝ) ^ (q + 1) := by
  obtain ⟨v', n, hu', hn, he'⟩ := chirpGeneratedBatch_exec (body := body)
    h hT hQ hA j layout.setup_inj layout.width layout.header layout.counters layout.privateBank hst hα hq hw hm hl u hu
    records recordSaved srcX srcY saved acc buf savedBlock tmp layout.packX layout.packY layout.offY layout.data
    e layout.extraction_inj layout.ringSize layout.word layout.batch layout.source v S state.clean state.precision state.ringSize state.width
    state.inputLength state.kernelLength state.setup state.batch hsrcX hsrcY
    state.scratch state.product state.outputLength state.output state.owned state.extraction
  refine ⟨v', _, n, hu', hn, he', rfl, ?_⟩
  intro k hk b
  simp only [Function.update_self]
  exact chirpOperandBatch_err hA hst α q l w M m hα hq hw hm hl u hu (S.R (e .dst)) k hk b

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
