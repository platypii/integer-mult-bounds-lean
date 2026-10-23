module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpOperandProduct
public import IntegerMultBounds.MathlibTM2.Mult.ChirpOperandStreams

/-! # One shared S1 execution for the generated chirp operands

Specialize actual batch execution, discharging the operand length and disk conditions
from the generated tables and the original grid-input bound.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.Spec.SignedRingProduct

variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U}
  {rg : RpReg → Fin T} {ι : Fin 91 → Fin T}

/-- The actual shared program requires no supplied operand disk or length proofs. -/
theorem chirpGeneratedBatch_exec (h : RpLayout rg ι) (hT : 91 ≤ T) (hQ : rpStates ≤ Q) (hA : 4 ≤ A)
    (j : SetupReg → Fin T) (hj : Function.Injective j)
    (hwidth : j .w = rg .wn) (hheader : j .header = rg .d0)
    (hoff : ∀ s ∈ setupCounters, ∀ r, j s ≠ rg r)
    (hpriv : ∀ s ∈ setupCounters, ∀ k, j s ≠ ι k)
    {s t α q l w M m : ℕ} [NeZero s] [NeZero t]
    (hst : s < t) (hα : 0 < α) (hq : 13 ≤ q) (hw : q + 1 + 2 ≤ w) (hm : 1 ≤ m) (hl : 7 * m ≤ 2 ^ l)
    (u : ZMod s → GaussianInt) (hu : ∀ j, ‖value q (u j)‖ ≤ 1)
    (records recordSaved srcX srcY saved acc buf savedBlock tmp : Fin T)
    (hpackX : [records, recordSaved, j .countX, j .padX, srcX, saved, acc, buf, savedBlock, tmp, rg .xs].Nodup)
    (hpackY : [records, recordSaved, j .countY, j .padY, srcY, saved, acc, buf, savedBlock, tmp, rg .ys].Nodup)
    (hoffY : ∀ k ∈ [records, recordSaved, j .countY, j .padY, srcY, saved, acc, buf, savedBlock, tmp], k ≠ rg .xs)
    (hdata : ∀ k ∈ [records, recordSaved, srcX, srcY, saved, acc, buf, savedBlock, tmp],
      ∀ s ∈ setupWritten, k ≠ j s)
    (e : CorrelationReg → Fin T) (he : Function.Injective e)
    (el : e .l = j .l) (ew : e .w = j .w) (eb : e .batch = records) (es : e .src = rg .out)
    (v : HS T Q A U) (S : Stacks T A) (hc : RpClean ι S)
    (hpR : (S.R (j .p)).length = q + 1) (hlR : (S.R (j .l)).length = l)
    (hwR : (S.R (j .w)).length = w)
    (haR : (S.R (j .a)).length = 3 * m + 1) (hbR : (S.R (j .b)).length = 4 * m)
    (hemptySetup : ∀ s ∈ setupWritten ++ setupScratch, S.R (j s) = [])
    (hrecords : (S.R records).length = M)
    (hsrcX : S.R srcX = cstream A w ((List.range M).flatMap fun n =>
      chirpOperandX s t q m n (chirpInputNumerators s t α q m) u))
    (hsrcY : S.R srcY = chirpBlockStream M (fun n => chirpEntryStream A w (4 * m)
      (fun a => chirpNegativeNumerator true s t α q (2 * m - 1) (n * m) a)))
    (hscratch : ∀ k ∈ [recordSaved, saved, acc, buf, savedBlock, tmp], S.R k = [])
    (hempty : ∀ r ∈ [RpReg.xs, .ys, .sv, .ta, .tb, .acc, .tmp, .d1, .d2, .d3], S.R (rg r) = [])
    (hmR : (S.R (e .m)).length = m) (hout : S.R (rg .out) = [])
    (howned : ∀ r ∈ [CorrelationReg.triples, .skip, .recordSymbols], S.R (e r) = [])
    (hclean : ∀ r ∈ [CorrelationReg.batchSaved, .acc, .savedSource, .savedSkip, .recordSaved,
      .current, .saved, .buf, .tmp], S.R (e r) = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ chirpBatchProductCost (q + 1) l w m M ∧
      Exec body (chirpBatchProduct j rg ι h hT hQ records recordSaved srcX srcY saved acc buf savedBlock tmp e)
        (mk v S) n
        (mk v' { S with R := (Function.update S.R (e .dst)
          (cstream A w (correlationStream M m (fun n => coeff (q + 1) l
            (chirpOperandX s t q m n (chirpInputNumerators s t α q m) u)
            (chirpOperandY m n (chirpKernelNumerators s t α q m)))) ++ S.R (e .dst))) }) := by
  rw [← chirpOperandYStream_eq s t α q w m M hm] at hsrcY
  exact chirpBatchProduct_exec (body := body) h hT hQ hA j hj hwidth hheader hoff hpriv
    (p := q + 1) (by omega) hw hm hl
    (fun n => chirpOperandX s t q m n (chirpInputNumerators s t α q m) u)
    (fun n => chirpOperandY m n (chirpKernelNumerators s t α q m))
    (fun n _ => length_chirpOperandX ..) (fun n _ => length_chirpOperandY ..)
    (fun n _ z hz => chirpOperandX_disk hst α q m hα hq u hu n z hz)
    (fun n _ z hz => chirpOperandY_disk hst α q m hα hq u hu n z hz)
    records recordSaved srcX srcY saved acc buf savedBlock tmp hpackX hpackY hoffY hdata
    e he el ew eb es v S hc hpR hlR hwR haR hbR hemptySetup hrecords hsrcX hsrcY
    hscratch hempty hmR hout howned hclean

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
