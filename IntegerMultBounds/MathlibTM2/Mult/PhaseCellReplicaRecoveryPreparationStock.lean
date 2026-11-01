module

public import IntegerMultBounds.MathlibTM2.Host.ExchangePairStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaRecoveryProblem

/-! A completed preparation row exchanges two input rows for two output rows.
The shared bank and suffixes cancel, so iteration boundaries have equal stock. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s Q A : ℕ} [NeZero s] {U : Type}

theorem replicaRecoveryPreparation_stock (H : ReplicaHaloProblem s) (r : ℕ) (D Y : ZMod s → GaussianInt)
    (rhsTail residualTail : List (Fin (A+4))) (v w : HS 257 Q A U) (S F : Stacks 257 A)
    (hsource : S.R 93 = cstream A H.wordWidth (packedInterval H.origin H.span
      (H.Fs.reverse.getD r (fun _ => 0)))++rhsTail)
    (hresidual : S.R 238 = cstream A H.wordWidth (packedInterval H.origin H.span D)++residualTail)
    (h93 : F.R 93 = rhsTail) (h238 : F.R 238 = residualTail)
    (h125 : F.R 125 = cstream A H.wordWidth (packedInterval H.origin H.span Y)++S.R 125)
    (h256 : F.R 256 = cstream A H.wordWidth (packedInterval H.origin H.span (replicaRecoveryRhs H r Y))++S.R 256)
    (hframe : ∀ k : Fin 257, k ∉ [93,238,125,256] → F.R k = S.R k)
    (hL : F.L = S.L) (hinp : F.inp = S.inp) (hout : F.out = S.out) :
    mnSize (mk w F) = mnSize (mk v S) := by
  let C := cstream A H.wordWidth (packedInterval H.origin H.span (H.Fs.reverse.getD r (fun _ => 0)))
  let ds := cstream A H.wordWidth (packedInterval H.origin H.span D)
  let ys := cstream A H.wordWidth (packedInterval H.origin H.span Y)
  let rs := cstream A H.wordWidth (packedInterval H.origin H.span (replicaRecoveryRhs H r Y))
  have he : F = {S with R := (Function.update (Function.update (Function.update (Function.update S.R
      93 rhsTail) 238 residualTail) 125 (ys++S.R 125)) 256 (rs++S.R 256))} := by
    refine Stacks.ext hinp hout hL ?_
    funext k
    by_cases h93k : k = 93
    · subst k; simpa using h93
    by_cases h238k : k = 238
    · subst k; simpa using h238
    by_cases h125k : k = 125
    · subst k; simpa using h125
    by_cases h256k : k = 256
    · subst k; simpa using h256
    · simpa [Function.update_apply,h93k,h238k,h125k,h256k] using
        hframe k (by simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]; exact ⟨h93k,h238k,h125k,h256k⟩)
  rw [he]
  apply mn_exchange_pair_size 93 238 125 256 (by decide) v w S C ds ys rs rhsTail residualTail hsource hresidual
  · simp [ys,C,length_cstream,packedInterval_length _ H.span_fit]
  · simp [rs,ds,length_cstream,packedInterval_length _ H.span_fit]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
