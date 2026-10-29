module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellMetadataPackedBoundaryRhs
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellClosedPackedBoundaryRhsFold

/-! Generate the boundary selection, gather its local RHS and fold it into solver
order. The borrowed RHS suffix is restored and only owned boundary data remains. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 168 Q A U}

def packedBoundaryData : Pr P 168 Q A U := .seq metadataPackedBoundaryRhs closedPackedBoundaryRhsFold

def packedBoundaryDataCost (V N n w : ℕ) : ℕ :=
  metadataPackedBoundaryRhsCost V N w+closedPackedBoundaryRhsFoldCost N n w

theorem packedBoundaryData_exec {V s t band a b origin N : ℕ} [NeZero s]
    (v : HS 168 Q A U) (S : Stacks 168 A)
    (hmeta : CouplingIntervalMetadata V s t band a b origin N S)
    (hfit : origin+N ≤ s) (hst : s < t) (haS : a ≤ s) (hbS : b ≤ s) (hA : 4 ≤ A)
    (hwide : 8*(t+1)^2+2*band+8 < 2^V) (hfitV : origin+(N+2*band)+s < 2^V)
    (hblank : ∀ k : Fin 168, k.val < 77 → S.R k = [])
    (hB : ∀ i ∈ haloBoundary s t band a b, origin ≤ i.val ∧ i.val < origin+N)
    (C : ZMod s → GaussianInt) (w : ℕ) (tail : List (Fin (A+4)))
    (hsource : S.R 110 = cstream A w (packedInterval origin N C)++tail)
    (h167 : S.R 167 = []) (hw : (S.R 130).length = w) (h116 : S.R 116 = []) (h143 : S.R 143 = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ packedBoundaryDataCost V N (haloBoundary s t band a b).card w ∧
      Exec body packedBoundaryData (mk v S) m
        (mk v' {S with R := (Function.update (Function.update (Function.update S.R
          167 (couplingSourceIntervalMaskSymbols true A s t band a b origin N))
          116 (List.replicate (haloBoundary s t band a b).card tick))
          143 (cstream A w ((bFoldOrder s (haloBoundary s t band a b)).map C)))}) := by
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := metadataPackedBoundaryRhs_exec (body := body) v S hmeta
    hfit hst haS hbS hA hwide hfitV (fun k hk => hblank k (by omega)) hB C w tail hsource h167 hw
  let B : Stacks 168 A := {S with R := (Function.update
    (Function.update S.R 167 (couplingSourceIntervalMaskSymbols true A s t band a b origin N))
    93 (cstream A w ((bOrder s (haloBoundary s t band a b)).map C)++S.R 93))}
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := closedPackedBoundaryRhsFold_exec (body := body)
    hst hA band a b hbS hfit hB C w (S.R 93) v₁ B (by simp [B]) (by simp [B])
    (by simpa [B] using hw)
    (by
      intro k hk
      have hn93 : k ≠ 93 := by intro he; subst k; norm_num at hk
      have hn167 : k ≠ 167 := by intro he; subst k; norm_num at hk
      simpa [B,hn93,hn167] using hblank k hk)
    (by simpa [B] using h116) (by simpa [B] using h143)
  refine ⟨v₂,m₁+m₂,hu₂.trans hu₁,Nat.add_le_add hm₁ hm₂,(Exec.seq he₁ he₂).cast rfl ?_⟩
  apply congrArg (mk v₂)
  refine Stacks.ext rfl rfl rfl ?_
  funext k
  by_cases h93 : k = 93
  · subst k; simp [B]
  · simp [B,Function.update_apply,h93]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
