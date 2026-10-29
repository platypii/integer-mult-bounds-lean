module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellMetadataBoundaryMask
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedBoundaryMask

/-! Extract the boundary RHS from a local residual using its retained canonical
metadata. All stacks except the new mask and selected RHS are restored. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Layer
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 168 Q A U}

def metadataPackedBoundaryRhs : Pr P 168 Q A U :=
  .seq metadataBoundaryMask (gatherRecords 110 167 130 0 1 2 3 93 4 pairRe)

def metadataPackedBoundaryRhsCost (V N w : ℕ) : ℕ :=
  144*V+145+((29*N+2)*tblC V 1+66*V+2*N+70)+(N*(16*w+10)+16)

theorem metadataPackedBoundaryRhs_exec {V s t band a b origin N : ℕ} [NeZero s]
    (v : HS 168 Q A U) (S : Stacks 168 A)
    (hmeta : CouplingIntervalMetadata V s t band a b origin N S)
    (hfit : origin+N ≤ s) (hst : s < t) (haS : a ≤ s) (hbS : b ≤ s) (hA : 4 ≤ A)
    (hwide : 8*(t+1)^2+2*band+8 < 2^V) (hfitV : origin+(N+2*band)+s < 2^V)
    (hblank : ∀ k : Fin 168, k.val < 32 → S.R k = [])
    (hB : ∀ i ∈ haloBoundary s t band a b, origin ≤ i.val ∧ i.val < origin+N)
    (C : ZMod s → GaussianInt) (w : ℕ) (tail : List (Fin (A+4)))
    (hsrc : S.R 110 = cstream A w (packedInterval origin N C)++tail)
    (hmask : S.R 167 = []) (hw : (S.R 130).length = w) :
    ∃ v' m, v'.user = v.user ∧
      m ≤ metadataPackedBoundaryRhsCost V N w ∧
      Exec body metadataPackedBoundaryRhs (mk v S) m
        (mk v' {S with R := (Function.update
          (Function.update S.R 167 (couplingSourceIntervalMaskSymbols true A s t band a b origin N))
          93 (cstream A w ((bOrder s (haloBoundary s t band a b)).map C)++S.R 93))}) := by
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := metadataBoundaryMask_exec (body := body) v S hmeta
    hfit hst haS hbS hwide hfitV hblank
  let S₁ : Stacks 168 A := {S with R := (Function.update S.R 167
    (couplingSourceIntervalMaskSymbols true A s t band a b origin N++S.R 167))}
  have hsrc₁ : S₁.R 110 = cstream A w (packedInterval origin N C)++tail := by simpa [S₁] using hsrc
  have hmask₁ : S₁.R 167 = couplingSourceIntervalMaskSymbols true A s t band a b origin N := by
    simp [S₁,hmask]
  have hw₁ : (S₁.R 130).length = w := by simpa [S₁] using hw
  have hfresh : ∀ k ∈ ([0,1,2,3] : List (Fin 168)), S₁.R k = [] := by
    intro k hk
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl <;> simp [S₁]
    all_goals exact hblank _ (by decide)
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := packedBoundaryRhsHaloGather_exec (body := body)
    (src := 110) (mask := 167) (width := 130) (symbols := 0) (ts := 1) (tm := 2)
    (acc := 3) (out := 93) (cs := 4) (by decide) hst hA band a b hbS hfit hB C w tail
    v₁ S₁ hsrc₁ hmask₁ hw₁ hfresh
  refine ⟨v₂,m₁+m₂,hu₂.trans hu₁,by dsimp only [metadataPackedBoundaryRhsCost]; omega,(Exec.seq he₁ he₂).cast rfl ?_⟩
  simp only [S₁,hmask,List.append_nil,Function.update_of_ne (by decide : (93 : Fin 168) ≠ 167)]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
