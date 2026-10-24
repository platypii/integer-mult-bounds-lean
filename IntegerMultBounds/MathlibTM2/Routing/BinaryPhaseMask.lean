module

public import IntegerMultBounds.MathlibTM2.Routing.BinaryPhaseSeed
public import IntegerMultBounds.MathlibTM2.Routing.BinaryLowPad
public import IntegerMultBounds.MathlibTM2.Routing.BinaryHighPad
public import IntegerMultBounds.MathlibTM2.Routing.PhaseMaskNumeral

/-! Generate the actual full-width R2 phase classifier mask from binary
inputs, including block/count construction, shifting, padding and all cleanup. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactMasks
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

def binaryPhaseMaskProgram {T Q A : ℕ} {P U : Type}
    (rg : PhaseBlockReg → Fin T) (rp : Fin 4 → Fin T) (pad : Fin 2 → Fin T) : Pr P T Q A U :=
  .seq (binaryPhaseSeedProgram rg rp)
    (.seq (binaryLowPadProgram (pad 0) (rp 1) (rp 3) (rg .work) (rg (.scratch 0)) (rg (.scratch 1)))
      (binaryHighPadProgram (pad 1) (rp 1) (rp 3) (rg .work) (rg (.scratch 0)) (rg (.scratch 1))))

def binaryPhaseMaskCost (p : Par) (L Ln Lo Lm : ℕ) :=
  1 + binaryPhaseBlockCost L p.K p.G + binaryWordRepeatCost Ln p.n p.K + (2 * p.K + 2) +
    (Lo * (4 * p.ρ + 11) + 8 * p.ρ + 12) +
    (Lm * (4 * p.m + 11) + 10 * p.m + 4 * (p.ρ + (p.n * p.K + 1)) + 16)

def binaryPhaseMaskUniformCost (n L Ln Lo Lm : ℕ) :=
  1 + ((L * (4 * n + 21) + 2 * n + 16) +
    (L * (4 * n + 11) + 2 * n + 6) + (10 * n + 6 * n + 22) +
    (2 * n + 2) + (2 * n + 2)) + binaryWordRepeatCost Ln n n + (2 * n + 2) +
    (Lo * (4 * n + 11) + 8 * n + 12) +
    (Lm * (4 * n + 11) + 10 * n + 4 * (n + (n * n + 1)) + 16)

theorem binaryPhaseMaskUniformCost_widths_mono (n : ℕ)
    {L L' Ln Ln' Lo Lo' Lm Lm' : ℕ}
    (hL : L ≤ L') (hn : Ln ≤ Ln') (ho : Lo ≤ Lo') (hm : Lm ≤ Lm') :
    binaryPhaseMaskUniformCost n L Ln Lo Lm ≤ binaryPhaseMaskUniformCost n L' Ln' Lo' Lm' := by
  unfold binaryPhaseMaskUniformCost binaryWordRepeatCost
  gcongr

theorem binaryPhaseMaskCost_le (p : Par) (n L Ln Lo Lm : ℕ)
    (hK : p.K ≤ n) (hG : p.G ≤ n) (hn : p.n ≤ n)
    (ho : p.ρ ≤ n) (hm : p.m ≤ n) :
    binaryPhaseMaskCost p L Ln Lo Lm ≤ binaryPhaseMaskUniformCost n L Ln Lo Lm := by
  have hd : p.K - p.G ≤ n := (Nat.sub_le _ _).trans hK
  have hg : p.G - 1 ≤ n := (Nat.sub_le _ _).trans hG
  have ht : p.K - p.G - 2 ≤ n := (Nat.sub_le _ _).trans hd
  unfold binaryPhaseMaskCost binaryPhaseMaskUniformCost binaryPhaseBlockCost binaryWordRepeatCost
  gcongr

theorem binaryPhaseMask_exec {T Q A : ℕ} {P U : Type}
    (body : P → Pr P T Q A U) (p : Par) (hG : 0 < p.G) (hGK : p.G + 1 < p.K)
    (rg : PhaseBlockReg → Fin T) (hrg : Function.Injective rg)
    (rp : Fin 4 → Fin T) (hrp : Function.Injective rp) (hsep : ∀ i r, rp i ≠ rg r)
    (pad : Fin 2 → Fin T) (hpadr : ∀ i r, pad i ≠ rg r) (hpadp : ∀ i j, pad i ≠ rp j)
    (L Ln Lo Lm : ℕ) (hK : p.K < 2 ^ L) (hn : p.n < 2 ^ Ln)
    (ho : p.ρ < 2 ^ Lo) (hm : p.m < 2 ^ Lm)
    (v : HS T Q A U) (S : Stacks T A)
    (hwidth : S.R (rg .width) = binSyms L p.K) (hrun : S.R (rg .run) = binSyms L p.G)
    (hblank : ∀ r, r ≠ .width → r ≠ .run → S.R (rg r) = [])
    (hcount : S.R (rp 0) = binSyms Ln p.n) (hunary : S.R (rp 1) = []) (hsaved : S.R (rp 2) = [])
    (hout : S.R (rp 3) = []) (hoffset : S.R (pad 0) = binSyms Lo p.ρ)
    (htop : S.R (pad 1) = binSyms Lm p.m) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧ m ≤ binaryPhaseMaskCost p L Ln Lo Lm ∧
      Exec body (binaryPhaseMaskProgram rg rp pad) (mk v S) m
        (mk v' { S with R := Function.update S.R (rp 3) (binSyms (p.wy + 1) (mkV p)) }) := by
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := binaryPhaseSeed_exec body rg hrg rp hrp hsep L Ln p.K p.G p.n
    hK hG hGK hn v S hwidth hrun hblank hcount hunary hsaved
  rw [hout] at he₁
  let word : List (Fin (A + 4)) := wordCopies (binSyms p.K (phaseBlockValue p.G)) p.n ++ [bitSymbol true]
  let S₁ : Stacks T A := { S with R := Function.update S.R (rp 3) word }
  have hlreg : [pad 0, rp 1, rp 3, rg .work, rg (.scratch 0), rg (.scratch 1)].Nodup := by
    simp [List.nodup_cons, hrp.eq_iff, hrg.eq_iff, hsep, hpadr, hpadp, Ne.symm]
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := binaryLowPad_exec body (pad 0) (rp 1) (rp 3) (rg .work)
    (rg (.scratch 0)) (rg (.scratch 1)) hlreg Lo p.ρ ho v₁ S₁
    (by simp [S₁, hpadp, hoffset]) (by simp [S₁, hrp.eq_iff, hunary])
    (by simp [S₁, (hsep 3 .work).symm, hblank .work (by simp) (by simp)])
    (by simp [S₁, (hsep 3 (.scratch 0)).symm, hblank (.scratch 0) (by simp) (by simp)])
    (by simp [S₁, (hsep 3 (.scratch 1)).symm, hblank (.scratch 1) (by simp) (by simp)])
  have hd₁ : S₁.R (rp 3) = word := by simp [S₁]
  rw [hd₁] at he₂
  have hv : binSyms (A := A) p.ρ 0 ++ word =
      binSyms (p.ρ + (p.n * p.K + 1)) (mkV p) :=
    phaseMask_shiftedWord p hG hGK
  rw [hv] at he₂
  let W := p.ρ + (p.n * p.K + 1)
  let S₂ : Stacks T A := { S₁ with R := Function.update S₁.R (rp 3) (binSyms W (mkV p)) }
  have hx : mkV p < 2 ^ W := by
    rw [phaseMask_repeatBlocks p]
    apply lowPadValue_lt
    have hfit := repeatBlockValue_lt p.K (phaseBlockValue p.G) p.n (phaseBlockValue_lt _ _ hG hGK)
    rw [pow_succ]
    omega
  have hhreg : [pad 1, rp 1, rp 3, rg .work, rg (.scratch 0), rg (.scratch 1)].Nodup := by
    simp [List.nodup_cons, hrp.eq_iff, hrg.eq_iff, hsep, hpadr, hpadp, Ne.symm]
  obtain ⟨v₃, m₃, hu₃, hm₃, he₃⟩ := binaryHighPad_exec body (pad 1) (rp 1) (rp 3) (rg .work)
    (rg (.scratch 0)) (rg (.scratch 1)) hhreg Lm p.m W _ hm hx v₂ S₂
    (by simp [S₂, S₁, hpadp, htop]) (by simp [S₂])
    (by simp [S₂, S₁, hrp.eq_iff, hunary])
    (by simp [S₂, S₁, (hsep 3 .work).symm, hblank .work (by simp) (by simp)])
    (by simp [S₂, S₁, (hsep 3 (.scratch 0)).symm, hblank (.scratch 0) (by simp) (by simp)])
    (by simp [S₂, S₁, (hsep 3 (.scratch 1)).symm, hblank (.scratch 1) (by simp) (by simp)])
  have hw : W + p.m = p.wy + 1 := by dsimp [W, Par.wy]; omega
  rw [hw] at he₃
  have hf : Function.update S₂.R (rp 3) (binSyms (p.wy + 1) (mkV p)) =
      Function.update S.R (rp 3) (binSyms (p.wy + 1) (mkV p)) := by
    simp only [S₂, S₁, Function.update_idem]
  rw [hf] at he₃
  exact ⟨v₃, m₁ + (m₂ + m₃), hu₃.trans (hu₂.trans hu₁),
    by unfold binaryPhaseMaskCost; dsimp only [W] at hm₃; omega, Exec.seq he₁ (Exec.seq he₂ he₃)⟩

end IntegerMultBounds.MathlibTM2.Routing
