module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpLineSetupFrame
public import IntegerMultBounds.MathlibTM2.Mult.ChirpLineData

/-! # Derive the retained line interface from raw initialization's bank witness -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Node

/-- Initialization produces all retained data; no input line is needed for this fact. -/
theorem initialized_lineData (W p q l Γ w t s α m : ℕ) (S SB : Stacks 640 A) (z : TblSt 16 A)
    (hL : SB.L = S.L)
    (hframe : ∀ k, k.val < 176 ∨ 369 ≤ k.val → SB.R k = S.R k)
    (hbanks : ∀ b ∈ consumers, tblHolds b.rg SB
      (tblRho W (List.replicate W tick) (List.replicate w tick) ⟨fun i => z.val (b.index i), []⟩))
    (hz : z.val 0 = p ∧ z.val 1 = α ∧ z.val 5 = m ∧ z.val 7 = chirpBlockCount t m ∧ z.val 8 = l ∧
      z.val 9 = Γ ∧ z.val 10 = q ∧ z.val 11 = w ∧ z.val 13 = 0 ∧ z.val 14 = s ∧
      z.val 15 = t ∧ ∀ i, z.val i < 2 ^ W)
    (hproc : ∀ r, S.R (processor r) = [])
    (hcr : ∀ r, S.R (output.cr r) = []) (hnr : ∀ r, S.R (output.nr r) = [])
    (hclean : CClean output.mul S) (hK0 : S.R (batch .srcY) = [])
    (hbank : ∀ i, S.R (output.bank i) = []) (hproducer : ∀ i, S.R (producer i) = [])
    (hring : RpClean host S) (hworkspace : ∀ k ∈ correlationEmpty, S.R k = [])
    (hdim : ∀ i, S.R (correlationDimensions i) = []) (hoperand : S.R (batch .srcX) = [])
    (hraw : ∀ r, r ≠ .raw → r ≠ .dst → S.R (raw r) = []) :
    LineData W s t α p q l Γ m w (preparedStack p q l Γ w t s α m (chirpBlockCount t m) SB) := by
  let M := chirpBlockCount t m
  let SF := preparedStack p q l Γ w t s α m M SB
  have off (k : Fin 640) (hk : k.val < 176 ∨ 369 ≤ k.val) (hn : k ∉ prepareWrites) : SF.R k = S.R k :=
    initialized_off p q l Γ w t s α m M S SB hframe k hk hn
  have hp := initialized_prepared p q l Γ w t s α m M S SB hL hframe
    hproc hcr hnr hclean hK0 hbank
  rcases consumer_state W w z.val SB hbanks with ⟨hg, hc, _, _, hcoef⟩
  rcases hz with ⟨hzp, hzα, hzm, hzM, hzl, hzΓ, hzq, hzw, hz0, hzs, hzt, hzfit⟩
  rw [hzs, hzt, hzm, hzw, hz0] at hg
  rw [hzq, hzt, hzm, hzw, hzl, hz0] at hc
  have hgF : tblHolds gather SF (tblRho W (List.replicate W tick) (List.replicate w tick)
      ⟨![s, t, m, w, 0, 0, 0, 0, 0, 0], []⟩) := by
    intro r
    exact (preparedStack_bank p q l Γ w t s α m M SB (ForwardBankPlacement.gather r)).trans (hg r)
  have hcF : tblHolds convolution SF (tblRho W (List.replicate W tick) (List.replicate w tick)
      ⟨![q, t, m, w, l, 0, 0, 0, 0, 0], []⟩) := by
    intro r
    exact (preparedStack_bank p q l Γ w t s α m M SB (ForwardBankPlacement.convolution r)).trans (hc r)
  have hword : (SF.R wordCounter).length = w := by
    rw [preparedStack_off p q l Γ w t s α m M SB wordCounter wordCounter_not_written]
    change (SB.R (coefficient .wn)).length = w
    have hh := congrArg List.length (hcoef .wn)
    simpa only [tblRho_wn, List.length_replicate] using hh
  refine ⟨?_, ?_, hp.1, ?_, hp.2.2.2.1.mul_clean, hgF, hcF, hword,
    ?_, ?_, ?_, ?_, ?_, ?_, hp.2.2.2.1, hp.2.2.2.2.1, hp.2.2.2.2.2⟩
  · simpa [chirpScheduledStream, chirpTableLength, chirpTableOffset] using hp.2.1
  · simpa [chirpScheduledStream, chirpTableLength, chirpTableOffset] using hp.2.2.1
  · intro r hr
    exact (off _ (Or.inl (processor_range r).2) (processor_data_not_written r hr)).trans (hproc r)
  · intro i
    exact (off _ (Or.inr (by have hi := producer_high i; omega))
      (high_not_written _ (producer_high i))).trans (hproducer i)
  · exact initialized_product_clean p q l Γ w t s α m M S SB hL hframe hring
  · intro k hk
    exact (off k (Or.inr (workspace_high k hk)) (workspace_not_written k hk)).trans (hworkspace k hk)
  · intro i
    exact (off _ (Or.inr (dimensions_high i)) (dimensions_not_written i)).trans (hdim i)
  · exact (off _ (Or.inr (by decide +kernel)) operand_not_written).trans hoperand
  · intro r hr hd
    exact (off _ (raw_outside_banks r) (raw_not_written r)).trans (hraw r hr hd)

end IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement
