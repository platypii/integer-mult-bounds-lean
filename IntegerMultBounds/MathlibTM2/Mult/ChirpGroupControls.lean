module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpLineData

/-! # Generate the retained block count and advance schedule once per group -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Node

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 640 Q A U}

def controlsSetup : Pr P 640 Q A U :=
  .seq (tblUnaryCopies source [(7, raw .count)])
    (chirpControlBatch gather (raw .count) (raw .saved) (raw .acc) (raw .control))

def controlsSetupR (s t m w M : ℕ) (R : Regs 640 A) : Regs 640 A :=
  Function.update (Function.update R (raw .count) (List.replicate M tick)) (raw .control)
    (gatherControls A (chirpAdvancesFrom s t m w 0 M))

def controlsSetupCost (W w s t m M : ℕ) : ℕ :=
  (6 * M + 11 * W + 7) +
    (M * (6 * tblC W w + 11 * W + 14) + 8 * (chirpCenter s t m M * w) + 6 * tblC W w + 6)

/-- Execute both shared controls from the computed source and gather banks, restoring both banks. -/
theorem controlsSetup_exec (W w s t m M : ℕ) (hwW : w ≤ W) (hst : s ≤ t) (ht : 0 < t)
    (hk : ∀ j < M, (j + 1) * m < 2 ^ W)
    (hnum : ∀ j < M, s * ((j + 1) * m) < 2 ^ W) (hwidth : m * w < 2 ^ W)
    (z : TblSt 16 A) (hM : z.val 7 = M) (hfit : ∀ i, z.val i < 2 ^ W)
    (hgfit : ∀ i : Fin 4, (![s, t, m, w] : Fin 4 → ℕ) i < 2 ^ W)
    (v : HS 640 Q A U) (S : Stacks 640 A)
    (hsource : tblHolds source S (tblRho W (List.replicate W tick) (List.replicate w tick) z))
    (hgather : tblHolds gather S (tblRho W (List.replicate W tick) (List.replicate w tick)
      ⟨![s, t, m, w, 0, 0, 0, 0, 0, 0], []⟩))
    (hblank : ∀ r ∈ [ChirpRawReg.count, .saved, .acc, .control], S.R (raw r) = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ controlsSetupCost W w s t m M ∧
      Exec body controlsSetup (mk v S) n (mk v' { S with R := controlsSetupR s t m w M S.R }) := by
  obtain ⟨v₁, n₁, hu₁, hn₁, he₁⟩ := tblUnaryCopies_exec (body := body) source_inj
    (List.replicate W tick) (List.replicate w tick) z hfit [(7, raw .count)]
    (by
      intro p hp r
      simp only [List.mem_singleton] at hp
      subst p
      exact bank_raw _ .count) v S hsource
  have hn₁' : n₁ ≤ 6 * M + 11 * W + 7 := by simpa [unaryCopiesCost, hM, Nat.add_assoc] using hn₁
  let S₁ : Stacks 640 A := { S with R := Function.update S.R (raw .count) (List.replicate M tick) }
  have he₁' : Exec body (tblUnaryCopies source [(7, raw .count)]) (mk v S) n₁ (mk v₁ S₁) := by
    simpa only [unaryCopiesR, hM, hblank .count (by simp), List.append_nil] using he₁
  have off (r : ChirpRawReg) (hr : r ≠ .count) : S₁.R (raw r) = S.R (raw r) :=
    Function.update_of_ne (raw_inj.ne hr) _ _
  obtain ⟨v₂, n₂, hu₂, hn₂, he₂⟩ := chirpControlBatch_exec (body := body) gather_inj
    (raw .count) (raw .saved) (raw .acc) (raw .control)
    (by simpa only [List.map_cons, List.map_nil] using
      (show [ChirpRawReg.count, .saved, .acc, .control].Nodup by decide).map raw_inj)
    (gather_raw .count) (gather_raw .saved) (gather_raw .acc) (gather_raw .control)
    (List.replicate W tick) (List.replicate w tick) (by simp) (by simp) hwW s t m w M hst ht hk hnum hwidth
    ⟨![s, t, m, w, 0, 0, 0, 0, 0, 0], []⟩ ⟨rfl, rfl, rfl, rfl, by simp, by simp⟩
    (by intro i hi; fin_cases i <;> first | (simp at hi; done) | rfl)
    (by intro i; fin_cases i <;> first | exact hgfit 0 | exact hgfit 1 | exact hgfit 2 | exact hgfit 3 | simp)
    v₁ S₁
    (fun r => (Function.update_of_ne (gather_raw .count r) _ _).trans (hgather r))
    (by simp only [S₁, Function.update_self, List.length_replicate])
    ((off .saved (by decide)).trans (hblank .saved (by simp)))
    ((off .acc (by decide)).trans (hblank .acc (by simp)))
  refine ⟨v₂, n₁ + n₂, hu₂.trans hu₁, Nat.add_le_add hn₁' hn₂, ?_⟩
  simpa only [controlsSetup, controlsSetupR, S₁,
    Function.update_of_ne (raw_inj.ne (show ChirpRawReg.control ≠ .count by decide)),
    hblank .control (by simp), List.append_nil] using Exec.seq he₁' he₂

theorem controlsSetupR_off (s t m w M : ℕ) (R : Regs 640 A) (k : Fin 640)
    (hn : k ≠ raw .count) (hc : k ≠ raw .control) : controlsSetupR s t m w M R k = R k := by
  simp only [controlsSetupR, Function.update_of_ne hc, Function.update_of_ne hn]

/-- Installing the two raw controls preserves all arithmetic data and producer ports. -/
theorem controlsSetupR_core (s t m w M : ℕ) (R : Regs 640 A) (k : Fin 640)
    (hk : LineCoreRead k) : controlsSetupR s t m w M R k = R k := by
  apply controlsSetupR_off
  · intro he
    have hv := congrArg Fin.val he
    change k.val = 508 at hv
    rcases hk with hk | hk <;> omega
  · intro he
    have hv := congrArg Fin.val he
    change k.val = 510 at hv
    rcases hk with hk | hk <;> omega

theorem controlsSetupR_high (s t m w M : ℕ) (R : Regs 640 A) (k : Fin 640)
    (hk : 533 ≤ k.val) : controlsSetupR s t m w M R k = R k := by
  apply controlsSetupR_off
  · intro he; have hv := congrArg Fin.val he; change k.val = 508 at hv; omega
  · intro he; have hv := congrArg Fin.val he; change k.val = 510 at hv; omega

/-- Generated controls establish the shared-mode interface without redoing arithmetic setup. -/
theorem LineData.shareControls {W s t α p q l Γ m w : ℕ} {S : Stacks 640 A}
    (h : LineData W s t α p q l Γ m w S) :
    LineData W s t α p q l Γ m w
      { S with R := controlsSetupR s t m w (chirpBlockCount t m) S.R } true := by
  apply h.transport (S' := { S with R := controlsSetupR s t m w (chirpBlockCount t m) S.R }) rfl
    (controlsSetupR_core s t m w (chirpBlockCount t m) S.R)
  refine ⟨?_, ?_, ?_⟩
  · simp only [controlsSetupR, Function.update_of_ne
      (raw_inj.ne (show ChirpRawReg.count ≠ .control by decide)),
      Function.update_self, List.length_replicate]
  · simp only [controlsSetupR, Function.update_self]
  · intro r hr hd hn hc
    exact (controlsSetupR_off s t m w (chirpBlockCount t m) S.R _
      (raw_inj.ne hn) (raw_inj.ne hc)).trans (h.raw r hr hd)

def controlsRelease : Pr P 640 Q A U := clearWords [raw .count, raw .control]

def controlsReleaseR (R : Regs 640 A) : Regs 640 A :=
  fun k => if k ∈ [raw .count, raw .control] then [] else R k

def controlsReleaseCost (s t m w M : ℕ) : ℕ :=
  2 * (M + (chirpCenter s t m M * w + M)) + 5

theorem controlsRelease_exec (s t m w M : ℕ) (v : HS 640 Q A U) (S : Stacks 640 A)
    (hn : (S.R (raw .count)).length = M)
    (hc : S.R (raw .control) = gatherControls A (chirpAdvancesFrom s t m w 0 M)) :
    ∃ v', v'.user = v.user ∧
      Exec body controlsRelease (mk v S) (controlsReleaseCost s t m w M)
        (mk v' { S with R := controlsReleaseR S.R }) := by
  obtain ⟨v', hu, he⟩ := clearWords_exec (body := body) [raw .count, raw .control]
    (by decide +kernel) v S
  have hlen : (gatherControls A (chirpAdvancesFrom s t m w 0 M)).length =
      chirpCenter s t m M * w + M := by
    rw [length_gatherControls, chirpAdvances_sum]
    simp only [chirpAdvancesFrom, List.length_map, List.length_range]
  refine ⟨v', hu, ?_⟩
  unfold controlsRelease controlsReleaseR controlsReleaseCost
  simpa [hn, hc, hlen, Nat.add_assoc] using he

/-- Clearing the shared controls restores their old empty values while retaining published output. -/
theorem controlsReleaseR_collect (s t m w M : ℕ) (R : Regs 640 A) (ys : List (Fin (A + 4)))
    (hn : R (raw .count) = []) (hc : R (raw .control) = []) :
    controlsReleaseR (Function.update (controlsSetupR s t m w M R) groupOutput
      (ys ++ controlsSetupR s t m w M R groupOutput)) =
      Function.update R groupOutput (ys ++ R groupOutput) := by
  have hreg : [raw .count, raw .control, groupOutput].Nodup := by decide +kernel
  regs_ne hreg
  funext k
  by_cases hn' : k = raw .count
  · subst k; simp_all [controlsReleaseR]
  by_cases hc' : k = raw .control
  · subst k; simp_all [controlsReleaseR]
  by_cases ho : k = groupOutput
  · subst k; simp_all [controlsReleaseR, controlsSetupR]
  · simp_all [controlsReleaseR, controlsSetupR]

end IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement
