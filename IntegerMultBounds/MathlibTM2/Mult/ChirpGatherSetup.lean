module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpControlBatch
public import IntegerMultBounds.MathlibTM2.Mult.ChirpGatherExec

/-! # Gather cyclic windows with internally generated advance controls -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM

variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U} {rg : TblR 10 → Fin T}

def chirpGatherSetup (rg : TblR 10 → Fin T)
    (dst control savedControl advance window src acc current savedSource buf tmp count : Fin T) : Pr P T Q A U :=
  .seq (chirpControlBatch rg count savedControl acc control)
    (.seq (gatherBatch dst control savedControl advance window src acc current savedSource buf tmp) (uclear control))

/-- The control schedule is generated from dimensions, consumed by the sweep and released.
Only the gathered-window destination changes. The cyclic source itself remains an input. -/
theorem chirpGatherSetup_exec (hrg : Function.Injective rg)
    {dst control savedControl advance window src acc current savedSource buf tmp count : Fin T}
    (hreg : [dst, control, savedControl, advance, window, src, acc, current, savedSource, buf, tmp, count].Nodup)
    (hcount : ∀ r, rg r ≠ count) (hsaved : ∀ r, rg r ≠ savedControl)
    (hacc : ∀ r, rg r ≠ acc) (hcontrol : ∀ r, rg r ≠ control)
    {W e : ℕ} (wl nl : List (Fin (A + 4)))
    (hwl : wl.length = W) (hnl : nl.length = e) (heW : e ≤ W)
    (s t m w M : ℕ) (hs : 0 < s) (hst : s ≤ t) (ht : 0 < t)
    (hk : ∀ j < M, (j + 1) * m < 2 ^ W)
    (hnum : ∀ j < M, s * ((j + 1) * m) < 2 ^ W) (hwidth : m * w < 2 ^ W)
    (st : TblSt 10 A) (hready : ChirpControlReady st s t m w 0)
    (hzero : ∀ i : Fin 10, 4 ≤ i.val → st.val i = 0) (hfit : ∀ i, st.val i < 2 ^ W)
    (u : ZMod s → GaussianInt) (hvalid : ∀ n < M, n * m < t)
    (v : HS T Q A U) (S : Stacks T A) (hS : tblHolds rg S (tblRho W wl nl st))
    (hlen : (S.R count).length = M) (hsrc : S.R src = cstream A w (chirpExtended s m u))
    (hw : (S.R window).length = (3 * m + 1) * w)
    (hclean : ∀ k ∈ [control, savedControl, advance, acc, current, savedSource, buf, tmp], S.R k = []) :
    ∃ v' n, v'.user = v.user ∧
      n ≤ M * (6 * tblC W e + 11 * W + 14 * ((3 * m + 1) * w) + 41) +
        (4 * W + 18) * (chirpCenter s t m M * w) + 6 * tblC W e + 16 ∧
      Exec body (chirpGatherSetup rg dst control savedControl advance window src acc current savedSource buf tmp count)
        (mk v S) n (mk v' { S with R := (Function.update S.R dst
          ((List.range M).flatMap (fun j => cstream A w (chirpWindow s t m j u)) ++ S.R dst)) }) := by
  have hgather : [dst, control, savedControl, advance, window, src, acc, current, savedSource, buf, tmp].Nodup :=
    (List.nodup_append.mp (show ([dst, control, savedControl, advance, window, src, acc,
      current, savedSource, buf, tmp] ++ [count]).Nodup from hreg)).1
  have hreg' := hreg
  regs_ne hreg'
  obtain ⟨v₁, n₁, hu₁, hn₁, he₁⟩ := chirpControlBatch_exec (body := body) hrg count savedControl acc control
    (by regs_nodup) hcount hsaved hacc hcontrol wl nl hwl hnl heW s t m w M hst ht
    hk hnum hwidth st hready hzero hfit v S hS hlen (hclean _ (by simp)) (hclean _ (by simp))
  let controls := gatherControls A (chirpAdvancesFrom s t m w 0 M)
  let S₁ : Stacks T A := { S with R := Function.update S.R control (controls ++ S.R control) }
  have hc0 : S.R control = [] := hclean _ (by simp)
  have off₁ (k : Fin T) (hk : k ≠ control) : S₁.R k = S.R k := by simp [S₁, hk]
  obtain ⟨v₂, hu₂, he₂⟩ := chirpGather_exec (body := body) (dst := dst) (control := control) (savedControl := savedControl)
    (advance := advance) (window := window) (src := src) (acc := acc) (current := current)
    (savedSource := savedSource) (buf := buf) (tmp := tmp) hgather s t m w M hs hst ht u hvalid
    v₁ S₁ (by simp [S₁, hc0, controls]) (by rw [off₁ _ ‹control ≠ src›.symm]; exact hsrc)
    (by rw [off₁ _ ‹control ≠ window›.symm]; exact hw) (by
      intro k hk
      have hz : S.R k = [] := hclean k (List.mem_cons_of_mem control hk)
      have hkc : k ≠ control := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          first | assumption | (apply Ne.symm; assumption)
      exact (off₁ k hkc).trans hz)
  let rows := (List.range M).flatMap (fun j => cstream A w (chirpWindow s t m j u))
  let S₂ : Stacks T A := { S₁ with R := Function.update S₁.R dst (rows ++ S₁.R dst) }
  obtain ⟨v₃, hu₃, he₃⟩ := uclear_exec body control v₂ S₂
  have hcontrols : S₂.R control = controls := by simp [S₂, S₁, ‹dst ≠ control›.symm, hc0]
  have hcost : n₁ + (M * (14 * ((3 * m + 1) * w) + 25) + 12 * (chirpCenter s t m M * w) + 8 +
      (2 * (S₂.R control).length + 2)) ≤
      M * (6 * tblC W e + 11 * W + 14 * ((3 * m + 1) * w) + 41) +
        (4 * W + 18) * (chirpCenter s t m M * w) + 6 * tblC W e + 16 := by
    rw [hcontrols]
    dsimp only [controls]
    rw [length_gatherControls, chirpAdvances_sum]
    have hM : (chirpAdvancesFrom s t m w 0 M).length = M := by simp [chirpAdvancesFrom]
    rw [hM]
    nlinarith
  refine ⟨v₃, _, hu₃.trans (hu₂.trans hu₁), hcost, (Exec.seq he₁ (Exec.seq he₂ he₃)).cast rfl ?_⟩
  congr 1
  ext1
  · rfl
  · rfl
  · rfl
  funext k
  by_cases hk : k = control
  · subst k
    simp [S₂, S₁, Function.update_of_ne ‹dst ≠ control›.symm, hc0]
  · by_cases hkd : k = dst
    · subst k
      simp [S₂, S₁, rows, ‹dst ≠ control›]
    · simp [S₂, S₁, hk, hkd]

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
