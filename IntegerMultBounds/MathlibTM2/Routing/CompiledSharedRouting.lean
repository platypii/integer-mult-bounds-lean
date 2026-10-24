module

public import IntegerMultBounds.MathlibTM2.Routing.CompiledElementaryRouting
public import IntegerMultBounds.MathlibTM2.Routing.ElementarySharedProgram

/-!
# Compiled routing with executed shared setup and final cleanup

Raw binary shared inputs and a coordinate table suffice: counters, instruction
headers and masks are constructed by actual programs. All metadata is cleared
and both raw inputs are restored. Only the record stream changes.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

variable {t₀ T Q K : ℕ} {P U : Type}

/-- All shared setup, compilation, routing and cleanup execute, with a complete
stream-only bank frame and a cost bound in the input dimensions and pair count. -/
theorem compiledSharedRouting_exec {n rows B : ℕ}
    (body : P → Pr P T Q (prime + K) U)
    (compiler : ElementaryCompilerReg → Fin T) (hcompiler : Function.Injective compiler)
    (src archive : Fin T) (hsa : src ≠ archive)
    (hsrc : ∀ r, src ≠ compiler r) (harchive : ∀ r, archive ≠ compiler r)
    (rg : LayReg t₀ → Fin T) (hrg : Function.Injective rg)
    (hsrcR : ∀ r, src ≠ rg r) (harchiveR : ∀ r, archive ≠ rg r)
    (hseparate : ∀ r key, compiler r ≠ elementarySharedTarget rg key)
    (hd : Fin 5 → Fin t₀) (pay : Fin t₀) (hhd : Function.Injective hd) (hpay : ∀ j, hd j ≠ pay)
    (hQ : swapStates hd pay hhd ≤ Q) (hT : swapT t₀ ≤ T) (saved : Fin T)
    (hcs : compiler .output ≠ saved) (hconfig : ∀ r, compiler .output ≠ rg r) (hsaved : ∀ r, saved ≠ rg r)
    (cfg : Fin 4 → Fin T) (work tmp ctmp : Fin T) (wb wm : ℕ)
    (hregs : ∀ key, [(elementarySharedJob rg cfg wb wm B (rows * 2 ^ n) key).src,
      elementarySharedTarget rg key, work, tmp, ctmp].Nodup)
    (hsources : ∀ key other, (elementarySharedJob rg cfg wb wm B (rows * 2 ^ n) key).src ≠ elementarySharedTarget rg other)
    (L Lb : ℕ) (hn : n < 2 ^ L) (hBin : B < 2 ^ Lb) (hnB : n ≤ B) (hrows : 0 < rows) (hB : 1 ≤ B)
    (rowBits : List Bool) (hrow : GrowingCounterData.Canonical rowBits) (hrowNe : rowBits ≠ [])
    (hrowValue : Counter.value rowBits = rows) (cs : List (ElementaryCoordinate n))
    (v : HS T Q (prime + K) U) (S : Stacks T (prime + K))
    (hcompileReady : ElementaryCompileReady compiler S.R n L Lb B rowBits)
    (data : ElementarySharedData cfg wb wm n B (rows * 2 ^ n) S.R)
    (hL : ∀ j, S.L j = []) (hempty : ∀ key, S.R (elementarySharedTarget rg key) = [])
    (hw : S.R work = []) (ht : S.R tmp = []) (hc : S.R ctmp = [])
    (hblank : ∀ r : LayReg t₀, r ≠ .ctrB → r ≠ .cnt → r ≠ .fld → r ≠ .mA →
      r ≠ .str → r ≠ .mB → (∀ j, r ≠ .sw j) → S.R (rg r) = [])
    (hmeta : ∀ key, S.R (elementaryConfigTarget rg hd key) = [])
    (hpay0 : S.R (rg (.sw (reg pay))) = [])
    (hprivate : ∀ j : Fin (swapT t₀), t₀ ≤ j.val → S.R (rg (.sw j)) = [])
    (hother : ∀ i, i ≠ pay → (∀ k, hd k ≠ i) → ∀ x ∈ S.R (rg (.sw (reg i))), x ≠ blank ∧ x.val < prime + 4)
    (hinput : S.R src = elementaryCoordinateFrames L cs) (harchive0 : S.R archive = [])
    (hconfig0 : S.R (compiler .output) = []) (hsaved0 : S.R saved = [])
    (l : List (List (Fin (prime + K + 4)))) (hl : l.length = rows * 2 ^ n)
    (hlB : ∀ r ∈ l, r.length = B) (h8 : ∀ r ∈ l, ∀ x ∈ r, x.val < 8)
    (hstream : S.R (rg .str) = l.flatten) :
    ∃ (ds : List (ElementaryInstruction n)) (v' : HS T Q (prime + K) U) (m : ℕ),
      ds.map (fun d => (d.target, d.source)) = cs.reverse.map ElementaryCoordinate.key ∧ v'.user = v.user ∧
      (m : ℝ) ≤ (6 * B + 6 * (rows * 2 ^ n) + 11 * wb + 11 * wm + 10 * n + 24 : ℕ) +
        ((cs.length : ℝ) *
          ((elementaryCompileBase n L Lb rowBits.length + 7 * (rowBits.length + 3 * n + Lb + 11) + 4 * L + 6 : ℕ) +
            elementaryBaseCost rg n rows B S + 2 +
            (12 * swapT t₀ + 22 : ℕ) * (rowBits.length + 3 * n + Lb + 11 : ℕ)) + 10) +
        (2 * B + 2 * (rows * 2 ^ n) + 4 * n + 9 : ℕ) ∧
      Exec body (elementarySharedProgram rg cfg work tmp ctmp wb wm B (rows * 2 ^ n)
        (compiledElementaryProgram compiler src archive rg hrg hd pay hhd hQ hT saved)) (mk v S) m
        (mk v' { S with R := Function.update S.R (rg .str) (moveRecs (elementaryInstructionsRank rows ds) l).flatten }) := by
  let jobs := elementarySharedJobs rg cfg wb wm B (rows * 2 ^ n)
  let bank := metadataInstalled S.R jobs
  let S₁ : Stacks T (prime + K) := { S with R := bank }
  have hkeep (j : Fin T) (hj : ∀ key, j ≠ elementarySharedTarget rg key) : S₁.R j = S.R j :=
    elementarySharedSetup_keep rg cfg wb wm B (rows * 2 ^ n) S.R j hj
  have hcompilerKeep (r : ElementaryCompilerReg) : S₁.R (compiler r) = S.R (compiler r) := hkeep _ (hseparate r)
  have hcompile₁ : ElementaryCompileReady compiler S₁.R n L Lb B rowBits :=
    hcompileReady.congr (fun r _ => hcompilerKeep r)
  have hroute₁ : ElementaryLoopReady rg hd pay S₁.R n rows B :=
    elementarySharedSetup_ready rg hrg hd pay cfg wb wm n rows B S.R data hblank hmeta hpay0 hprivate hother
  have hinput₁ : S₁.R src = elementaryCoordinateFrames L cs := by
    rw [hkeep]
    · exact hinput
    · intro key; fin_cases key <;> exact hsrcR _
  have harchive₁ : S₁.R archive = [] := by
    rw [hkeep]
    · exact harchive0
    · intro key; fin_cases key <;> exact harchiveR _
  have hsaved₁ : S₁.R saved = [] := by
    rw [hkeep]
    · exact hsaved0
    · intro key; fin_cases key <;> exact hsaved _
  have hstream₁ : S₁.R (rg .str) = l.flatten := by
    rw [hkeep]
    · exact hstream
    · intro key; fin_cases key <;> simp [elementarySharedTarget, hrg.eq_iff]
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := elementarySharedSetup_exec body rg hrg cfg work tmp ctmp
    wb wm n B (rows * 2 ^ n) hregs hsources v S data hempty hw ht hc
  obtain ⟨ds, v₂, m₂, hk, hu₂, hm₂, he₂⟩ := compiledElementary_exec body compiler hcompiler src archive hsa hsrc harchive
    rg hrg hd pay hhd hpay hQ hT saved hcs hconfig hsaved L Lb hn hBin hnB hrows hB rowBits hrow hrowNe hrowValue
    cs v₁ S₁ hcompile₁ hroute₁ hL hinput₁ harchive₁ ((hcompilerKeep .output).trans hconfig0) hsaved₁
    l hl hlB h8 hstream₁
  let out := (moveRecs (elementaryInstructionsRank rows ds) l).flatten
  let S₂ : Stacks T (prime + K) := { S₁ with R := Function.update S₁.R (rg .str) out }
  let keys := jobs.map MetadataJob.dst
  have hkeys : keys.Nodup := by
    simpa only [keys, jobs, elementarySharedJobs, List.map_map, Function.comp_def, elementarySharedJob_dst]
      using (List.nodup_finRange 4).map (elementarySharedTarget_injective rg hrg)
  have hstr : rg .str ∉ keys := by
    simp [keys, jobs, elementarySharedJobs, List.finRange_succ, elementarySharedJob, MetadataJob.dst, hrg.eq_iff]
  obtain ⟨v₃, hu₃, he₃⟩ := metadataClean_exec body keys hkeys v₂ S₂
  have hcost : metadataCleanCost S₂.R keys = metadataCleanCost bank keys := by
    apply metadataCleanCost_congr
    intro j hj
    have hne : j ≠ rg .str := by intro he; subst j; exact hstr hj
    exact Function.update_of_ne hne _ _
  have hfinal : metadataCleared S₂.R keys = Function.update S.R (rg .str) out :=
    elementarySharedSetup_restore rg hrg cfg wb wm B (rows * 2 ^ n) S.R out hempty
  have he₃' : Exec body (metadataClean keys) (mk v₂ S₂) (metadataCleanCost bank keys)
      (mk v₃ { S with R := Function.update S.R (rg .str) out }) := by
    simpa only [hcost, hfinal] using he₃
  have hbase : elementaryBaseCost rg n rows B S₁ = elementaryBaseCost rg n rows B S := by
    have hsw (j : Fin (swapT t₀)) : S₁.R (rg (.sw j)) = S.R (rg (.sw j)) := by
      apply hkeep
      intro key; fin_cases key <;> simp [elementarySharedTarget, hrg.eq_iff]
    simp only [elementaryBaseCost, hsw]
  rw [hbase] at hm₂
  rw [elementarySharedSetup_cost rg cfg wb wm n B (rows * 2 ^ n) S.R data] at hm₁
  have hm₁' : (m₁ : ℝ) ≤ (6 * B + 6 * (rows * 2 ^ n) + 11 * wb + 11 * wm + 10 * n + 24 : ℕ) := by
    exact_mod_cast hm₁
  have hclean : metadataCleanCost bank keys = 2 * B + 2 * (rows * 2 ^ n) + 4 * n + 9 :=
    elementarySharedSetup_cleanCost rg hrg cfg wb wm n B (rows * 2 ^ n) S.R data
  refine ⟨ds, v₃, m₁ + (m₂ + metadataCleanCost bank keys), hk, hu₃.trans (hu₂.trans hu₁), ?_,
    Exec.seq he₁ (Exec.seq he₂ he₃')⟩
  rw [hclean]
  simp only [Nat.cast_add] at hm₁' hm₂ ⊢
  linarith only [hm₁', hm₂]

end IntegerMultBounds.MathlibTM2.Routing
