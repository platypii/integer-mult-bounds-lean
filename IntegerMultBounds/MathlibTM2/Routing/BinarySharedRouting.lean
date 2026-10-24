module

public import IntegerMultBounds.MathlibTM2.Routing.CompiledSharedRouting
public import IntegerMultBounds.MathlibTM2.Routing.SharedInputProgram

/-! Terminal routing with executed shared-input generation from binary dimensions. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

variable {t₀ T Q K : ℕ} {P U : Type}

theorem binarySharedRouting_exec {n rows B : ℕ}
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
    (input : SharedInputReg → Fin T) (hinputReg : Function.Injective input)
    (hcompilerInput : ∀ r, compiler r ∉ sharedInputPrivate input)
    (hrouterInput : ∀ r, rg r ∉ sharedInputPrivate input)
    (hsrcInput : src ∉ sharedInputPrivate input) (harchiveInput : archive ∉ sharedInputPrivate input)
    (hsavedInput : saved ∉ sharedInputPrivate input)
    (work tmp ctmp : Fin T)
    (hworkInput : work ∉ sharedInputPrivate input) (htmpInput : tmp ∉ sharedInputPrivate input)
    (hctmpInput : ctmp ∉ sharedInputPrivate input)
    (wb wm : ℕ)
    (cfg : Fin 4 → Fin T) (hcfg : cfg = sharedInputConfig input)
    (hregs : ∀ key, [(elementarySharedJob rg cfg wb wm B (rows * 2 ^ n) key).src,
      elementarySharedTarget rg key, work, tmp, ctmp].Nodup)
    (hsources : ∀ key other, (elementarySharedJob rg cfg wb wm B (rows * 2 ^ n) key).src ≠ elementarySharedTarget rg other)
    (L Lb : ℕ) (hwb : wb = Lb) (hn0 : 0 < n) (hn : n < 2 ^ L) (hBin : B < 2 ^ Lb) (hnB : n ≤ B) (hrows : 0 < rows) (hB : 1 ≤ B)
    (rowBits : List Bool) (hrow : GrowingCounterData.Canonical rowBits) (hrowNe : rowBits ≠ [])
    (hrowValue : Counter.value rowBits = rows) (cs : List (ElementaryCoordinate n))
    (v : HS T Q (prime + K) U) (S : Stacks T (prime + K))
    (hcompileReady : ElementaryCompileReady compiler S.R n L Lb B rowBits)
    (hwm : wm = n + rowBits.length)
    (hwidthInput : S.R (input .width) = binSyms L n)
    (hrowsInput : S.R (input .rows) = rowBits.map bitSymbol)
    (hblockInput : S.R (input .block) = binSyms Lb B)
    (hfieldInput : S.R (input .field) = []) (hrecordsInput : S.R (input .records) = [])
    (hmaskInput : S.R (input .mask) = []) (hscratchInput : ∀ i, S.R (input (.scratch i)) = [])
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
      (m : ℝ) ≤ (L * (4 * n + 11) + 22 * n + 6 * rowBits.length + 46 : ℕ) + ((6 * B + 6 * (rows * 2 ^ n) + 11 * wb + 11 * wm + 10 * n + 24 : ℕ) +
        ((cs.length : ℝ) *
          ((elementaryCompileBase n L Lb rowBits.length + 7 * (rowBits.length + 3 * n + Lb + 11) + 4 * L + 6 : ℕ) +
            elementaryBaseCost rg n rows B S + 2 +
            (12 * swapT t₀ + 22 : ℕ) * (rowBits.length + 3 * n + Lb + 11 : ℕ)) + 10) +
        (2 * B + 2 * (rows * 2 ^ n) + 4 * n + 9 : ℕ)) +
        (6 * n + 2 * rowBits.length + 7 : ℕ) ∧
      Exec body (sharedInputRoutingProgram input (elementarySharedProgram rg cfg work tmp ctmp wb wm B (rows * 2 ^ n)
        (compiledElementaryProgram compiler src archive rg hrg hd pay hhd hQ hT saved))) (mk v S) m
        (mk v' { S with R := Function.update S.R (rg .str) (moveRecs (elementaryInstructionsRank rows ds) l).flatten }) := by
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := sharedInput_exec body input hinputReg L n rows hn hn0
    rowBits hrowValue v S hwidthInput hrowsInput hfieldInput hrecordsInput hmaskInput hscratchInput
  let S₁ : Stacks T (prime + K) := { S with R := sharedInputBank S.R input n rows rowBits.length }
  have hkeep (j : Fin T) (hj : j ∉ sharedInputPrivate input) : S₁.R j = S.R j :=
    sharedInputBank_keep S.R input n rows rowBits.length j hj
  have hcomp (r : ElementaryCompilerReg) : S₁.R (compiler r) = S.R (compiler r) := hkeep _ (hcompilerInput r)
  have hroute (r : LayReg t₀) : S₁.R (rg r) = S.R (rg r) := hkeep _ (hrouterInput r)
  have data : ElementarySharedData cfg wb wm n B (rows * 2 ^ n) S₁.R := by
    subst cfg; subst wb; subst wm
    exact sharedInputBank_data S.R input hinputReg Lb n rows B rowBits hrowValue hBin hblockInput
  obtain ⟨ds, v₂, m₂, hk, hu₂, hm₂, he₂⟩ := compiledSharedRouting_exec body compiler hcompiler
    src archive hsa hsrc harchive rg hrg hsrcR harchiveR hseparate hd pay hhd hpay hQ hT saved
    hcs hconfig hsaved cfg work tmp ctmp wb wm hregs hsources L Lb hn hBin hnB hrows hB
    rowBits hrow hrowNe hrowValue cs v₁ S₁
    (hcompileReady.congr (fun r _ => hcomp r)) data hL
    (by intro key; simpa only [elementarySharedTarget, hroute] using hempty key)
    ((hkeep work hworkInput).trans hw) ((hkeep tmp htmpInput).trans ht) ((hkeep ctmp hctmpInput).trans hc)
    (by simpa only [hroute] using hblank) (by
      intro key
      have hk := hmeta key
      unfold elementaryConfigTarget at hk ⊢
      split <;> rename_i h <;> simpa [h, hroute] using hk)
    (by simpa only [hroute] using hpay0) (by simpa only [hroute] using hprivate)
    (by simpa only [hroute] using hother)
    ((hkeep src hsrcInput).trans hinput) ((hkeep archive harchiveInput).trans harchive0)
    ((hcomp .output).trans hconfig0) ((hkeep saved hsavedInput).trans hsaved0)
    l hl hlB h8 ((hroute .str).trans hstream)
  let out := (moveRecs (elementaryInstructionsRank rows ds) l).flatten
  let S₂ : Stacks T (prime + K) := { S₁ with R := Function.update S₁.R (rg .str) out }
  obtain ⟨v₃, hu₃, he₃⟩ := metadataClean_exec body (sharedInputPrivate input)
    (by simp [sharedInputPrivate, List.nodup_cons, hinputReg.eq_iff]) v₂ S₂
  have hcost : metadataCleanCost S₂.R (sharedInputPrivate input) = 6 * n + 2 * rowBits.length + 7 := by
    trans metadataCleanCost S₁.R (sharedInputPrivate input)
    · apply metadataCleanCost_congr
      intro j hj
      have hne : j ≠ rg .str := by intro he; subst j; exact hrouterInput .str hj
      exact Function.update_of_ne hne _ _
    · exact sharedInput_cleanCost S.R input hinputReg n rows rowBits.length
  have hfinal : metadataCleared S₂.R (sharedInputPrivate input) = Function.update S.R (rg .str) out :=
    sharedInput_restore S.R input hinputReg n rows rowBits.length (rg .str) out
      (hrouterInput .str) hrecordsInput hfieldInput hmaskInput
  rw [hcost, hfinal] at he₃
  have hbase : elementaryBaseCost rg n rows B S₁ = elementaryBaseCost rg n rows B S := by
    simp only [elementaryBaseCost, hroute]
  rw [hbase] at hm₂
  refine ⟨ds, v₃, m₁ + (m₂ + (6 * n + 2 * rowBits.length + 7)), hk,
    hu₃.trans (hu₂.trans hu₁), ?_, Exec.seq he₁ (Exec.seq he₂ he₃)⟩
  have hm₁' : (m₁ : ℝ) ≤ (L * (4 * n + 11) + 22 * n + 6 * rowBits.length + 46 : ℕ) := by
    exact_mod_cast hm₁
  simp only [Nat.cast_add] at hm₁' hm₂ ⊢
  linarith only [hm₁', hm₂]

end IntegerMultBounds.MathlibTM2.Routing
