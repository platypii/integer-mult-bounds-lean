module

public import IntegerMultBounds.MathlibTM2.Routing.CompactPatternTable
public import IntegerMultBounds.MathlibTM2.Routing.RepairDescriptorBank

/-! The compact compiler's concrete patterns for all eleven repair descriptors.
Compact inputs still require executed generation from the sparse profiles. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget IntegerMultBounds.MathlibTM2.Layer.CompactDigits

noncomputable section

def repairCompactRows (p : Par) : RepairDescriptorKey → ℕ
  | none => p.wy
  | some (off, _) => selectiveTargetWidth p off

def repairCompactSourceWidth (p : Par) (X : ℕ) : RepairDescriptorKey → ℕ
  | none => p.wy + 2 * p.wc + X
  | some (off, _) => selectiveSourceWidth p X off

theorem repairCompactRows_le_fields (p : Par) (X : ℕ) (key : RepairDescriptorKey) :
    repairCompactRows p key ≤ fieldsLen (selectiveLen p X) := by
  cases key with
  | none => simp [repairCompactRows, fieldsLen, selectiveLen, Fin.sum_univ_succ]; omega
  | some pair =>
    obtain ⟨off, k⟩ := pair
    cases off <;> simp [repairCompactRows, selectiveTargetWidth, fieldsLen, selectiveLen, Fin.sum_univ_succ] <;> omega

theorem repairCompactSourceWidth_le_fields (p : Par) (X : ℕ) (key : RepairDescriptorKey) :
    repairCompactSourceWidth p X key ≤ fieldsLen (selectiveLen p X) := by
  cases key with
  | none => simp [repairCompactSourceWidth, fieldsLen, selectiveLen, Fin.sum_univ_succ]; omega
  | some pair =>
    obtain ⟨off, k⟩ := pair
    cases off <;> simp [repairCompactSourceWidth, selectiveSourceWidth, fieldsLen, selectiveLen, Fin.sum_univ_succ] <;> omega

variable (p : Par) (X : ℕ) (hG : 0 < p.G) (hK : 0 < p.K)
  (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X) (key : RepairDescriptorKey)

def repairCompactPattern : (key : RepairDescriptorKey) →
    Fin (repairCompactRows p key) → Option (Fin (repairCompactSourceWidth p X key))
  | none => selectiveKeyPattern p X active s
  | some (off, k) => selectivePatterns p X hG hK active s off k

theorem repairCompactPattern_word {A : ℕ} :
    (patternTable (repairCompactPattern p X hG hK active s key)).flatten.map (bitSymbol (a := A)) =
      repairDescriptorWord p X hG hK active s key := by
  cases key with
  | none => rfl
  | some pair => cases pair; rfl

theorem repairLiveDescriptorWord_length {A : ℕ} :
    (repairDescriptorWord (A := A) p X hG hK active s key).length =
      repairCompactRows p key * (repairCompactSourceWidth p X key + 1) := by
  rw [← repairCompactPattern_word p X hG hK active s key]
  simp only [List.length_map, patternTable, sourceTable_size, List.length_ofFn]

theorem repairDescriptorWord_length_le {A : ℕ} (n : ℕ)
    (hfields : fieldsLen (selectiveLen p X) = n) :
    (repairDescriptorWord (A := A) p X hG hK active s key).length ≤ n * (n + 1) := by
  rw [repairLiveDescriptorWord_length]
  exact Nat.mul_le_mul ((repairCompactRows_le_fields p X key).trans_eq hfields)
    (Nat.add_le_add_right ((repairCompactSourceWidth_le_fields p X key).trans_eq hfields) 1)

theorem repairSetupPayload_length_le {A : ℕ} (rb R B n headerWidth : ℕ)
    (hfields : fieldsLen (selectiveLen p X) = n) (headers : Fin 2 → Fin 5 → List Bool)
    (hheaders : ∀ c k, (headers c k).length ≤ headerWidth) (setupKey : RepairSetupKey) :
    (repairSetupPayload (A := A) p X rb hG hK active s R B headers setupKey).length ≤
      n * (n + 1) + (n + rb + B) + R * 2 ^ n + headerWidth + 2 := by
  have htotal := hfields
  simp [fieldsLen, selectiveLen, Fin.sum_univ_succ] at htotal
  have hkey : fieldsLen (selectiveKeyLen p X rb) = n + rb := by
    rw [selectiveKeyWidth, hfields]
  cases setupKey with
  | inl setupKey =>
    cases setupKey with
    | field f =>
      simp only [repairSetupPayload, setupPayload, length_binSyms]
      fin_cases f <;> simp [selectiveLen] <;> omega
    | desc off k =>
      have hd := repairDescriptorWord_length_le (A := A) p X hG hK active s (some (off, k)) n hfields
      change (repairDescriptorWord (A := A) p X hG hK active s (some (off, k))).length ≤ _
      omega
    | block => simp only [repairSetupPayload, setupPayload, List.length_replicate, hkey]; omega
    | records => simp only [repairSetupPayload, setupPayload, List.length_replicate, hfields]; omega
    | header c k =>
      have hh := hheaders c k
      simp only [repairSetupPayload, setupPayload, List.length_cons, List.length_map]
      omega
  | inr setupKey =>
    have hd := repairDescriptorWord_length_le (A := A) p X hG hK active s none n hfields
    cases setupKey <;>
      simp only [repairSetupPayload, repairExtraPayload, length_binSyms, List.length_replicate, hkey]
    all_goals first | omega | (change (repairDescriptorWord (A := A) p X hG hK active s none).length ≤ _; omega)

theorem repairSetupSource_length_le {A : ℕ} (rb wb wm wp wk R B n width : ℕ)
    (hfields : fieldsLen (selectiveLen p X) = n) (headers : Fin 2 → Fin 5 → List Bool)
    (bank : Fin repairT → List (Fin (A + 4)))
    (data : RepairSetupData p X rb hG hK active s wb wm wp wk R B headers bank)
    (hheaders : ∀ c k, (headers c k).length ≤ width) (setupKey : RepairSetupKey) :
    (bank (repairSetupSource setupKey)).length ≤
      n * (n + 1) + n + rb + width + wb + wm + wp + wk + 1 := by
  have htotal := hfields
  simp [fieldsLen, selectiveLen, Fin.sum_univ_succ] at htotal
  cases setupKey with
  | inl setupKey =>
    change (bank (repairRoutingConfig setupKey)).length ≤ _
    cases setupKey with
    | field f =>
      rw [data.routing.widths f]
      fin_cases f <;> simp [selectiveLen] <;> omega
    | desc off k =>
      rw [data.routing.desc off k]
      have hd := repairDescriptorWord_length_le (A := A) p X hG hK active s (some (off, k)) n hfields
      change (repairDescriptorWord (A := A) p X hG hK active s (some (off, k))).length ≤ _
      omega
    | block => rw [data.routing.block, length_binSyms]; omega
    | records => rw [data.routing.records, length_binSyms]; omega
    | header c k =>
      rw [data.routing.headers c k, List.length_map]
      have hh := hheaders c k
      omega
  | inr setupKey =>
    cases setupKey with
    | row => rw [data.row]; omega
    | keyDescriptor =>
      rw [data.descriptor]
      have hd := repairDescriptorWord_length_le (A := A) p X hG hK active s none n hfields
      change (repairDescriptorWord (A := A) p X hG hK active s none).length ≤ _
      omega
    | keyMask => rw [data.keyMask, length_binSyms]; omega
    | badMask => rw [data.badMask, length_binSyms]; omega
    | badPhase => rw [data.badPhase, length_binSyms]; omega
    | payload => rw [data.payload, length_binSyms]; omega
    | keyLength => rw [data.keyLength, length_binSyms]; omega

theorem repairSetupInstallCost_le {A : ℕ} (rb wb wm wp wk R B n width : ℕ)
    (hfields : fieldsLen (selectiveLen p X) = n) (headers : Fin 2 → Fin 5 → List Bool)
    (bank : Fin repairT → List (Fin (A + 4)))
    (data : RepairSetupData p X rb hG hK active s wb wm wp wk R B headers bank)
    (hheaders : ∀ c k, (headers c k).length ≤ width) :
    let wordBound := n * (n + 1) + n + rb + width + wb + wm + wp + wk + 1
    let widthBound := wb + wm + wp + wk
    let valueBound := n + rb + B + R * 2 ^ n
    metadataInstallCost bank (repairSetupJobs wb wm wp wk
      (fieldsLen (selectiveKeyLen p X rb) + B) (R * 2 ^ fieldsLen (selectiveLen p X))
      B (fieldsLen (selectiveKeyLen p X rb))) ≤
      34 * (6 * wordBound + 7 + widthBound * (4 * valueBound + 11) + 2 * valueBound + 6) + 1 := by
  have hk : fieldsLen (selectiveKeyLen p X rb) = n + rb := by
    rw [selectiveKeyWidth, hfields]
  dsimp only
  apply repairSetupJobsCost_le
  · exact fun setupKey => repairSetupSource_length_le p X hG hK active s
      rb wb wm wp wk R B n width hfields headers bank data hheaders setupKey
  all_goals first | omega | (rw [hfields]; omega)

variable {T Q A : ℕ} {P U : Type}

theorem repairCompactPattern_exec (body : P → Pr P T Q A U)
    (zero : BinaryZeroReg → Fin T) (hzero : Function.Injective zero)
    (runs : SelectorRunReg → Fin T) (hruns : Function.Injective runs) (hblockReg : zero .dst = runs .block)
    (mask : BinaryMaskReg → Fin T) (hmask : Function.Injective mask)
    (saved out : Fin T) (hss : runs .dst ≠ saved) (hso : runs .dst ≠ out) (hao : saved ≠ out)
    (hsrcMask : ∀ r, runs .dst ≠ mask r) (hsavedMask : ∀ r, saved ≠ mask r) (houtMask : ∀ r, out ≠ mask r)
    (Lw Lg L : ℕ) (hL : L < 2 ^ Lw) (hW : repairCompactSourceWidth p X key + 1 < 2 ^ L)
    (hsize : repairCompactRows p key < 2 ^ Lg)
    (v : HS T Q A U) (S : Stacks T A)
    (hwidth : S.R (zero .width) = binSyms Lw L) (hunary : S.R (zero .unary) = [])
    (hscratch : ∀ i, S.R (zero (.scratch i)) = [])
    (hinput : S.R (runs .src) = selectorRunFrames Lg L (SparseSelectorRun.compress (List.ofFn (patternIndex (repairCompactPattern p X hG hK active s key))).reverse).reverse)
    (harchive : S.R (runs .archive) = []) (hblock : S.R (runs .block) = []) (hselectors : S.R (runs .dst) = [])
    (hblank : ∀ r, r ≠ .src → r ≠ .archive → r ≠ .block → r ≠ .dst → S.R (runs r) = [])
    (hready : DescriptorCompileReady mask S.R L (repairCompactSourceWidth p X key + 1)) (hsaved : S.R saved = []) :
    ∃ (v' : HS T Q A U) (steps : ℕ), v'.user = v.user ∧
      steps ≤ ((Lw * (4 * L + 11) + 8 * L + 13) + selectorRunLoopCost Lg L (SparseSelectorRun.compress (List.ofFn (patternIndex (repairCompactPattern p X hG hK active s key))).reverse).reverse +
        2 * (selectorRunFrames (A := A) Lg L (SparseSelectorRun.compress (List.ofFn (patternIndex (repairCompactPattern p X hG hK active s key))).reverse).reverse).length + 3 + (2 * (L + 1) + 2)) +
        (repairCompactRows p key * (descriptorCompileCallCost L (repairCompactSourceWidth p X key + 1) + 2) + 2 * (repairCompactRows p key * (L + 1)) + 4) +
        (2 * (repairCompactRows p key * (L + 1)) + 2) ∧
      Exec body (compactDescriptorProgram zero runs mask saved out) (mk v S) steps
        (mk v' { S with R := Function.update S.R out (repairDescriptorWord p X hG hK active s key ++ S.R out) }) := by
  obtain ⟨v', steps, hu, ht, he⟩ := compactPatternTable_exec body zero hzero runs hruns hblockReg mask hmask
    saved out hss hso hao hsrcMask hsavedMask houtMask Lw Lg L hL hW
    (repairCompactPattern p X hG hK active s key) hsize v S hwidth hunary hscratch
    hinput harchive hblock hselectors hblank hready hsaved
  rw [repairCompactPattern_word] at he
  exact ⟨v', steps, hu, ht, he⟩

end
end IntegerMultBounds.MathlibTM2.Routing
