module

public import IntegerMultBounds.MathlibTM2.Routing.SelectivePrepared
public import IntegerMultBounds.MathlibTM2.Node.CompactProg

/-!
# Complete selective host execution from prepared metadata

Every rotation and interchange is the concrete checked host program. Their exact
order is the existing well-formed gadget schedule. The complete execution restores
all prepared metadata and changes only the record stream, with the sum of all pass
costs charged. Setup and final metadata cleanup are not included in this boundary.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Layer.CompactDigits
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

variable (p : Par) (X : ℕ)
  (hG : 0 < p.G) (hK : 0 < p.K) (hGK : p.G < p.K)
  (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X)

def selectivePerm (R : ℕ) (o : {o : Op // o.WF}) :
    Equiv.Perm (Fin (R * 2 ^ fieldsLen (selectiveLen p X))) :=
  match o.1 with
  | .rotY neg off | .rotB neg off => rotPerm neg
      (selectiveOffset_high p X hG hK hGK active s off)
      (fieldOff_add_le_total (selectiveLen p X) (selectiveTgt off))
  | .swapT => selectiveSwapPerm p X R 0
  | .swapU => selectiveSwapPerm p X R 1

theorem selectivePerm_val (R : ℕ) (o : {o : Op // o.WF})
    (i : Fin (R * 2 ^ fieldsLen (selectiveLen p X))) :
    (selectivePerm p X hG hK hGK active s R o i : ℕ) =
      selectiveIdx p X active (fun y x => slotPhysicalRead s y x) o.1 i := by
  obtain ⟨o, ho⟩ := o
  cases o with
  | rotY neg off =>
    rcases ho with rfl | rfl <;> exact (selectiveRotation_idx p X active s _ neg i).symm
  | rotB neg off =>
    rcases ho with rfl | rfl | rfl <;> exact (selectiveRotation_idx p X active s _ neg i).symm
  | swapT => rfl
  | swapU => rfl

theorem selectiveListPerm_val (R : ℕ) (os : List {o : Op // o.WF})
    (i : Fin (R * 2 ^ fieldsLen (selectiveLen p X))) :
    (listPerm (selectivePerm p X hG hK hGK active s R) os i : ℕ) =
      selectiveRunIdx p X active (fun y x => slotPhysicalRead s y x) (os.map Subtype.val) i := by
  induction os generalizing i with
  | nil => rfl
  | cons o os ih =>
    change (listPerm (selectivePerm p X hG hK hGK active s R) os
      (selectivePerm p X hG hK hGK active s R o i) : ℕ) = _
    rw [ih, selectivePerm_val]
    rfl

/-- The actual composed rank permutation has the already checked physical endpoint. -/
theorem selectiveProgramPerm_good (R : ℕ) (hs : ∀ c, (s c).Allowed active)
    (i : Fin (R * 2 ^ fieldsLen (selectiveLen p X)))
    (hgood : Good p (selectiveView p X i)) :
    (listPerm (selectivePerm p X hG hK hGK active s R) progW i : ℕ) =
      setDigit (selectiveLen p X) 1
        ((selectiveView p X i).y ^^^ targetWord p active s
          (selectiveView p X i).y (selectiveView p X i).x) i := by
  rw [selectiveListPerm_val, progW_val]
  have hread : (fun y x => slotPhysicalRead s y x) = slotRead p active (slotSourcesRead active s) := by
    funext y x
    exact (slotRead_eq_physical active s hs y x).symm
  rw [hread]
  exact selectiveRunIdx_good p X active s hs i hgood hG (by omega)

variable {T Q K : ℕ} {P U : Type}

noncomputable def selectivePass (H : SelectiveHost T) (hH : H.Valid)
    (hQ : swapStates selectiveSwapHd selectiveSwapPay selectiveSwapHd_inj ≤ Q)
    (hT : swapT 6 ≤ T) : Op → Pr P T Q (prime + K) U
  | .rotY neg off | .rotB neg off =>
    headerRotate H.cf (H.cb off) (higherFields (selectiveTgt off)) (selectiveGate off) neg
      H.src H.dst H.aux H.out H.ctr H.tmp H.cnt H.ctmp
  | .swapT => swapPass selectiveSwapHd selectiveSwapPay selectiveSwapHd_inj hQ
      (H.swaps 0) (hH.swap_inj 0) hT H.src H.tmp
  | .swapU => swapPass selectiveSwapHd selectiveSwapPay selectiveSwapHd_inj hQ
      (H.swaps 1) (hH.swap_inj 1) hT H.src H.tmp

noncomputable def selectiveSwapCost (T R B bankLen : ℕ) : ℝ :=
  3 * swapConst * (T + 12 * swapT 6 + 5 : ℕ) *
    (R * 2 ^ fieldsLen (selectiveLen p X) * B : ℕ) *
      ((max 1 p.wc : ℕ) : ℝ) ^ Parameters.tau +
    (6 * bankLen + 34 * (R * 2 ^ fieldsLen (selectiveLen p X) * B) +
      2 * T + 6 * swapT 6 + 23 : ℕ)

/-- Dimension-only swap ledger retaining the compact field's exponent. -/
noncomputable def selectiveUniformSwapCost (T M B compactWidth bankLen : ℕ) : ℝ :=
  3 * swapConst * (T + 12 * swapT 6 + 5 : ℕ) * (M * B : ℕ) *
    ((max 1 compactWidth : ℕ) : ℝ) ^ Parameters.tau +
    (6 * bankLen + 34 * (M * B) + 2 * T + 6 * swapT 6 + 23 : ℕ)

theorem selectiveSwapCost_le (T R B bankLen bankBound n : ℕ)
    (hfields : fieldsLen (selectiveLen p X) = n) (hbank : bankLen ≤ bankBound) :
    selectiveSwapCost p X T R B bankLen ≤ selectiveUniformSwapCost T (R * 2 ^ n) B p.wc bankBound := by
  unfold selectiveSwapCost selectiveUniformSwapCost
  rw [hfields]
  refine add_le_add (le_refl _) ?_
  exact_mod_cast (show 6 * bankLen + 34 * (R * 2 ^ n * B) + 2 * T + 6 * swapT 6 + 23 ≤
    6 * bankBound + 34 * (R * 2 ^ n * B) + 2 * T + 6 * swapT 6 + 23 by omega)

noncomputable def selectiveOpCost (T R B : ℕ) (bankLen : Fin 2 → ℕ) : Op → ℝ
  | .rotY _ off | .rotB _ off =>
    classMoveCost (nd := 2) (selectiveRotationCost p X off) (selectiveRotationCost p X off)
      (R * 2 ^ fieldsLen (selectiveLen p X)) B (selectiveLen p X)
  | .swapT => selectiveSwapCost p X T R B (bankLen 0)
  | .swapU => selectiveSwapCost p X T R B (bankLen 1)

/-- Charge the actual schedule: four A rotations, two of each other rotation,
eight b/t interchanges and four b/u interchanges. -/
theorem selectiveCost_sum (T R B : ℕ) (bankLen : Fin 2 → ℕ) :
    (progW.map (fun o => selectiveOpCost p X T R B bankLen o.1)).sum =
      4 * selectiveOpCost p X T R B bankLen (.rotY false .A) +
      2 * selectiveOpCost p X T R B bankLen (.rotY false .Z) +
      2 * selectiveOpCost p X T R B bankLen (.rotB false .Y) +
      2 * selectiveOpCost p X T R B bankLen (.rotB true .YZ) +
      2 * selectiveOpCost p X T R B bankLen (.rotB false .X) +
      8 * selectiveOpCost p X T R B bankLen .swapT +
      4 * selectiveOpCost p X T R B bankLen .swapU := by
  simp [progW, prog, E, selectiveOpCost]
  ring

/-- The actual schedule has twelve bounded rotations and twelve compact swaps. -/
theorem selectiveCost_sum_le (T R B n bankBound : ℕ) (bankLen : Fin 2 → ℕ)
    (hfields : fieldsLen (selectiveLen p X) = n) (hbank : ∀ c, bankLen c ≤ bankBound) :
    (progW.map (fun o => selectiveOpCost p X T R B bankLen o.1)).sum ≤
      12 * (selectiveUniformRotationCost n (R * 2 ^ n) B : ℕ) +
      12 * selectiveUniformSwapCost T (R * 2 ^ n) B p.wc bankBound := by
  have hr (off : Off) : (classMoveCost (nd := 2) (selectiveRotationCost p X off) (selectiveRotationCost p X off)
      (R * 2 ^ fieldsLen (selectiveLen p X)) B (selectiveLen p X) : ℝ) ≤
      (selectiveUniformRotationCost n (R * 2 ^ n) B : ℕ) := by
    exact_mod_cast selectiveRotationPassCost_le p X n R B hfields off
  have hA := hr .A
  have hZ := hr .Z
  have hY := hr .Y
  have hYZ := hr .YZ
  have hX := hr .X
  have h₀ := selectiveSwapCost_le p X T R B (bankLen 0) bankBound n hfields (hbank 0)
  have h₁ := selectiveSwapCost_le p X T R B (bankLen 1) bankBound n hfields (hbank 1)
  rw [selectiveCost_sum]
  simp only [selectiveOpCost]
  linarith only [hA, hZ, hY, hYZ, hX, h₀, h₁]

def selectiveSwapValues (R B : ℕ) (c : Fin 2) (k : Fin 5) : ℕ :=
  swapValues
    (swapDimsIdx (len := selectiveLen p X) 0 (selectiveSwapFld c) p.wc R
      (fieldsLen (selectiveLen p X)) B).1
    (swapDimsIdx (len := selectiveLen p X) 0 (selectiveSwapFld c) p.wc R
      (fieldsLen (selectiveLen p X)) B).2.1
    (swapDimsIdx (len := selectiveLen p X) 0 (selectiveSwapFld c) p.wc R
      (fieldsLen (selectiveLen p X)) B).2.2 p.wc p.wc k

/-- Each pass is supplied by its concrete executed rotation or interchange. -/
theorem selectivePass_exec (body : P → Pr P T Q (prime + K) U)
    (H : SelectiveHost T) (hH : H.Valid)
    (hQ : swapStates selectiveSwapHd selectiveSwapPay selectiveSwapHd_inj ≤ Q)
    (hT : swapT 6 ≤ T) {R B : ℕ} (hR : 0 < R) (hB : 1 ≤ B)
    (hs : Fin 2 → Fin 5 → List Bool)
    (hv : ∀ c k, Counter.value (hs c k) = selectiveSwapValues p X R B c k)
    (hc : ∀ c k, GrowingCounterData.Canonical (hs c k))
    (S₀ : Stacks T (prime + K))
    (hS : SelectivePrepared p X H hG hK active s B (R * 2 ^ fieldsLen (selectiveLen p X)) hs S₀)
    (o : {o : Op // o.WF}) (l : List (List (Fin (prime + K + 4))))
    (hl : l.length = R * 2 ^ fieldsLen (selectiveLen p X))
    (hlB : ∀ r ∈ l, r.length = B ∧ ∀ a ∈ r, a.val < 8) (v : HS T Q (prime + K) U) :
    ∃ (v' : HS T Q (prime + K) U) (m : ℕ), v'.user = v.user ∧
      (m : ℝ) ≤ selectiveOpCost p X T R B (fun c => ∑ j, (S₀.R (H.swaps c j)).length) o.1 ∧
      Exec body (selectivePass H hH hQ hT o.1)
        (mk v { S₀ with R := Function.update S₀.R H.src l.flatten }) m
        (mk v' { S₀ with R := Function.update S₀.R H.src (moveRecs (selectivePerm p X hG hK hGK active s R o) l).flatten }) := by
  have hS' := SelectivePrepared.update p X H hG hK active s hH hS l.flatten
  have hlen : ∀ r ∈ l, r.length = B := fun r hr => (hlB r hr).1
  have h8 : ∀ r ∈ l, ∀ a ∈ r, a.val < 8 := fun r hr => (hlB r hr).2
  have hswap (c : Fin 2) : ∃ (v' : HS T Q (prime + K) U) (m : ℕ), v'.user = v.user ∧
      (m : ℝ) ≤ selectiveSwapCost p X T R B (∑ j, (S₀.R (H.swaps c j)).length) ∧
      Exec body (swapPass selectiveSwapHd selectiveSwapPay selectiveSwapHd_inj hQ
        (H.swaps c) (hH.swap_inj c) hT H.src H.tmp)
        (mk v { S₀ with R := Function.update S₀.R H.src l.flatten }) m
        (mk v' { S₀ with R := Function.update S₀.R H.src (moveRecs (selectiveSwapPerm p X R c) l).flatten }) := by
    obtain ⟨v', m, hu, hm, he⟩ := selectiveSwap_exec p X body c hQ (H.swaps c) (hH.swap_inj c)
      hT H.src H.tmp (SelectiveHost.Valid.tmp_src H hH).symm (hH.swap_src c) (hH.swap_tmp c)
      hR (by omega) l hl hlen h8 (hs c) (hv c) (hc c) v _ hS'.left (by simp) hS'.tmp
      (hS'.pay c) (hS'.priv c) (hS'.hdr c)
    refine ⟨v', m, hu, ?_, Exec.cast he rfl (by simp)⟩
    simpa [selectiveSwapCost, hH.swap_src] using hm
  obtain ⟨o, ho⟩ := o
  cases o with
  | rotY neg off | rotB neg off =>
    obtain ⟨v', m, hu, hm, he⟩ := selectiveRotate_exec p X body hG hK hGK active s off neg
      (hH.callback off) (hH.move off) hB hl hlen hS'.ctr hS'.cnt v _ (by simp) rfl rfl
      hS'.tmp hS'.ctmp hS'.out hS'.dst hS'.aux (hS'.inv off)
    exact ⟨v', m, hu, by dsimp only [selectiveOpCost]; exact_mod_cast hm,
      Exec.cast he rfl (by simp [selectivePerm])⟩
  | swapT => exact hswap 0
  | swapU => exact hswap 1

/-- One complete host execution of all twelve rotations and twelve interchanges.
Prepared metadata is restored, and the same composed permutation has the physical
endpoint in `selectiveProgramPerm_good`. Setup remains outside this theorem. -/
theorem selectivePrepared_exec (body : P → Pr P T Q (prime + K) U)
    (H : SelectiveHost T) (hH : H.Valid)
    (hQ : swapStates selectiveSwapHd selectiveSwapPay selectiveSwapHd_inj ≤ Q)
    (hT : swapT 6 ≤ T) {R B : ℕ} (hR : 0 < R) (hB : 1 ≤ B)
    (hs : Fin 2 → Fin 5 → List Bool)
    (hv : ∀ c k, Counter.value (hs c k) = selectiveSwapValues p X R B c k)
    (hc : ∀ c k, GrowingCounterData.Canonical (hs c k))
    (S₀ : Stacks T (prime + K))
    (hS : SelectivePrepared p X H hG hK active s B (R * 2 ^ fieldsLen (selectiveLen p X)) hs S₀)
    (l : List (List (Fin (prime + K + 4))))
    (hl : l.length = R * 2 ^ fieldsLen (selectiveLen p X))
    (hlB : ∀ r ∈ l, r.length = B ∧ ∀ a ∈ r, a.val < 8) (v : HS T Q (prime + K) U) :
    ∃ (v' : HS T Q (prime + K) U) (m : ℕ), v'.user = v.user ∧
      (m : ℝ) ≤ (progW.map (fun o => selectiveOpCost p X T R B
        (fun c => ∑ j, (S₀.R (H.swaps c j)).length) o.1)).sum + 1 ∧
      Exec body (Prog.seqList (progW.map (fun o => selectivePass H hH hQ hT o.1)))
        (mk v { S₀ with R := Function.update S₀.R H.src l.flatten }) m
        (mk v' { S₀ with R := Function.update S₀.R H.src (moveRecs (listPerm (selectivePerm p X hG hK hGK active s R) progW) l).flatten }) := by
  apply seqList_moveRecs body (fun o => selectivePass H hH hQ hT o.1)
    (selectivePerm p X hG hK hGK active s R)
    (fun o => selectiveOpCost p X T R B (fun c => ∑ j, (S₀.R (H.swaps c j)).length) o.1)
    H.src S₀ (fun r => r.length = B ∧ ∀ a ∈ r, a.val < 8) progW
  · intro o _ l hl hlB v
    exact selectivePass_exec p X hG hK hGK active s body H hH hQ hT hR hB hs hv hc S₀ hS o l hl hlB v
  · exact hl
  · exact hlB

end IntegerMultBounds.MathlibTM2.Routing
