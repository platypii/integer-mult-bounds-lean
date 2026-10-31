module

public import IntegerMultBounds.MathlibTM2.Host.PlacedSwapMachineStock
public import IntegerMultBounds.MathlibTM2.Host.StackLoopsStock

/-! The complete placed swap, including setup and normalization, retains the
existing exact endpoint and time bound with linear-volume stock throughout. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Host
noncomputable section
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast.Main
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

theorem placedSwapProg_run_within {t₀ T Q K : ℕ} {U F : Type} (body : F → Pr F T Q (prime + K) U)
    (hd : Fin 5 → Fin t₀) (pay : Fin t₀) (hi : Function.Injective hd)
    (hQ : swapStates hd pay hi ≤ Q)
    (ι : Fin (swapT t₀) → Fin T) (hι : Function.Injective ι) (hT : swapT t₀ ≤ T)
    (P G B h d : ℕ) (hs : Fin 5 → List Bool) (hhd : h ≤ d + 1) (hdh : d ≤ h + 1)
    (hv : ∀ k, Counter.value (hs k) = swapValues P G B h d k)
    (hc : ∀ k, GrowingCounterData.Canonical (hs k)) (hP : 0 < P) (hG : 0 < G) (hB : 0 < B)
    (x : Fin (BinaryAdjacentWidthInterchange.volume P (2 ^ h) G (2 ^ d) B) → Bool)
    (v : HS T Q (prime + K) U) (S : Stacks T (prime + K))
    (hL : ∀ j, S.L (ι j) = [])
    (hpriv : ∀ j : Fin (swapT t₀), t₀ ≤ j.val → S.R (ι j) = [])
    (hhdr : ∀ k, S.R (ι (reg (hd k))) = separator :: (hs k).map bitSymbol)
    (hpay : S.R (ι (reg pay)) = List.ofFn fun i => bitSymbol (x i))
    (hother : ∀ i, i ≠ pay → (∀ k, hd k ≠ i) →
      ∀ s ∈ S.R (ι (reg i)), s ≠ blank ∧ s.val < prime + 4) (depth : ℕ) :
    ∃ v' m, v'.user = v.user ∧
      m ≤ (T + 12 * swapT t₀ + 5) * swapCost P G B h d hs +
        6 * ∑ j, (S.R (ι j)).length + 2 * T + 6 * swapT t₀ + 15 ∧
      ExecWithin body (fun z c => mnSize c+z ≤ mnSize (mk v S)+depth+
        T*(2*SwapMachineStock.reserve P G B h d+2)+3*T+20) depth (placedSwapProg hd pay hi hQ ι hι hT) (mk v S) m
        (mk v' { S with
          L := fun y => if y ∈ List.ofFn ι then [] else S.L y
          R := Function.update S.R (ι (reg pay))
            (List.ofFn fun z => bitSymbol (BinaryAdjacentWidthInterchange.transpose x z)) }) := by
  classical
  set e := Alphabet.widen prime K with he_def
  set pe := swapPlacement ι hι hT with hpe
  -- every placed register holds non-blank symbols of the vendored alphabet
  have hgood : ∀ j, ∀ s ∈ S.R (ι j), s ≠ blank ∧ s.val < prime + 4 := by
    intro j s hs'
    by_cases hj : j.val < t₀
    · have hji : j = reg (⟨j.val, hj⟩ : Fin t₀) := Fin.ext rfl
      rw [hji] at hs'
      by_cases hip : (⟨j.val, hj⟩ : Fin t₀) = pay
      · rw [hip, hpay, List.mem_ofFn] at hs'
        obtain ⟨z, rfl⟩ := hs'
        exact bitSymbol_good _
      · by_cases hk : ∃ k, hd k = ⟨j.val, hj⟩
        · obtain ⟨k, hk⟩ := hk
          rw [← hk, hhdr k] at hs'
          simp only [List.mem_cons, List.mem_map] at hs'
          rcases hs' with rfl | ⟨b, _, rfl⟩
          · exact separator_good
          · exact bitSymbol_good _
        · exact hother _ hip (fun k hk' => hk ⟨k, hk'⟩) s hs'
    · rw [hpriv j (by omega)] at hs'
      simp at hs'
  -- the payload register is not a header register
  have hpay_hd : ∀ k, hd k ≠ pay := by
    intro k hk
    have hvol : 0 < BinaryAdjacentWidthInterchange.volume P (2 ^ h) G (2 ^ d) B := by
      unfold BinaryAdjacentWidthInterchange.volume; positivity
    have h1 := congrArg (fun l => l[0]?) (hhdr k)
    rw [hk, hpay] at h1
    simp only [List.getElem?_ofFn, hvol, dite_true, List.getElem?_cons_zero,
      Option.some.injEq] at h1
    have h2 := congrArg Fin.val h1
    revert h2
    cases x ⟨0, hvol⟩ <;> simp [bitSymbol, separator]
  -- the caller bank seen by the interchange machine
  let caller : Tapes t₀ prime :=
    ⟨fun i => if ∃ k, hd k = i then 1 else 0, fun i => wordTape ((S.R (ι (reg i))).map e.decode)⟩
  have htapes : ∀ k, caller.tape (hd k) = RadixZeroFill.encodedBinary (hs k) := by
    intro k
    show wordTape ((S.R (ι (reg (hd k)))).map e.decode) = _
    rw [hhdr k, encodedBinary_eq]
    simp [e, Function.comp_def]
  have hheads : ∀ k, caller.head (hd k) = 1 := fun k => by
    show (if ∃ k', hd k' = hd k then (1 : ℤ) else 0) = 1
    rw [ite_eq_left ⟨k, rfl⟩]
  have ht :
      caller.tape pay = BinaryRadixRangePrepareAlphabet.word (fun i => bitSymbol (x i)) := by
    show wordTape ((S.R (ι (reg pay))).map e.decode) = _
    rw [BinaryRadixRangePrepareAlphabet.word, putWord_blank_zero, hpay, List.map_ofFn]
    simp [e, Function.comp_def]
  have hh : caller.head pay = 0 := by
    show (if ∃ k, hd k = pay then (1 : ℤ) else 0) = 0
    rw [ite_eq_right (fun ⟨k, hk⟩ => hpay_hd k hk)]
  -- step 1: mark the unplaced registers
  have hun : ∀ j, ι j ∉ unplaced ι := fun j hm => (mem_unplaced ι _).1 hm j rfl
  have he₀ := markList_exec body (unplaced ι) (unplaced_nodup ι) v S
  set S₀ : Stacks T (prime + K) :=
    { S with R := fun y => if y ∈ unplaced ι then blank :: S.R y else S.R y } with hS₀
  -- step 2: shift the header registers
  set l₀ : List (Fin T) := List.ofFn fun k => ι (reg (hd k)) with hl₀
  have hnd₀ : l₀.Nodup := by
    rw [hl₀, List.nodup_ofFn]
    intro a b hab
    exact hi (swapReg_injective (hι hab))
  have hmem : ∀ y, y ∈ l₀ ↔ ∃ k, ι (reg (hd k)) = y := fun y => List.mem_ofFn
  obtain ⟨v₁, hu₁, he₁⟩ := shiftList_exec body l₀ hnd₀ v S₀
  set S₁ : Stacks T (prime + K) := { S₀ with
    L := fun i => if i ∈ l₀ then (S₀.R i).head?.getD blank :: S₀.L i else S₀.L i
    R := fun i => if i ∈ l₀ then (S₀.R i).tail else S₀.R i } with hS₁
  have hS₁hdr : ∀ k, S₁.L (ι (reg (hd k))) = [separator] ∧
      S₁.R (ι (reg (hd k))) = (hs k).map bitSymbol := by
    intro k
    have hm : ι (reg (hd k)) ∈ l₀ := (hmem _).2 ⟨k, rfl⟩
    simp [S₁, S₀, hm, hun, hL, hhdr k]
  have hS₁oth : ∀ j, (∀ k, reg (hd k) ≠ j) → S₁.L (ι j) = [] ∧ S₁.R (ι j) = S.R (ι j) := by
    intro j hj
    have hm : ι j ∉ l₀ := fun hm => by
      obtain ⟨k, hk⟩ := (hmem _).1 hm
      exact hj k (hι hk)
    simp [S₁, S₀, hm, hun, hL]
  -- the host bank represented by `S₁`
  let w₀ : Tapes T (prime + K) := ⟨fun _ => 0, fun y z => readAt blank (S₁.L y) (S₁.R y) z⟩
  let W := Placement.replace pe w₀ (Alphabet.mapTapes e (BinaryInterchangeRun.input caller))
  have hrep : RepT W S₁.L S₁.R := by
    intro y z
    by_cases hy : ∃ j, ι j = y
    · obtain ⟨j, rfl⟩ := hy
      rw [InjectivePlacement.replace_tape_slot, InjectivePlacement.replace_head_slot]
      obtain ⟨hhead, htape⟩ := input_ext caller j
      show e.encode ((BinaryInterchangeRun.input caller).tape j z) =
        readAt blank (S₁.L (ι j)) (S₁.R (ι j)) (z - (BinaryInterchangeRun.input caller).head j)
      rw [hhead, htape]
      by_cases hj : j.val < t₀
      · rw [dite_eq_left hj, dite_eq_left hj]
        obtain ⟨i, rfl⟩ : ∃ i : Fin t₀, j = reg i := ⟨⟨j.val, hj⟩, Fin.ext rfl⟩
        change e.encode (wordTape ((S.R (ι (reg i))).map e.decode) z) =
          readAt blank (S₁.L (ι (reg i))) (S₁.R (ι (reg i))) (z - caller.head i)
        rw [encode_wordTape_decode _ (fun s hs => (hgood _ s hs).2) z]
        by_cases hk : ∃ k, hd k = i
        · obtain ⟨k, rfl⟩ := hk
          rw [(hS₁hdr k).1, (hS₁hdr k).2, hheads k, hhdr k, readAt_single]
        · have hc0 : caller.head i = 0 := ite_eq_right hk
          have hoth := hS₁oth (reg i) (fun k hk' => hk ⟨k, swapReg_injective hk'⟩)
          rw [hoth.1, hoth.2, hc0, sub_zero, readAt_nil_left]
      · rw [dite_eq_right hj, dite_eq_right hj]
        have hoth := hS₁oth j (fun k hk' => hj (hk' ▸ (hd k).isLt))
        rw [hoth.1, hoth.2, hpriv j (by omega), readAt_nil_left, wordTape_nil]
        rfl
    · have hy' : ∀ j, ι j ≠ y := fun j hj => hy ⟨j, hj⟩
      rw [InjectivePlacement.replace_tape_other _ _ _ _ _ _ hy',
        InjectivePlacement.replace_head_other _ _ _ _ _ _ hy']
      show readAt blank (S₁.L y) (S₁.R y) z = readAt blank (S₁.L y) (S₁.R y) (z - 0)
      rw [sub_zero]
  let bound := mnSize (mk v S)+depth+T*(2*SwapMachineStock.reserve P G B h d+2)+3*T+20
  have hmark := markList_within (unplaced ι) he₀ depth
  have hshift := shiftList_within l₀ he₁ depth
  have hmarkEnd := hmark.final
  have hshiftEnd := hshift.final
  have hlist : l₀.length = 5 := by simp only [hl₀,List.length_ofFn]
  have hunplaced := unplaced_length_le ι
  have hcaller : ∀ i, 0 ≤ caller.head i ∧ caller.head i ≤ 1 := by
    intro i
    dsimp only [caller]
    split_ifs <;> constructor <;> decide
  have hW : ∀ j, 0 ≤ W.head j ∧ W.head j ≤ 1 := by
    intro y
    by_cases hy : ∃ j, ι j = y
    · obtain ⟨j,rfl⟩ := hy
      dsimp only [W]
      rw [InjectivePlacement.replace_head_slot]
      change 0 ≤ (BinaryInterchangeRun.input caller).head j ∧
        (BinaryInterchangeRun.input caller).head j ≤ 1
      rw [(input_ext caller j).1]
      split_ifs with hj
      · exact hcaller _
      · exact ⟨le_refl 0,by decide⟩
    · dsimp only [W]
      rw [InjectivePlacement.replace_head_other _ _ _ _ _ _ (fun j hj => hy ⟨j,hj⟩)]
      change (0 : ℤ) ≤ 0 ∧ (0 : ℤ) ≤ 1
      decide
  obtain ⟨v₂,S₂,hrep₂,hu₂,hin₂,hout₂,hlen₂,hframe₂,n₂,hn₂,hforeign⟩ :=
    PlacedSwapMachineStock.exec_within body caller hd pay hi hQ ι hι hT P G B h d hs
      hhd hdh hv hc hP hG hB htapes hheads x ht hh hcaller W
      (by exact Placement.active_replace pe w₀ _) hW v₁ S₁ hrep depth
  have hwmark := hmark.mono (J := fun z c => mnSize c+z ≤ bound) (by
    intro z c hc
    dsimp only [bound]
    omega)
  have hwshift := hshift.mono (J := fun z c => mnSize c+z ≤ bound) (by
    intro z c hc
    change mnSize (mk v S₀)+depth ≤ mnSize (mk v S)+depth+((unplaced ι).length+1) at hmarkEnd
    dsimp only [bound]
    omega)
  have hwforeign := hforeign.mono (J := fun z c => mnSize c+z ≤ bound) (by
    intro z c hc
    change mnSize (mk v S₀)+depth ≤ mnSize (mk v S)+depth+((unplaced ι).length+1) at hmarkEnd
    change mnSize (mk v₁ S₁)+depth ≤ mnSize (mk v S₀)+depth+(l₀.length+1) at hshiftEnd
    dsimp only [bound]
    omega)
  obtain ⟨v₃,n₃,hu₃,hn₃,he₃⟩ := normList_exec body (List.ofFn ι) (List.nodup_ofFn.2 hι) v₂ S₂
  have hwnorm := normList_within (List.ofFn ι) he₃ depth bound hwforeign.final
  have he₄ := dropList_exec body (unplaced ι) (unplaced_nodup ι) v₃ {S₂ with
    L := fun i => if i ∈ List.ofFn ι then [] else S₂.L i
    R := fun i => if i ∈ List.ofFn ι then sweep (S₂.L i) (S₂.R i) else S₂.R i}
  have hwdrop := dropList_within (unplaced ι) he₄ depth bound hwnorm.final
  have hwhole := ExecWithin.seq hwmark (ExecWithin.seq hwshift
    (ExecWithin.seq hwforeign (ExecWithin.seq hwnorm hwdrop)))
  change ExecWithin body _ depth (placedSwapProg hd pay hi hQ ι hι hT) (mk v S) _ _ at hwhole
  obtain ⟨vf,m,huser,htime,he⟩ := placedSwapProg_run body hd pay hi hQ ι hι hT
    P G B h d hs hhd hdh hv hc hP hG hB x v S hL hpriv hhdr hpay hother
  obtain ⟨hsteps,hfinal⟩ := hwhole.toExec.unique he
  rw [hsteps,hfinal] at hwhole
  exact ⟨vf,m,huser,htime,hwhole⟩

theorem placedSwapProg_exec_within {t₀ T Q K : ℕ} {U F : Type} (body : F → Pr F T Q (prime + K) U)
    (hd : Fin 5 → Fin t₀) (pay : Fin t₀) (hi : Function.Injective hd)
    (hQ : swapStates hd pay hi ≤ Q)
    (ι : Fin (swapT t₀) → Fin T) (hι : Function.Injective ι) (hT : swapT t₀ ≤ T)
    (P G B h d : ℕ) (hs : Fin 5 → List Bool) (hhd : h ≤ d + 1) (hdh : d ≤ h + 1)
    (hv : ∀ k, Counter.value (hs k) = swapValues P G B h d k)
    (hc : ∀ k, GrowingCounterData.Canonical (hs k)) (hP : 0 < P) (hG : 0 < G) (hB : 0 < B)
    (x : Fin (BinaryAdjacentWidthInterchange.volume P (2 ^ h) G (2 ^ d) B) → Bool)
    (v : HS T Q (prime + K) U) (S : Stacks T (prime + K))
    (hL : ∀ y, S.L y = [])
    (hpriv : ∀ j : Fin (swapT t₀), t₀ ≤ j.val → S.R (ι j) = [])
    (hhdr : ∀ k, S.R (ι (reg (hd k))) = separator :: (hs k).map bitSymbol)
    (hpay : S.R (ι (reg pay)) = List.ofFn fun i => bitSymbol (x i))
    (hother : ∀ i, i ≠ pay → (∀ k, hd k ≠ i) →
      ∀ s ∈ S.R (ι (reg i)), s ≠ blank ∧ s.val < prime + 4) (depth : ℕ) :
    ∃ v' m, v'.user = v.user ∧
      m ≤ (T + 12 * swapT t₀ + 5) * swapCost P G B h d hs +
        6 * ∑ j, (S.R (ι j)).length + 2 * T + 6 * swapT t₀ + 15 ∧
      ExecWithin body (fun z c => mnSize c+z ≤ mnSize (mk v S)+depth+
        T*(2*SwapMachineStock.reserve P G B h d+2)+3*T+20) depth (placedSwapProg hd pay hi hQ ι hι hT) (mk v S) m
        (mk v' { S with
          L := fun _ => []
          R := Function.update S.R (ι (reg pay))
            (swapList P (2 ^ h) G (2 ^ d) B blank (S.R (ι (reg pay)))) }) := by
  obtain ⟨v', m, hu, hm, he⟩ := placedSwapProg_run_within body hd pay hi hQ ι hι hT P G B h d hs hhd
    hdh hv hc hP hG hB x v S (fun j => hL (ι j)) hpriv hhdr hpay hother depth
  refine ⟨v', m, hu, hm, ?_⟩
  have hL' : (fun y => if y ∈ List.ofFn ι then [] else S.L y) = fun _ => [] := by
    funext y; split_ifs <;> simp [hL]
  rw [hL'] at he
  rw [hpay, ← transpose_bits_eq_swapList]
  exact he


end
end IntegerMultBounds.MathlibTM2.Host
