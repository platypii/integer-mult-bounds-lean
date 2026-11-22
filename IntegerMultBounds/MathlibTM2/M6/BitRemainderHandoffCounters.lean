module

public import IntegerMultBounds.MathlibTM2.M6.BitRemainderInputCounters

/-! Install both the staging and the ordinary padding counters for the two handoffs. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode.OrdinaryHandoff
open IntegerMultBounds.Machine Stack Host
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open FlatCoordinateSchedule (bits)
local instance (w : ℕ) : NeZero (prime^w) := ⟨(pow_pos IntegerMultBounds.Networks.Shared50ModularControl.prime_prime.pos _).ne'⟩

def paddingBanks : Fin 4 → Fin 12 ↪ Fin 95 := ![inputCrop,inputPad,outputCrop,outputPad]

private theorem privateBanks : ∀ i j, i ≠ j → ∀ a b : Fin 12, 2 ≤ a.val → 2 ≤ b.val →
    paddingBanks i a ≠ paddingBanks j b := by decide +kernel

/-- Staging crop and return padding use the same three retained dimensions.
Ordinary padding and return crop share a second triple. -/
theorem preparePadding_exec {P U : Type} {T Q : ℕ} (body : P → Pr P T Q prime U)
    (slots : Fin 95 ↪ Fin T) (staging : Fin 3 → Fin T)
    (apart : ∀ i j k, staging i ≠ slots (paddingBanks j k)) :
    let port := fun i => (paddingBanks i).trans slots
    ∃ code, ∀ A B N K (shift : ℕ) u S,
      StageDimensionWords staging K N (A*B) S → (∀ j z, readAt blank (S.L (slots (inputHeaders j))) (S.R (slots (inputHeaders j))) (z-1) =
        RadixZeroFill.encodedBinary (bits (![A*K,N,shift,B] j)) z) →
      (∀ i j, 2 ≤ j.val → S.L (port i j) = [] ∧ S.R (port i j) = []) →
      ∃ v F t, Exec body code (mk u S) t (mk v F) ∧
        t = 2*(scanCounterCost ![K,N,A*B]+scanCounterCost ![A*K,N,B])+5 ∧ v.user = u.user ∧
        CropCounters (port 0) (A*B) N K F ∧ CropCounters (port 1) B N (A*K) F ∧
        CropCounters (port 2) B N (A*K) F ∧ CropCounters (port 3) (A*B) N K F ∧
        ∀ j, (∀ i k, 2 ≤ k.val → port i k ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  intro port
  let hdr : Fin 3 → Fin 4 := ![0,1,3]
  let ordinary := fun k => slots (inputHeaders (hdr k))
  let source := fun i : Fin 4 => if i = 0 ∨ i = 3 then staging else ordinary
  have never (i j k l) : source i k ≠ port j l := by
    dsimp only [source]; split
    · exact apart k j l
    · exact slots.injective.ne ((by decide +kernel : ∀ a j l, inputHeaders a ≠ paddingBanks j l) (hdr k) j l)
  choose setup install using fun i => prepareOwnerPad_exec body (port i) (source i) (fun k j => never i i k j)
  refine ⟨Prog.seqList ((List.finRange 4).map setup),?_⟩
  intro A B N K shift u S hs ho fresh
  let width := fun i : Fin 4 => if i = 0 ∨ i = 3 then K else A*K
  let blocks := fun i : Fin 4 => if i = 0 ∨ i = 3 then A*B else B
  let fee := fun i => scanCounterCost ![width i,N,blocks i]+1
  have go (is : List (Fin 4)) (nd : is.Nodup) (v : HS T Q prime U) (D : Stacks T prime)
      (words : ∀ i, ∀ k z, readAt blank (D.L (source i k)) (D.R (source i k)) (z-1) =
        RadixZeroFill.encodedBinary (bits (![width i,N,blocks i] k)) z)
      (free : ∀ i ∈ is, ∀ j, 2 ≤ j.val → D.L (port i j) = [] ∧ D.R (port i j) = []) :
      ∃ z F, Exec body (Prog.seqList (is.map setup)) (mk v D) ((is.map fee).sum+1) (mk z F) ∧
        z.user = v.user ∧ (∀ i ∈ is, CropCounters (port i) (blocks i) N (width i) F) ∧
        ∀ j, (∀ i ∈ is, ∀ k, 2 ≤ k.val → port i k ≠ j) → F.L j = D.L j ∧ F.R j = D.R j := by
    induction is generalizing v D with
    | nil => exact ⟨v,D,Exec.act _ _,rfl,by simp,by simp⟩
    | cons i is ih =>
      obtain ⟨u,E,load,user,stored,off⟩ := install i _ _ _ v D (words i) (free i List.mem_cons_self)
      have diff j (h : j ∈ is) : i ≠ j := fun eq => nd.notMem (eq ▸ h)
      have disj (j q r) (h : i ≠ j) (hq : 2 ≤ q.val) (hr : 2 ≤ r.val) :
          port i q ≠ port j r := slots.injective.ne (privateBanks _ _ h _ _ hq hr)
      obtain ⟨z,F,run,same,ready,outside⟩ := ih nd.of_cons u E
        (fun j k z => by
          have keep := off _ (fun l _ => (never j i k l).symm)
          rw [keep.1,keep.2]; exact words j k z)
        (fun j h r hr => by
          have keep := off _ (fun q hq => disj j q r (diff j h) hq hr)
          rw [keep.1,keep.2]; exact free j (List.mem_cons_of_mem _ h) r hr)
      refine ⟨z,F,(Exec.seq load run).cast (by simp [fee,Nat.add_assoc]) rfl,same.trans user,?_,?_⟩
      · intro j hj
        rcases List.mem_cons.mp hj with rfl | h
        · intro r h₀ h₁ l
          have hr : 2 ≤ r.val := (by decide : ∀ r : Fin 12, r ≠ 0 → r ≠ 1 → 2 ≤ r.val) r h₀ h₁
          have keep := outside _ (fun j h q hq => (disj j r q (diff j h) hr hq).symm)
          rw [keep.1,keep.2]; exact stored r hr l
        · exact ready j h
      · intro j h
        have last := outside j (fun k hk => h k (List.mem_cons_of_mem _ hk))
        have first := off j (h i List.mem_cons_self)
        exact ⟨last.1.trans first.1,last.2.trans first.2⟩
  obtain ⟨v,F,run,same,ready,off⟩ := go _ (List.nodup_finRange 4) u S
    (fun i k z => by
      dsimp only [source,width,blocks]; split
      · exact hs.read k z
      · fin_cases k <;> first | exact ho 0 z | exact ho 1 z | exact ho 3 z)
    (fun i _ => fresh i)
  refine ⟨v,F,_,run,?_,same,ready 0 (by decide),ready 1 (by decide),ready 2 (by decide),ready 3 (by decide),
    fun j h => off j (fun i _ => h i)⟩
  change (fee 0+(fee 1+(fee 2+(fee 3+0))))+1 = _
  simp [fee,width,blocks]
  omega

/-- All four counter installations together cost linear time in the padded volume. -/
theorem preparePadding_cost_le {A B N K : ℕ}
    (ha : 0 < A) (hb : 0 < B) (hn : 0 < N) (hk : 0 < K) :
    2*(scanCounterCost ![K,N,A*B]+scanCounterCost ![A*K,N,B])+5 ≤ 301*(A*B*(N*K)) := by
  let V := A*B*(N*K)
  have ab : A*B ≤ V := Nat.le_mul_of_pos_right _ (Nat.mul_pos hn hk)
  have nk : N*K ≤ V := Nat.le_mul_of_pos_left _ (Nat.mul_pos ha hb)
  have k := (Nat.le_mul_of_pos_left K hn).trans nk
  have n := (Nat.le_mul_of_pos_right N hk).trans nk
  have ak : A*K ≤ V := Nat.mul_le_mul (Nat.le_mul_of_pos_right A hb) (Nat.le_mul_of_pos_left K hn)
  have b := (Nat.le_mul_of_pos_left B ha).trans ab
  have pos := hk.trans_le k
  have := scanCounterCost_le k n ab pos
  have := scanCounterCost_le ak n b pos
  change _ ≤ 301*V
  omega

/-- Prepare both directions before entering the scanner, retaining its return counters. -/
theorem prepareAndEnter_exec {P U : Type} {T Q : ℕ} (body : P → Pr P T Q prime U)
    (fits : 235 ≤ Q) (slots : Fin 95 ↪ Fin T) (staging : Fin 3 → Fin T)
    (apart : ∀ i j k, staging i ≠ slots (paddingBanks j k)) :
    ∃ code, ∀ w B K, 0 < B → 0 < K →
      let A := (prime^w)^16
      let N := prime^(64*(w*64))
      let g := ordinaryIdentityRow w
      ∀ (x : Fin 142081 → Fin (A*(B*K)) → ZMod 2) i u S,
      StageDimensionWords staging K N (A*B) S →
      (∀ b j, 2 ≤ j.val → S.L (slots (paddingBanks b j)) = [] ∧ S.R (slots (paddingBanks b j)) = []) →
      WordAtZero (singleLabelBank (firstRowLabel w) x i) (S.L (slots 0)) (S.R (slots 0)) →
      (∀ z, readAt blank (S.L ((inputCrop.trans slots) 1)) (S.R ((inputCrop.trans slots) 1)) z = blank) →
      S.R (slots (inputHeaders 3)) = binSyms B.size B → S.R (slots 94) = binSyms K.size K →
      S.L ((inputTranspose.trans slots) 0) = [] → S.L ((inputTranspose.trans slots) 1) = [] →
      (∀ j, S.R ((inputTranspose.trans slots) j) = []) →
      (∀ z, readAt blank (S.L ((inputPad.trans slots) 1)) (S.R ((inputPad.trans slots) 1)) z = blank) →
      (∀ j z, readAt blank (S.L ((inputHeaders.trans slots) j)) (S.R ((inputHeaders.trans slots) j)) (z-1) =
        RadixZeroFill.encodedBinary (bits (![A*K,N,g.val,B] j)) z) →
      (∀ j : Fin 14, j ≠ 10 → j ≠ 11 → S.L ((inputRotation.trans slots) j) = [] ∧ S.R ((inputRotation.trans slots) j) = []) →
      (∀ z, readAt blank (S.L (slots 1)) (S.R (slots 1)) z = blank) →
      ∃ v F t, Exec body code (mk u S) t (mk v F) ∧ t ≤ 23462*(A*(B*N*K))+583 ∧
        v.user = u.user ∧ WordAtZero (fun j => singleLabelBank (firstRowLabel w) x i
          ((ordinaryRowLayout (Equiv.swap 0 g)).symm j)) (F.L (slots 1)) (F.R (slots 1)) ∧
        (∀ l, readAt blank (F.L (slots 0)) (F.R (slots 0)) l = blank) ∧
        CropCounters (outputCrop.trans slots) B N (A*K) F ∧
        CropCounters (outputPad.trans slots) (A*B) N K F ∧
        ∀ j, (∀ b k, 2 ≤ k.val → slots (paddingBanks b k) ≠ j) →
          (∀ i, (inputCrop.trans slots) i ≠ j) → (∀ i, (inputTranspose.trans slots) i ≠ j) → (∀ i, (inputPad.trans slots) i ≠ j) → (∀ i, (inputRotation.trans slots) i ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  obtain ⟨setup,install⟩ := preparePadding_exec body slots staging apart
  obtain ⟨enter,move⟩ := enter_exec body fits slots
  obtain ⟨clocks,build⟩ := inputCounters_exec body (inputTranspose.trans slots) (slots (inputHeaders 3)) (slots 94)
    (slots.injective.ne (by decide)) (fun i => ⟨slots.injective.ne ((by decide : ∀ i, inputHeaders 3 ≠ inputTranspose i) i),
      slots.injective.ne ((by decide : ∀ i, (94 : Fin 95) ≠ inputTranspose i) i)⟩)
  refine ⟨setup.seq (clocks.seq enter),?_⟩
  intro w B K hb hk A N g x i u S dims fresh owner cropBlank blockDigits widthDigits
    left₀ left₁ transpose padBlank headers rotFree scannerBlank
  obtain ⟨v,D,t,load,time,user,c₀,c₁,c₂,c₃,off⟩ := install A B N K g.val u S dims headers fresh
  have keep (j : Fin 95) (h : ∀ b k, 2 ≤ k.val → paddingBanks b k ≠ j) :=
    off (slots j) (fun b k hk => slots.injective.ne (h b k hk))
  have tr (j : Fin 8) := keep (inputTranspose j)
    ((by decide +kernel : ∀ j b k, 2 ≤ k.val → paddingBanks b k ≠ inputTranspose j) j)
  have hd (j : Fin 4) := keep (inputHeaders j)
    ((by decide +kernel : ∀ j b k, 2 ≤ k.val → paddingBanks b k ≠ inputHeaders j) j)
  have rot (j : Fin 14) := keep (inputRotation j)
    ((by decide +kernel : ∀ j b k, 2 ≤ k.val → paddingBanks b k ≠ inputRotation j) j)
  have zero := keep 0 (by decide +kernel)
  have one := keep 1 (by decide +kernel)
  have crop := keep (inputCrop 1) (by decide +kernel)
  have pad := keep (inputPad 1) (by decide +kernel)
  obtain ⟨y,E,r,clockRun,clockCost,clockUser,left,clockWords,clockOff⟩ := build B K v D
    ((hd 3).2.trans blockDigits) ((keep 94 (by decide +kernel)).2.trans widthDigits)
    (fun j => (tr j).2.trans (transpose j))
  have kept (j : Fin 95) (h : j ≠ inputTranspose 4 ∧ j ≠ inputTranspose 7) :
      E.R (slots j) = D.R (slots j) := clockOff _ (slots.injective.ne h.1) (slots.injective.ne h.2)
  have counters (b : Fin 4) {d n k} (ready : CropCounters ((paddingBanks b).trans slots) d n k D) :
      CropCounters ((paddingBanks b).trans slots) d n k E := by
    intro j h₀ h₁ z
    have eq := kept _ ((by decide +kernel : ∀ b j, paddingBanks b j ≠ inputTranspose 4 ∧ paddingBanks b j ≠ inputTranspose 7) b j)
    simpa only [Function.Embedding.trans_apply,left,eq] using ready j h₀ h₁ z
  have unchanged (j : Fin 95) (a : j ≠ inputTranspose 4 ∧ j ≠ inputTranspose 7)
      (b : D.R (slots j) = S.R (slots j)) := (kept j a).trans b
  have rotR (j : Fin 14) := unchanged _ ((by decide : ∀ j, inputRotation j ≠ inputTranspose 4 ∧ inputRotation j ≠ inputTranspose 7) j) (rot j).2
  have hdR (j : Fin 4) := unchanged _ ((by decide : ∀ j, inputHeaders j ≠ inputTranspose 4 ∧ inputHeaders j ≠ inputTranspose 7) j) (hd j).2
  obtain ⟨z,F,m,run,paid,same,out,cleared,frame⟩ := move w B K hb hk x i y E
    (by rwa [left,zero.1,unchanged 0 (by decide) zero.2])
    (by simpa only [Function.Embedding.trans_apply,left,crop.1,unchanged _ (by decide : inputCrop 1 ≠ inputTranspose 4 ∧ inputCrop 1 ≠ inputTranspose 7) crop.2] using cropBlank)
    (counters 0 c₀) _ _ (List.length_replicate ..) (List.length_replicate ..)
    (by rw [left]; exact (tr 0).1.trans left₀) (by rw [left]; exact (tr 1).1.trans left₁)
    clockWords
    (by simpa only [Function.Embedding.trans_apply,left,pad.1,unchanged _ (by decide : inputPad 1 ≠ inputTranspose 4 ∧ inputPad 1 ≠ inputTranspose 7) pad.2] using padBlank)
    (counters 1 c₁) (fun j l => by simpa only [Function.Embedding.trans_apply,left,(hd j).1,hdR j] using headers j l)
    (fun j h₀ h₁ => ⟨by rw [left]; exact (rot j).1.trans (rotFree j h₀ h₁).1,(rotR j).trans (rotFree j h₀ h₁).2⟩)
    (by simpa only [left,one.1,unchanged 1 (by decide) one.2] using scannerBlank)
  have returnFrame (b : Fin 4) (hb : 2 ≤ b.val) (k : Fin 12) (hk : 2 ≤ k.val) :=
    frame (slots (paddingBanks b k))
      (fun j => slots.injective.ne ((by decide +kernel : ∀ b : Fin 4, 2 ≤ b.val → ∀ k : Fin 12, 2 ≤ k.val → ∀ j, inputCrop j ≠ paddingBanks b k) b hb k hk j))
      (fun j => slots.injective.ne ((by decide +kernel : ∀ b : Fin 4, 2 ≤ b.val → ∀ k : Fin 12, 2 ≤ k.val → ∀ j, inputTranspose j ≠ paddingBanks b k) b hb k hk j))
      (fun j => slots.injective.ne ((by decide +kernel : ∀ b : Fin 4, 2 ≤ b.val → ∀ k : Fin 12, 2 ≤ k.val → ∀ j, inputPad j ≠ paddingBanks b k) b hb k hk j))
      (fun j => slots.injective.ne ((by decide +kernel : ∀ b : Fin 4, 2 ≤ b.val → ∀ k : Fin 12, 2 ≤ k.val → ∀ j, inputRotation j ≠ paddingBanks b k) b hb k hk j))
  refine ⟨z,F,_,Exec.seq load (Exec.seq clockRun run),?_,same.trans (clockUser.trans user),out,cleared,?_,?_,?_⟩
  · have bound := preparePadding_cost_le (A := A) (N := N) (pow_pos (pow_pos IntegerMultBounds.Networks.Shared50ModularControl.prime_prime.pos _) _) hb
        (pow_pos IntegerMultBounds.Networks.Shared50ModularControl.prime_prime.pos _) hk
    rw [show A*B*(N*K) = A*(B*N*K) by ac_rfl] at bound
    change m ≤ 22944*(A*(B*N*K))+583 at paid
    have clockBound := clockCost.trans (inputCounters_cost_le hb hk)
    have small : B*K ≤ A*(B*N*K) := (Nat.mul_le_mul_right K (Nat.le_mul_of_pos_right B (pow_pos IntegerMultBounds.Networks.Shared50ModularControl.prime_prime.pos _))).trans
      (Nat.le_mul_of_pos_left _ (pow_pos (pow_pos IntegerMultBounds.Networks.Shared50ModularControl.prime_prime.pos _) _))
    omega
  · intro k h₀ h₁ l
    have keep := returnFrame 2 (by decide) k ((by decide : ∀ k : Fin 12, k ≠ 0 → k ≠ 1 → 2 ≤ k.val) k h₀ h₁)
    rw [show F.L ((outputCrop.trans slots) k) = _ from keep.1,
      show F.R ((outputCrop.trans slots) k) = _ from keep.2]
    exact counters 2 c₂ k h₀ h₁ l
  · intro k h₀ h₁ l
    have keep := returnFrame 3 (by decide) k ((by decide : ∀ k : Fin 12, k ≠ 0 → k ≠ 1 → 2 ≤ k.val) k h₀ h₁)
    rw [show F.L ((outputPad.trans slots) k) = _ from keep.1,
      show F.R ((outputPad.trans slots) k) = _ from keep.2]
    exact counters 3 c₃ k h₀ h₁ l
  · intro j banks a b c d
    have endFrame := frame j a b c d
    have startFrame := off j banks
    exact ⟨endFrame.1.trans (by rw [left]; exact startFrame.1),endFrame.2.trans ((clockOff j (b 4).symm (b 7).symm).trans startFrame.2)⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode.OrdinaryHandoff
