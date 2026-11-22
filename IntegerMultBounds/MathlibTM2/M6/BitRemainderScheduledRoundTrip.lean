module

public import IntegerMultBounds.MathlibTM2.M6.BitRemainderScheduledReturn

/-! Compose preparation, scheduled scanning and return on one staged owner. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover
open Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume role)
open FlatCoordinateSchedule (bits)
open IntegerMultBounds.Swap.Modular Matrix
open M8.RevMachine Cover.Fallback IntegerMultBounds.MathlibTM2.Fast.Main
local instance (w : ℕ) : NeZero (prime^w) := ⟨(pow_pos Shared50ModularControl.prime_prime.pos _).ne'⟩

namespace OrdinaryHandoff

/-- The two rotations share width, row count and block count. The remaining words
are their shifts and the two staging dimensions. -/
def headerPorts : Fin 7 ↪ Fin 93 := ⟨![44,45,46,47,90,91,92],by decide⟩

/-- Copy the retained binary words once. Both rotations and the transpose
clocks read the resulting headers without consuming them. -/
theorem loadHeaders_exec {T Q : ℕ} {P U : Type} (body : P → Pr P T Q prime U)
    (slots : Fin 93 ↪ Fin T) (src : Fin 7 → Fin T)
    (apart : ∀ i j, src i ≠ slots j) :
    let dst := headerPorts.trans slots
    ∃ code, ∀ (vals : Fin 7 → ℕ) u S,
      (∀ i, S.R (src i) = binSyms (vals i).size (vals i)) →
      (∀ i, S.L (dst i) = [] ∧ S.R (dst i) = []) →
      S.R (slots 13) = [] → S.R (slots 14) = [] →
      ∃ z F, Exec body code (mk u S)
        (((List.finRange 7).map (fun i => 6*(vals i).size+6)).sum+2) (mk z F) ∧
        z.user = u.user ∧ (∀ i, F.L (dst i) = [separator] ∧ F.R (dst i) = binSyms (vals i).size (vals i)) ∧
        ∀ j, (∀ i, dst i ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  intro dst
  let indices := List.finRange 7
  let marks := indices.map dst
  refine ⟨(Record.copyLeafHeaders src dst (slots 13) (slots 14) indices).seq (.act (pushMarkers marks)),?_⟩
  intro vals u S words empty tmp aux
  have ports (i) : [src i,dst i,slots 13,slots 14].Nodup := by
    have priv := ((by decide : ∀ i, [headerPorts i,13,14].Nodup) i).map slots.injective
    exact List.nodup_cons.mpr ⟨by simp [dst,apart],priv⟩
  obtain ⟨z,D,user,copy,left,stored,off⟩ := Record.copyLeafHeaders_exec body src dst (slots 13) (slots 14)
    (fun i j => apart i _) ports indices (List.nodup_finRange _) u S tmp aux (fun i _ => (empty i).2)
  have unique : marks.Nodup := (List.nodup_finRange 7).map dst.injective
  have mark := Exec.act (body := body) (pushMarkers marks) (mk z D)
  rw [pushMarkers_run _ unique] at mark
  refine ⟨z,_,(Exec.seq copy mark).cast (by simp only [indices,words,length_binSyms,Nat.add_assoc]) rfl,user,?_,?_⟩
  · intro i
    have mem : dst i ∈ marks := List.mem_map_of_mem (List.mem_finRange i)
    exact ⟨by simp [mem,left,(empty i).1],(stored i (List.mem_finRange i)).trans (words i)⟩
  · intro j h
    have miss : j ∉ marks := fun mem => by obtain ⟨i,_,eq⟩ := List.mem_map.mp mem; exact h i eq
    exact ⟨by simp [miss,left],off j (fun i _ => h i)⟩

private theorem headerViews {T : ℕ} (slots : Fin 93 ↪ Fin T) (S : Stacks T prime)
    (K N g B h D tail : ℕ)
    (raw : ∀ j : Fin 7, let n := (![K,N,g,B,h,D,tail] : Fin 7 → ℕ) j
      S.L (slots (headerPorts j)) = [separator] ∧ S.R (slots (headerPorts j)) = binSyms n.size n) :
    StageDimensionWords (fun j => slots ((![92,45,91] : Fin 3 → Fin 93) j)) tail N D S ∧
    (∀ (j : Fin 4) z, readAt blank (S.L ((inputHeaders.trans slots) j)) (S.R ((inputHeaders.trans slots) j)) (z-1) =
      RadixZeroFill.encodedBinary (bits (![K,N,g,B] j)) z) ∧
    (∀ (j : Fin 4) z, readAt blank (S.L (slots (outputHeaders j))) (S.R (slots (outputHeaders j))) (z-1) =
      RadixZeroFill.encodedBinary (bits (![K,N,h,B] j)) z) := by
  let dim : Fin 3 → Fin 93 := ![92,45,91]
  let vals : Fin 7 → ℕ := ![K,N,g,B,h,D,tail]
  have read (j : Fin 7) (z : ℤ) : readAt blank (S.L (slots (headerPorts j))) (S.R (slots (headerPorts j))) (z-1) =
      RadixZeroFill.encodedBinary (bits (vals j)) z := by
    rw [(raw j).1,(raw j).2,← Cover.Fallback.canonicalBits_symbols,encodedBinary_eq,readAt_single]
  have dims : StageDimensionWords (fun j => slots (dim j)) tail N (D) S := by
    intro j; fin_cases j
    · exact raw 6
    · exact raw 1
    · exact raw 5
  have headers (j : Fin 4) (z : ℤ) : readAt blank (S.L ((inputHeaders.trans slots) j)) (S.R ((inputHeaders.trans slots) j)) (z-1) =
      RadixZeroFill.encodedBinary (bits (![K,N,g,B] j)) z := by
    fin_cases j
    · exact read 0 z
    · exact read 1 z
    · exact read 2 z
    · exact read 3 z
  have outHeaders (j : Fin 4) (z : ℤ) : readAt blank (S.L (slots (outputHeaders j))) (S.R (slots (outputHeaders j))) (z-1) =
      RadixZeroFill.encodedBinary (bits (![K,N,h,B] j)) z := by
    fin_cases j
    · exact read 0 z
    · exact read 1 z
    · exact read 4 z
    · exact read 3 z
  exact ⟨dims,headers,outHeaders⟩

private def returnSlot (j : Fin 93) : Bool :=
  (44 ≤ j.val && j.val ≤ 61) || (72 ≤ j.val && j.val ≤ 79) || 90 ≤ j.val

/-- Both directions and the scheduled scanner act on the same staging owner.
Only initial workspace conditions are required. -/
private theorem ScheduledReturn.roundTripPrepared [M8.Machine.Net] {V size back Q w B W : ℕ} {U : Type}
    {stage : SharedBankStage.Stage _ 1 prime (phaseOwners (N := V))} {words : Fin size → List (Fin (prime+4))}
    {interval : ℕ × ℕ} {parent : Fin 64 → ZMod (prime^(w+1))}
    {c : Certificates.PR589.Nine.PortCertificate} {checked : c.Checked}
    {body : Unit → Pr Unit ((size+stage.tapes+back)+99) Q prime U} {scan rate}
    (scheduled : ScheduledReturn (w := w) (B := B) (W := W) interval parent c checked
      (((stage.slots 0).natAdd size).castAdd back) (ScannerReady stage size back words) body scan rate)
    (hb : 0 < B) (hw : 0 < W) (fits : 235 ≤ Q) :
    ∃ code : Pr Unit ((size+stage.tapes+back)+99) Q prime U,
    let T := size+stage.tapes+back
    let owner := ((stage.slots 0).natAdd size).castAdd back
    let slots := aroundScanner owner
    let old := Fin.castAddEmb 99 (n := T)
    let layout := stagedScannerLayout w B W
    let M := prime^(w+1)
    let A := M^16
    let tail := M^112*W
    let N := M^(64*64)
    let K := M^128*W
    let g := ordinaryIdentityRow (w+1)
    let idRow := LabelAddress.address (1 : LabelPadding.Label 64 (w+1))
    ∀ (x : Fin 142081 → Fin (A*(B*tail)) → ZMod 2) i u S,
      ScannerReady stage size back words (embStk old S) →
      (∀ j : Fin 7, let h := slots (headerPorts j)
        let n := (![K,N,g.val,B,(0-idRow).val,A*B,tail] : Fin 7 → ℕ) j
        S.L h = [separator] ∧ S.R h = binSyms n.size n) →
      (∀ b j, 2 ≤ j.val → S.L (slots (paddingBanks b j)) = [] ∧ S.R (slots (paddingBanks b j)) = []) →
      WordAtZero (singleLabelBank (firstRowLabel (w+1)) x i) (S.L (slots 0)) (S.R (slots 0)) →
      (∀ z, readAt blank (S.L ((inputCrop.trans slots) 1)) (S.R ((inputCrop.trans slots) 1)) z = blank) →
      S.L ((inputTranspose.trans slots) 0) = [] → S.L ((inputTranspose.trans slots) 1) = [] →
      (∀ j, S.R ((inputTranspose.trans slots) j) = []) →
      (∀ z, readAt blank (S.L ((inputPad.trans slots) 1)) (S.R ((inputPad.trans slots) 1)) z = blank) →
      (∀ j : Fin 14, j ≠ 10 → j ≠ 11 → S.L ((inputRotation.trans slots) j) = [] ∧ S.R ((inputRotation.trans slots) j) = []) →
      (∀ z, readAt blank (S.L (slots 1)) (S.R (slots 1)) z = blank) →
      (∀ j : Fin 14, j ≠ 10 → j ≠ 11 → S.L ((outputRotation.trans slots) j) = [] ∧ S.R ((outputRotation.trans slots) j) = []) →
      (∀ z, readAt blank (S.L ((outputRotation.trans slots) 11)) (S.R ((outputRotation.trans slots) 11)) z = blank) →
      (∀ z, readAt blank (S.L ((outputCrop.trans slots) 1)) (S.R ((outputCrop.trans slots) 1)) z = blank) →
      (∀ i, S.R ((outputTranspose.trans slots) i) = []) → S.L ((outputTranspose.trans slots) 1) = [] →
      S.L ((outputTranspose.trans slots) 6) = [] →
      ∃ v F t, ∃ staged : Fin (M^16*(B*(M^112*W))) → ZMod 2, Exec body code (mk u S) t (mk v F) ∧
        (t : ℝ) ≤ (packedChartRate (0 : Fin 1) c checked false layout.width +
          packedChartRate (0 : Fin 1) c checked true layout.width + (366+16*64*64+19*64+344) +
          rate*((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau + 64*(8*64+21+28+(prime.size : ℝ)))*
          volume prime (role layout 142080) + 13 + 46444*(B*(N*K) : ℕ)+1182 ∧ v.user = u.user ∧
        WordAtZero (singleLabelBank (firstRowLabel (w+1)) (fun _ => staged) 0) (F.L (slots 0)) (F.R (slots 0)) ∧
      let proj := IntegerMultBounds.Swap.Modular.reduce M ((c.span interval.1 interval.2).submatrix stageAxis.symm stageAxis.symm)
      let frame := Matrix.fromBlocks (Matrix.diagonal parent) 0 0 (M8.ReversedExchange.rev 64)
      let addr := fun b y (k : Fin W) => stagedOwnerIndex b (FlatCoordinateLayout.index
        ((frame.mulVec y) ∘ (finSumFinEquiv : (Fin 64 ⊕ Fin 64) ≃ Fin 128).symm) k)
      ∀ b y k, staged (addr b ((Matrix.fromBlocks (1-proj) proj proj (1-proj)).mulVec y) k) = x i (addr b y k) := by
  let slots := aroundScanner (((stage.slots 0).natAdd size).castAdd back)
  let dim : Fin 3 → Fin 93 := ![92,45,91]
  obtain ⟨enter,forward⟩ := prepareAndEnter_exec body fits slots (fun j => slots (dim j))
    (fun i j k => slots.injective.ne ((by decide +kernel : ∀ (i : Fin 3) j k, (![92,45,91] : Fin 3 → Fin 93) i ≠ paddingBanks j k) i j k))
  refine ⟨enter.seq scan,?_⟩
  intro _ _ _ _ layout M A tail N K g idRow x i u S initial raw fresh ownerWord cropBlank
    left₀ left₁ transpose padBlank rotFree scannerBlank
    outRot outDest cropDest outTranspose outLeft₁ outLeft₆
  have rows : prime^(64*((w+1)*64)) = N := by
    change _ = (prime^(w+1))^(64*64)
    rw [← pow_mul]; congr 1; omega
  have width : A*tail = K := ordinaryCompact_width M W
  obtain ⟨dims,forwardHeaders,outHeaders⟩ := headerViews slots S K N g.val B (0-idRow).val (A*B) tail raw
  have headers := forwardHeaders
  rw [← width] at headers
  obtain ⟨v,D,n,enterRun,enterTime,same,live,blankOwner,crop,pad,frame⟩ :=
    forward (w+1) B tail hb (Nat.mul_pos (pow_pos (pow_pos IntegerMultBounds.Networks.Shared50ModularControl.prime_prime.pos _) _) hw)
      x i u S (by rwa [rows]) fresh ownerWord cropBlank (raw 3).2 (raw 6).2 left₀ left₁ transpose padBlank
      (by simpa only [rows] using headers) rotFree scannerBlank
  have keep (j : Fin 93) (h : returnSlot j) : D.L (slots j) = S.L (slots j) ∧ D.R (slots j) = S.R (slots j) := by
    apply frame
    all_goals simp only [Function.Embedding.trans_apply,ne_eq,slots.injective.eq_iff]
    · exact (by decide +kernel : ∀ j, returnSlot j → ∀ b k, 2 ≤ k.val → paddingBanks b k ≠ j) j h
    · exact (by decide +kernel : ∀ j, returnSlot j → ∀ i, inputCrop i ≠ j) j h
    · exact (by decide +kernel : ∀ j, returnSlot j → ∀ i, inputTranspose i ≠ j) j h
    · exact (by decide +kernel : ∀ j, returnSlot j → ∀ i, inputPad i ≠ j) j h
    · exact (by decide +kernel : ∀ j, returnSlot j → ∀ i, inputRotation i ≠ j) j h
  have hd (j : Fin 4) := keep _ ((by decide : ∀ j, returnSlot (outputHeaders j)) j)
  have rot (j : Fin 14) (hj : j ≠ 10) := keep _ ((by decide : ∀ j : Fin 14, j ≠ 10 → returnSlot (outputRotation j)) j hj)
  have tr (j : Fin 8) := keep _ ((by decide : ∀ j, returnSlot (outputTranspose j)) j)
  have dest := rot 11 (by decide)
  have free := keep (outputCrop 1) (by decide)
  change CropCounters (outputCrop.trans slots) B _ (A*tail) D at crop
  rw [rows,width] at crop
  obtain ⟨z,F,m,result,run,time,user,word,cells⟩ := scheduled x i v D
    (initial.after_entry frame) live
    (fun j l => by
      change readAt blank (D.L (slots (outputHeaders j))) (D.R (slots (outputHeaders j))) (l-1) = _
      rw [(hd j).1,(hd j).2]; exact outHeaders j l)
    (fun j a b => ⟨(rot j a).1.trans (outRot j a b).1,(rot j a).2.trans (outRot j a b).2⟩)
    (fun l => by
      change readAt blank (D.L (slots (outputRotation 11))) (D.R (slots (outputRotation 11))) l = _
      rw [dest.1,dest.2]; exact outDest l)
    crop
    (fun l => by
      change readAt blank (D.L (slots (outputCrop 1))) (D.R (slots (outputCrop 1))) l = _
      rw [free.1,free.2]; exact cropDest l)
    ((keep 92 (by decide)).2.trans (raw 6).2) ((hd 0).2.trans (raw 0).2)
    (fun j => (tr j).2.trans (outTranspose j)) ((tr 1).1.trans outLeft₁) ((tr 6).1.trans outLeft₆)
    pad blankOwner
  refine ⟨z,F,_,result,Exec.seq enterRun run,?_,user.trans same,word,cells⟩
  change n ≤ 23462*(A*(B*prime^(64*((w+1)*64))*tail))+583 at enterTime
  rw [rows,show A*(B*N*tail) = B*(N*K) by rw [← width]; ac_rfl] at enterTime
  have fee : (n : ℝ) ≤ 23462*(B*(N*K) : ℕ)+583 := by exact_mod_cast enterTime
  change (m : ℝ) ≤ _ + 22982*(B*(N*K) : ℕ)+599 at time
  push_cast at time fee ⊢
  linarith

private theorem sevenHeaderCharge {K N g B h D tail V : ℕ}
    (k : K ≤ V) (n : N ≤ V) (hg : g ≤ V) (b : B ≤ V) (hh : h ≤ V) (ab : D ≤ V) (small : tail ≤ V) :
    let vals : Fin 7 → ℕ := ![K,N,g,B,h,D,tail]
    ((List.finRange 7).map (fun i => 6*(vals i).size+6)).sum+2 ≤ 42*V+44 := by
  intro vals
  have bounds (j : Fin 7) : vals j ≤ V := by
    fin_cases j
    · exact k
    · exact n
    · exact hg
    · exact b
    · exact hh
    · exact ab
    · exact small
  have total := List.sum_le_length_nsmul ((List.finRange 7).map (fun i => 6*(vals i).size+6)) (6*V+6)
    (fun _ h => by obtain ⟨i,_,rfl⟩ := List.mem_map.mp h
                   have := (Nat.size_le.mpr (Nat.lt_two_pow_self (n := vals i))).trans (bounds i)
                   omega)
  simp only [List.length_map,List.length_finRange,nsmul_eq_mul] at total
  omega
private theorem headerCharge {w B W : ℕ} (hb : 0 < B) (hw : 0 < W) :
    let M := prime^(w+1)
    let A := M^16
    let tail := M^112*W
    let N := M^(64*64)
    let K := M^128*W
    let g := ordinaryIdentityRow (w+1)
    let idRow := LabelAddress.address (1 : LabelPadding.Label 64 (w+1))
    let vals : Fin 7 → ℕ := ![K,N,g.val,B,(0-idRow).val,A*B,tail]
    let V := B*(N*K)
    ((List.finRange 7).map (fun i => 6*(vals i).size+6)).sum+2 ≤ 42*V+44 := by
  intro M A tail N K g idRow vals V
  have posM : 0 < M := pow_pos IntegerMultBounds.Networks.Shared50ModularControl.prime_prime.pos _
  have posK : 0 < K := Nat.mul_pos (pow_pos posM _) hw
  have posN : 0 < N := pow_pos posM _
  have nk : N*K ≤ V := Nat.le_mul_of_pos_left _ hb
  have n := (Nat.le_mul_of_pos_right N posK).trans nk
  have k := (Nat.le_mul_of_pos_left K posN).trans nk
  have b : B ≤ V := Nat.le_mul_of_pos_right _ (Nat.mul_pos posN posK)
  have width : A*tail = K := ordinaryCompact_width M W
  have a : A ≤ K := width ▸ Nat.le_mul_of_pos_right A (Nat.mul_pos (pow_pos posM _) hw)
  have ab : A*B ≤ V := by rw [Nat.mul_comm]; exact Nat.mul_le_mul_left _ (a.trans (Nat.le_mul_of_pos_left K posN))
  have small : tail ≤ V := (Nat.le_mul_of_pos_left tail (pow_pos posM 16)).trans (width ▸ k)
  have grow : g.val ≤ N := by
    have h := g.isLt
    change _ < prime^(64*((w+1)*64)) at h
    change _ ≤ (prime^(w+1))^(64*64)
    rw [← pow_mul,show (w+1)*(64*64) = 64*((w+1)*64) by omega]; exact h.le
  exact sevenHeaderCharge k n (grow.trans n) b ((0-idRow).isLt.le.trans n) ab small

theorem ScheduledReturn.roundTrip [M8.Machine.Net] {V size back Q w B W : ℕ} {U : Type}
    {stage : SharedBankStage.Stage _ 1 prime (phaseOwners (N := V))} {words : Fin size → List (Fin (prime+4))}
    {interval : ℕ × ℕ} {parent : Fin 64 → ZMod (prime^(w+1))}
    {c : Certificates.PR589.Nine.PortCertificate} {checked : c.Checked}
    {body : Unit → Pr Unit ((size+stage.tapes+back)+99) Q prime U} {scan rate}
    (scheduled : ScheduledReturn (w := w) (B := B) (W := W) interval parent c checked
      (((stage.slots 0).natAdd size).castAdd back) (ScannerReady stage size back words) body scan rate)
    (hb : 0 < B) (hw : 0 < W) (fits : 235 ≤ Q) :
    ∃ code : Pr Unit ((size+stage.tapes+back)+99) Q prime U,
    let T := size+stage.tapes+back
    let owner := ((stage.slots 0).natAdd size).castAdd back
    let slots := aroundScanner owner
    let old := Fin.castAddEmb 99 (n := T)
    let layout := stagedScannerLayout w B W
    let M := prime^(w+1)
    let A := M^16
    let tail := M^112*W
    let N := M^(64*64)
    let K := M^128*W
    let g := ordinaryIdentityRow (w+1)
    let idRow := LabelAddress.address (1 : LabelPadding.Label 64 (w+1))
    ∀ (x : Fin 142081 → Fin (A*(B*tail)) → ZMod 2) i u S,
      ScannerReady stage size back words (embStk old S) →
      (∀ j : Fin 7, let n := (![K,N,g.val,B,(0-idRow).val,A*B,tail] : Fin 7 → ℕ) j
        S.R (retainedPort T j) = binSyms n.size n) →
      WordAtZero (singleLabelBank (firstRowLabel (w+1)) x i) (S.L (slots 0)) (S.R (slots 0)) →
      (∀ j, j ≠ 0 → S.L (slots j) = [] ∧ S.R (slots j) = []) →
      ∃ v F t, ∃ staged : Fin (M^16*(B*(M^112*W))) → ZMod 2, Exec body code (mk u S) t (mk v F) ∧
        (t : ℝ) ≤ (packedChartRate (0 : Fin 1) c checked false layout.width +
          packedChartRate (0 : Fin 1) c checked true layout.width + (366+16*64*64+19*64+344) +
          rate*((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau + 64*(8*64+21+28+(prime.size : ℝ)))*
          volume prime (role layout 142080) + 13 + 46486*(B*(N*K) : ℕ)+1226 ∧ v.user = u.user ∧
        WordAtZero (singleLabelBank (firstRowLabel (w+1)) (fun _ => staged) 0) (F.L (slots 0)) (F.R (slots 0)) ∧
      let proj := IntegerMultBounds.Swap.Modular.reduce M ((c.span interval.1 interval.2).submatrix stageAxis.symm stageAxis.symm)
      let frame := Matrix.fromBlocks (Matrix.diagonal parent) 0 0 (M8.ReversedExchange.rev 64)
      let addr := fun b y (k : Fin W) => stagedOwnerIndex b (FlatCoordinateLayout.index
        ((frame.mulVec y) ∘ (finSumFinEquiv : (Fin 64 ⊕ Fin 64) ≃ Fin 128).symm) k)
      ∀ b y k, staged (addr b ((Matrix.fromBlocks (1-proj) proj proj (1-proj)).mulVec y) k) = x i (addr b y k) := by
  let owner := ((stage.slots 0).natAdd size).castAdd back
  let slots := aroundScanner owner
  obtain ⟨load,copy⟩ := loadHeaders_exec body slots (retainedPort _) (retainedPort_private owner)
  obtain ⟨code,execute⟩ := scheduled.roundTripPrepared hb hw fits
  refine ⟨load.seq code,?_⟩
  intro T _ _ old layout M A tail N K g idRow x i u S initial sources live fresh
  let vals : Fin 7 → ℕ := ![K,N,g.val,B,(0-idRow).val,A*B,tail]
  obtain ⟨y,D,loadRun,same,headers,off⟩ := copy vals u S sources
    (fun i => fresh _ ((by decide : ∀ i, headerPorts i ≠ 0) i)) (fresh 13 (by decide)).2 (fresh 14 (by decide)).2
  have untouched (j : Fin 93) (h : ∀ i, headerPorts i ≠ j) := off (slots j) (fun i => slots.injective.ne (h i))
  have empty (j : Fin 93) (h : j ≠ 0 ∧ ∀ i, headerPorts i ≠ j) : D.L (slots j) = [] ∧ D.R (slots j) = [] :=
    ⟨(untouched j h.2).1.trans (fresh j h.1).1,(untouched j h.2).2.trans (fresh j h.1).2⟩
  have blankAt (j : Fin 93) (h : j ≠ 0 ∧ ∀ i, headerPorts i ≠ j) (z : ℤ) :
      readAt blank (D.L (slots j)) (D.R (slots j)) z = blank := by
    rw [(empty j h).1,(empty j h).2,readAt_nil_left,wordTape_nil]
  have ready : ScannerReady stage size back words (embStk old D) := by
    apply initial.of_owner_change
    intro j _
    exact off _ (fun i => (aroundScanner_private owner _ ((by decide : ∀ i, headerPorts i ≠ 1) i) j).symm)
  have srcLive := untouched 0 (by decide)
  have trans (j : Fin 8) := empty _ ((by decide : ∀ j, inputTranspose j ≠ 0 ∧ ∀ i, headerPorts i ≠ inputTranspose j) j)
  have ret (j : Fin 8) := empty _ ((by decide : ∀ j, outputTranspose j ≠ 0 ∧ ∀ i, headerPorts i ≠ outputTranspose j) j)
  obtain ⟨z,F,t,staged,run,time,user,word,cells⟩ := execute x i y D ready headers
    (fun b j hj => empty _ ((by decide +kernel : ∀ b (j : Fin 12), 2 ≤ j.val → paddingBanks b j ≠ 0 ∧ ∀ i, headerPorts i ≠ paddingBanks b j) b j hj))
    (by change WordAtZero _ (D.L (slots 0)) (D.R (slots 0)); rwa [srcLive.1,srcLive.2])
    (blankAt _ (by decide : inputCrop 1 ≠ 0 ∧ ∀ i, headerPorts i ≠ inputCrop 1))
    (trans 0).1 (trans 1).1 (fun j => (trans j).2)
    (blankAt _ (by decide : inputPad 1 ≠ 0 ∧ ∀ i, headerPorts i ≠ inputPad 1))
    (fun j _ _ => empty _ ((by decide : ∀ j, inputRotation j ≠ 0 ∧ ∀ i, headerPorts i ≠ inputRotation j) j))
    (blankAt 1 (by decide))
    (fun j _ _ => empty _ ((by decide : ∀ j, outputRotation j ≠ 0 ∧ ∀ i, headerPorts i ≠ outputRotation j) j))
    (blankAt _ (by decide : outputRotation 11 ≠ 0 ∧ ∀ i, headerPorts i ≠ outputRotation 11))
    (blankAt _ (by decide : outputCrop 1 ≠ 0 ∧ ∀ i, headerPorts i ≠ outputCrop 1))
    (fun j => (ret j).2) (ret 1).1 (ret 6).1
  refine ⟨z,F,_,staged,Exec.seq loadRun run,?_,user.trans same,word,cells⟩
  let V := B*(N*K)
  have charge := headerCharge (w := w) hb hw
  have fee : ((((List.finRange 7).map (fun i => 6*(vals i).size+6)).sum+2 : ℕ) : ℝ) ≤ 42*(V : ℝ)+44 := by exact_mod_cast charge
  change (t : ℝ) ≤ _ + 46444*(V : ℝ)+1182 at time
  change (((_ + t : ℕ) : ℝ)) ≤ _ + 46486*(V : ℝ)+1226
  rw [Nat.cast_add]
  linarith

end OrdinaryHandoff
end IntegerMultBounds.MathlibTM2.M6.BitNode
