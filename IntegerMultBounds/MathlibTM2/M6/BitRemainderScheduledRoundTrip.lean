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

private def returnSlot (j : Fin 95) : Bool :=
  (48 ≤ j.val && j.val ≤ 61) || (72 ≤ j.val && j.val ≤ 79) || 90 ≤ j.val

/-- Both directions and the scheduled scanner act on the same staging owner.
Only initial workspace conditions are required. -/
theorem ScheduledReturn.roundTrip [M8.Machine.Net] {V size back Q w B W : ℕ} {U : Type}
    {stage : SharedBankStage.Stage _ 1 prime (phaseOwners (N := V))} {words : Fin size → List (Fin (prime+4))}
    {interval : ℕ × ℕ} {parent : Fin 64 → ZMod (prime^(w+1))}
    {c : Certificates.PR589.Nine.PortCertificate} {checked : c.Checked}
    {body : Unit → Pr Unit ((size+stage.tapes+back)+94) Q prime U} {scan rate}
    (scheduled : ScheduledReturn (w := w) (B := B) (W := W) interval parent c checked
      (((stage.slots 0).natAdd size).castAdd back) (ScannerReady stage size back words) body scan rate)
    (hb : 0 < B) (hw : 0 < W) (fits : 235 ≤ Q)
    (staging : Fin 3 → Fin ((size+stage.tapes+back)+94))
    (apart : ∀ i j k, staging i ≠ aroundScanner (((stage.slots 0).natAdd size).castAdd back) (paddingBanks j k)) :
    ∃ code : Pr Unit ((size+stage.tapes+back)+94) Q prime U,
    let T := size+stage.tapes+back
    let owner := ((stage.slots 0).natAdd size).castAdd back
    let slots := aroundScanner owner
    let old := Fin.castAddEmb 94 (n := T)
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
      StageDimensionWords staging tail N (A*B) S →
      (∀ b j, 2 ≤ j.val → S.L (slots (paddingBanks b j)) = [] ∧ S.R (slots (paddingBanks b j)) = []) →
      WordAtZero (singleLabelBank (firstRowLabel (w+1)) x i) (S.L (slots 0)) (S.R (slots 0)) →
      (∀ z, readAt blank (S.L ((inputCrop.trans slots) 1)) (S.R ((inputCrop.trans slots) 1)) z = blank) →
      ∀ (record rowWidth : List (Fin (prime+4))), record.length = tail → rowWidth.length = B*tail →
      S.L ((inputTranspose.trans slots) 0) = [] → S.L ((inputTranspose.trans slots) 1) = [] →
      (∀ j, S.R ((inputTranspose.trans slots) j) = (transposeStacks (embStk (inputTranspose.trans slots) S) [] [] [] record rowWidth).R j) →
      (∀ z, readAt blank (S.L ((inputPad.trans slots) 1)) (S.R ((inputPad.trans slots) 1)) z = blank) →
      (∀ j z, readAt blank (S.L ((inputHeaders.trans slots) j)) (S.R ((inputHeaders.trans slots) j)) (z-1) =
        RadixZeroFill.encodedBinary (bits (![A*tail,N,g.val,B] j)) z) →
      (∀ j : Fin 14, j ≠ 10 → j ≠ 11 → S.L ((inputRotation.trans slots) j) = [] ∧ S.R ((inputRotation.trans slots) j) = []) →
      (∀ z, readAt blank (S.L (slots 1)) (S.R (slots 1)) z = blank) →
      (∀ i z, readAt blank (S.L ((outputHeaders.trans slots) i)) (S.R ((outputHeaders.trans slots) i)) (z-1) =
        RadixZeroFill.encodedBinary (bits (![K,N,(0-idRow).val,B] i)) z) →
      (∀ j : Fin 14, j ≠ 10 → j ≠ 11 → S.L ((outputRotation.trans slots) j) = [] ∧ S.R ((outputRotation.trans slots) j) = []) →
      (∀ z, readAt blank (S.L ((outputRotation.trans slots) 11)) (S.R ((outputRotation.trans slots) 11)) z = blank) →
      (∀ z, readAt blank (S.L ((outputCrop.trans slots) 1)) (S.R ((outputCrop.trans slots) 1)) z = blank) →
      S.R (slots 94) = binSyms (M^112*W).size (M^112*W) →
      S.R (slots (outputHeaders 0)) = binSyms K.size K →
      (∀ i, S.R ((outputTranspose.trans slots) i) = []) → S.L ((outputTranspose.trans slots) 1) = [] →
      S.L ((outputTranspose.trans slots) 6) = [] →
      ∃ v F t, ∃ staged : Fin (M^16*(B*(M^112*W))) → ZMod 2, Exec body code (mk u S) t (mk v F) ∧
        (t : ℝ) ≤ (packedChartRate (0 : Fin 1) c checked false layout.width +
          packedChartRate (0 : Fin 1) c checked true layout.width + (366+16*64*64+19*64+344) +
          rate*((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau + 64*(8*64+21+28+(prime.size : ℝ)))*
          volume prime (role layout 142080) + 13 + 46227*(B*(N*K) : ℕ)+1182 ∧ v.user = u.user ∧
        WordAtZero (singleLabelBank (firstRowLabel (w+1)) (fun _ => staged) 0) (F.L (slots 0)) (F.R (slots 0)) ∧
      let proj := IntegerMultBounds.Swap.Modular.reduce M ((c.span interval.1 interval.2).submatrix stageAxis.symm stageAxis.symm)
      let frame := Matrix.fromBlocks (Matrix.diagonal parent) 0 0 (M8.ReversedExchange.rev 64)
      let addr := fun b y (k : Fin W) => stagedOwnerIndex b (FlatCoordinateLayout.index
        ((frame.mulVec y) ∘ (finSumFinEquiv : (Fin 64 ⊕ Fin 64) ≃ Fin 128).symm) k)
      ∀ b y k, staged (addr b ((Matrix.fromBlocks (1-proj) proj proj (1-proj)).mulVec y) k) = x i (addr b y k) := by
  let slots := aroundScanner (((stage.slots 0).natAdd size).castAdd back)
  obtain ⟨enter,forward⟩ := prepareAndEnter_exec body fits slots staging apart
  refine ⟨enter.seq scan,?_⟩
  intro _ _ _ _ layout M A tail N K g idRow x i u S initial dims fresh ownerWord cropBlank record rowWidth
    recordLen rowLen left₀ left₁ transpose padBlank headers rotFree scannerBlank
    outHeaders outRot outDest cropDest tailDigits rowDigits outTranspose outLeft₁ outLeft₆
  have rows : prime^(64*((w+1)*64)) = N := by
    change _ = (prime^(w+1))^(64*64)
    rw [← pow_mul]; congr 1; omega
  have width : A*tail = K := ordinaryCompact_width M W
  obtain ⟨v,D,n,enterRun,enterTime,same,live,blankOwner,crop,pad,frame⟩ :=
    forward (w+1) B tail hb (Nat.mul_pos (pow_pos (pow_pos IntegerMultBounds.Networks.Shared50ModularControl.prime_prime.pos _) _) hw)
      x i u S (by rwa [rows]) fresh ownerWord cropBlank record rowWidth recordLen rowLen left₀ left₁ transpose padBlank
      (by simpa only [rows] using headers) rotFree scannerBlank
  have keep (j : Fin 95) (h : returnSlot j) : D.L (slots j) = S.L (slots j) ∧ D.R (slots j) = S.R (slots j) := by
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
    ((keep 94 (by decide)).2.trans tailDigits) ((hd 0).2.trans rowDigits)
    (fun j => (tr j).2.trans (outTranspose j)) ((tr 1).1.trans outLeft₁) ((tr 6).1.trans outLeft₆)
    pad blankOwner
  refine ⟨z,F,_,result,Exec.seq enterRun run,?_,user.trans same,word,cells⟩
  change n ≤ 23245*(A*(B*prime^(64*((w+1)*64))*tail))+583 at enterTime
  rw [rows,show A*(B*N*tail) = B*(N*K) by rw [← width]; ac_rfl] at enterTime
  have fee : (n : ℝ) ≤ 23245*(B*(N*K) : ℕ)+583 := by exact_mod_cast enterTime
  change (m : ℝ) ≤ _ + 22982*(B*(N*K) : ℕ)+599 at time
  push_cast at time fee ⊢
  linarith

end OrdinaryHandoff
end IntegerMultBounds.MathlibTM2.M6.BitNode
