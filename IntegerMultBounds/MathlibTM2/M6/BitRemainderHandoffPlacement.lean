module

public import IntegerMultBounds.MathlibTM2.M6.BitRemainderScannerTape

/-! Fixed local tape placement for the two handoffs surrounding one ordinary owner scan. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine Stack Host Cover
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open FlatCoordinateSchedule (bits)
local instance (w : ℕ) : NeZero (prime^w) := ⟨(pow_pos IntegerMultBounds.Networks.Shared50ModularControl.prime_prime.pos _).ne'⟩

namespace OrdinaryHandoff

/-- Slot zero holds the staging owner and slot one holds the scanner owner.
The remaining slots separate the two sets of scratch tapes so that a scan
can use its own metadata while the return workspace stays prepared. -/
def inputCrop : Fin 12 ↪ Fin 95 := ⟨![0,2,3,4,5,6,7,8,9,10,11,12],by decide⟩
def inputTranspose : Fin 8 ↪ Fin 95 := ⟨![13,14,15,16,17,18,19,20],by decide⟩
def inputPad : Fin 12 ↪ Fin 95 := ⟨![13,21,22,23,24,25,26,27,28,29,30,31],by decide⟩
def inputRotation : Fin 14 ↪ Fin 95 := ⟨![32,33,34,35,36,37,38,39,40,41,21,1,42,43],by decide⟩
def inputHeaders : Fin 4 ↪ Fin 95 := ⟨![44,45,46,47],by decide⟩
def outputRotation : Fin 14 ↪ Fin 95 := ⟨![48,49,50,51,52,53,54,55,56,57,1,58,59,60],by decide⟩
def outputCrop : Fin 12 ↪ Fin 95 := ⟨![58,61,62,63,64,65,66,67,68,69,70,71],by decide⟩
def outputTranspose : Fin 8 ↪ Fin 95 := ⟨![72,73,74,75,76,77,78,79],by decide⟩
def outputPad : Fin 12 ↪ Fin 95 := ⟨![78,0,80,81,82,83,84,85,86,87,88,89],by decide⟩
def outputHeaders : Fin 4 ↪ Fin 95 := ⟨![90,91,92,93],by decide⟩

theorem enter_exec {P U : Type} {T Q : ℕ} (body : P → Pr P T Q prime U)
    (fits : 235 ≤ Q) (slots : Fin 95 ↪ Fin T) :
    ∃ code, ∀ w B K, 0 < B → 0 < K →
      let A := (prime^w)^16
      let N := prime^(64*(w*64))
      let g := ordinaryIdentityRow w
      ∀ (x : Fin 142081 → Fin (A*(B*K)) → ZMod 2) i u S,
      WordAtZero (singleLabelBank (firstRowLabel w) x i) (S.L (slots 0)) (S.R (slots 0)) →
      (∀ z, readAt blank (S.L ((inputCrop.trans slots) 1)) (S.R ((inputCrop.trans slots) 1)) z = blank) → CropCounters (inputCrop.trans slots) (A*B) N K S →
      ∀ (record rowWidth : List (Fin (prime+4))), record.length = K → rowWidth.length = B*K →
      S.L ((inputTranspose.trans slots) 0) = [] → S.L ((inputTranspose.trans slots) 1) = [] →
      (∀ j, S.R ((inputTranspose.trans slots) j) = (transposeStacks (embStk (inputTranspose.trans slots) S) [] [] [] record rowWidth).R j) →
      (∀ z, readAt blank (S.L ((inputPad.trans slots) 1)) (S.R ((inputPad.trans slots) 1)) z = blank) →
      CropCounters (inputPad.trans slots) B N (A*K) S →
      (∀ j z, readAt blank (S.L ((inputHeaders.trans slots) j)) (S.R ((inputHeaders.trans slots) j)) (z-1) =
        RadixZeroFill.encodedBinary (bits (![A*K,N,g.val,B] j)) z) →
      (∀ j : Fin 14, j ≠ 10 → j ≠ 11 → S.L ((inputRotation.trans slots) j) = [] ∧ S.R ((inputRotation.trans slots) j) = []) →
      (∀ z, readAt blank (S.L (slots 1)) (S.R (slots 1)) z = blank) →
      ∃ v F t, Exec body code (mk u S) t (mk v F) ∧ t ≤ 22944*(A*(B*N*K))+583 ∧
        v.user = u.user ∧ WordAtZero (fun j => singleLabelBank (firstRowLabel w) x i
          ((ordinaryRowLayout (Equiv.swap 0 g)).symm j)) (F.L (slots 1)) (F.R (slots 1)) ∧
        (∀ l, readAt blank (F.L (slots 0)) (F.R (slots 0)) l = blank) ∧
        ∀ j, (∀ i, (inputCrop.trans slots) i ≠ j) → (∀ i, (inputTranspose.trans slots) i ≠ j) → (∀ i, (inputPad.trans slots) i ≠ j) → (∀ i, (inputRotation.trans slots) i ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  apply stagingToIdentity_exec body (inputCrop.trans slots) (inputTranspose.trans slots) _ fits
    (inputPad.trans slots) (inputRotation.trans slots) (inputHeaders.trans slots)
  all_goals simp only [Function.Embedding.trans_apply,ne_eq,slots.injective.eq_iff]
  all_goals decide +kernel

theorem leave_exec {P U : Type} {T Q : ℕ} (body : P → Pr P T Q prime U)
    (fits : 235 ≤ Q) (slots : Fin 95 ↪ Fin T) :
    ∃ code, ∀ {w B W : ℕ} {interval parent c}, 0 < B → 0 < W →
      let M := prime^(w+1)
      let N := M^(64*64)
      let K := M^128*W
      let idRow := LabelAddress.address (1 : LabelPadding.Label 64 (w+1))
      ∀ (input output : Fin ((B*N)*K) → ZMod 2),
      OriginalPortReads _ W B interval parent c input output → c.Checked → (∀ i, IsUnit (parent i)) →
      (∀ b j k, j ≠ idRow → input (finProdFinEquiv (finProdFinEquiv (b,j),k)) = 0) →
      ∀ u S, (∀ i z, readAt blank (S.L ((outputHeaders.trans slots) i)) (S.R ((outputHeaders.trans slots) i)) (z-1) =
        RadixZeroFill.encodedBinary (bits (![K,N,(0-idRow).val,B] i)) z) →
      (∀ j : Fin 14, j ≠ 10 → j ≠ 11 → S.L ((outputRotation.trans slots) j) = [] ∧ S.R ((outputRotation.trans slots) j) = []) →
      WordAtZero output (S.L (slots 1)) (S.R (slots 1)) →
      (∀ z, readAt blank (S.L ((outputRotation.trans slots) 11)) (S.R ((outputRotation.trans slots) 11)) z = blank) →
      CropCounters (outputCrop.trans slots) B N K S →
      (∀ z, readAt blank (S.L ((outputCrop.trans slots) 1)) (S.R ((outputCrop.trans slots) 1)) z = blank) →
      S.R (slots 94) = binSyms (M^112*W).size (M^112*W) →
      S.R (slots (outputHeaders 0)) = binSyms K.size K →
      (∀ i, S.R ((outputTranspose.trans slots) i) = []) → S.L ((outputTranspose.trans slots) 1) = [] →
      S.L ((outputTranspose.trans slots) 6) = [] →
      CropCounters (outputPad.trans slots) (M^16*B) (prime^(64*((w+1)*64))) (M^112*W) S →
      (∀ z, readAt blank (S.L (slots 0)) (S.R (slots 0)) z = blank) →
      ∃ v F t, ∃ staged : Fin (M^16*(B*(M^112*W))) → ZMod 2, Exec body code (mk u S) t (mk v F) ∧ t ≤ 22982*(B*(N*K))+599 ∧ v.user = u.user ∧
        WordAtZero (singleLabelBank (firstRowLabel (w+1)) (fun _ => staged) 0) (F.L (slots 0)) (F.R (slots 0)) ∧
        (∀ (a : Fin (M^16)) (b : Fin B) (k : Fin (M^112*W)),
          staged (finProdFinEquiv (a,finProdFinEquiv (b,k))) = output (finProdFinEquiv
            (finProdFinEquiv (b,idRow),(finProdFinEquiv (a,k)).cast (ordinaryCompact_width M W)))) ∧
        ∀ j, (∀ i, (outputRotation.trans slots) i ≠ j) → (∀ i, (outputCrop.trans slots) i ≠ j) → (∀ i, (outputTranspose.trans slots) i ≠ j) → (∀ i, (outputPad.trans slots) i ≠ j) →
          F.L j = S.L j ∧ F.R j = S.R j := by
  apply ordinaryReturn_exec body fits (outputRotation.trans slots) (outputHeaders.trans slots) _
    (outputCrop.trans slots) _ _ (outputTranspose.trans slots) _ (outputPad.trans slots) _ _
    (slots 94) (slots (outputHeaders 0))
  all_goals simp only [Function.Embedding.trans_apply,ne_eq,slots.injective.eq_iff]
  all_goals decide +kernel

/-- Share slot one with the scanner owner. Every other handoff slot is placed
after the scanner's last tape, including the caller's staging owner. -/
def aroundScanner {T : ℕ} (owner : Fin T) : Fin 95 ↪ Fin (T+94) where
  toFun i := Fin.succAboveCases (1 : Fin 95) (owner.castAdd 94) (Fin.natAdd T) i
  inj' := by
    intro i j
    induction i using Fin.succAboveCases (1 : Fin 95) <;>
      induction j using Fin.succAboveCases (1 : Fin 95) <;>
      simp
    all_goals intro eq; have h := congrArg Fin.val eq; simp only [Fin.val_castAdd,Fin.val_natAdd] at h; omega

@[simp] theorem aroundScanner_owner {T : ℕ} (owner : Fin T) :
    aroundScanner owner 1 = owner.castAdd 94 := by simp [aroundScanner]

theorem aroundScanner_private {T : ℕ} (owner : Fin T) (j : Fin 95) (hj : j ≠ 1) :
    ∀ i : Fin T, i.castAdd 94 ≠ aroundScanner owner j := by
  induction j using Fin.succAboveCases (1 : Fin 95) with
  | x => contradiction
  | p k =>
    intro i eq
    have h := congrArg Fin.val eq
    simp [aroundScanner] at h
    omega

/-- Place a native scanner execution in the shared host. The execution costs
the same number of steps and preserves every private handoff tape. -/
theorem scan_exec {P U : Type} {T Q : ℕ} (body : P → Pr P T Q prime U)
    (code : Pr P T Q prime U) (owner : Fin T) (u : HS (T+94) Q prime U) (S : Stacks (T+94) prime)
    {v D t} (run : Exec body code (mk (embDn (Fin.castAddEmb 94) u) (embStk (Fin.castAddEmb 94) S)) t (mk v D)) :
    ∃ z F, Exec (fun p => embProg (Fin.castAddEmb 94) id (body p))
        (embProg (Fin.castAddEmb 94) id code) (mk u S) t (mk z F) ∧ z.user = v.user ∧
      embStk (Fin.castAddEmb 94) F = D ∧
      ∀ j : Fin 95, j ≠ 1 → F.L (aroundScanner owner j) = S.L (aroundScanner owner j) ∧
        F.R (aroundScanner owner j) = S.R (aroundScanner owner j) := by
  obtain ⟨z,F,placed,_,same,view,off⟩ := exec_emb (ι := id) (body' := fun p => embProg (Fin.castAddEmb 94) id (body p)) (Fin.castAddEmb 94).injective
    (fun _ => rfl) run u rfl S rfl
  exact ⟨z,F,placed,same,view,fun j hj => off _ (aroundScanner_private owner j hj)⟩

end OrdinaryHandoff
end IntegerMultBounds.MathlibTM2.M6.BitNode
