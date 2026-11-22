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

/-- Run the native scanner, then restore the staged owner using the private return workspace. -/
theorem scanAndLeave_exec {P U : Type} {T Q : ℕ} (body : P → Pr P T Q prime U)
    (fits : 235 ≤ Q) (scan : Pr P T Q prime U) (owner : Fin T) :
    let slots := aroundScanner owner
    let old := Fin.castAddEmb 94 (n := T)
    let outer := fun p => embProg old id (body p)
    ∃ code, ∀ {w B W : ℕ} {interval parent c}, 0 < B → 0 < W →
      let M := prime^(w+1)
      let N := M^(64*64)
      let K := M^128*W
      let idRow := LabelAddress.address (1 : LabelPadding.Label 64 (w+1))
      let layout := stagedScannerLayout w B W
      let R := LabelMask.records (RecursiveInterchangeLayout.role layout 142080)
      let width := M^128*(layout.between*layout.afterD)
      ∀ (x : Fin 142081 → Fin (M^16*(B*(M^112*W))) → ZMod 2) i u S (budget : ℝ),
      c.Checked → (∀ i, IsUnit (parent i)) →
      WordAtZero (fun j => singleLabelBank (firstRowLabel (w+1)) x i
        ((ordinaryRowLayout (Equiv.swap 0 (ordinaryIdentityRow (w+1)))).symm j)) (S.L (slots 1)) (S.R (slots 1)) →
      (∀ words : Fin 1 → Fin (R*width) → ZMod 2,
        RepT (phaseOwners words) (fun _ => S.L (slots 1)) (fun _ => S.R (slots 1)) →
        ∃ z F n, ∃ final : Fin 1 → Fin (R*width) → ZMod 2,
          Exec body scan (mk (embDn old u) (embStk old S)) n (mk z F) ∧
          (z.user = u.user ∧ (n : ℝ) ≤ budget) ∧
          RepT (phaseOwners final) (fun _ => F.L owner) (fun _ => F.R owner) ∧
          OriginalPortReads R (layout.between*layout.afterD) (layout.beforeRows*1*B) interval parent c (words 0) (final 0)) →
      (∀ i z, readAt blank (S.L ((outputHeaders.trans slots) i)) (S.R ((outputHeaders.trans slots) i)) (z-1) =
        RadixZeroFill.encodedBinary (bits (![K,N,(0-idRow).val,B] i)) z) →
      (∀ j : Fin 14, j ≠ 10 → j ≠ 11 → S.L ((outputRotation.trans slots) j) = [] ∧ S.R ((outputRotation.trans slots) j) = []) →
      (∀ z, readAt blank (S.L ((outputRotation.trans slots) 11)) (S.R ((outputRotation.trans slots) 11)) z = blank) →
      CropCounters (outputCrop.trans slots) B N K S →
      (∀ z, readAt blank (S.L ((outputCrop.trans slots) 1)) (S.R ((outputCrop.trans slots) 1)) z = blank) →
      S.R (slots 94) = binSyms (M^112*W).size (M^112*W) →
      S.R (slots (outputHeaders 0)) = binSyms K.size K →
      (∀ i, S.R ((outputTranspose.trans slots) i) = []) → S.L ((outputTranspose.trans slots) 1) = [] →
      S.L ((outputTranspose.trans slots) 6) = [] →
      CropCounters (outputPad.trans slots) (M^16*B) (prime^(64*((w+1)*64))) (M^112*W) S →
      (∀ z, readAt blank (S.L (slots 0)) (S.R (slots 0)) z = blank) →
      ∃ v F t, ∃ staged : Fin (M^16*(B*(M^112*W))) → ZMod 2, Exec outer code (mk u S) t (mk v F) ∧ (t : ℝ) ≤ budget + 22982*(B*(N*K) : ℕ)+599 ∧ v.user = u.user ∧
        WordAtZero (singleLabelBank (firstRowLabel (w+1)) (fun _ => staged) 0) (F.L (slots 0)) (F.R (slots 0)) ∧
      let proj := IntegerMultBounds.Swap.Modular.reduce M ((c.span interval.1 interval.2).submatrix stageAxis.symm stageAxis.symm)
      let frame := Matrix.fromBlocks (Matrix.diagonal parent) 0 0 (M8.ReversedExchange.rev 64)
      let addr := fun b y (k : Fin W) => stagedOwnerIndex b (FlatCoordinateLayout.index
        ((frame.mulVec y) ∘ (finSumFinEquiv : (Fin 64 ⊕ Fin 64) ≃ Fin 128).symm) k)
      ∀ b y k, staged (addr b ((Matrix.fromBlocks (1-proj) proj proj (1-proj)).mulVec y) k) = x i (addr b y k) := by
  intro slots old outer
  obtain ⟨leave,exit⟩ := leave_exec outer fits slots
  refine ⟨(embProg old id scan).seq leave,?_⟩
  intro w B W interval parent c hb hw M N K idRow layout R width x i u S budget checked units entry execute
    headers rotation dest crop cropDest tailWidth rowWidth transpose left₁ left₆ pad staging
  have slot : slots 1 = old owner := aroundScanner_owner owner
  rw [slot] at entry execute
  obtain ⟨scannerState,D,time,input,output,native,⟨sameUser,timeBound⟩,word,reads,cells⟩ :=
    stagedScannerTape_exec (interval := interval) (parent := parent) (c := c) body scan owner (embDn old u) (embStk old S)
      (fun z _ n => z.user = u.user ∧ (n : ℝ) ≤ budget) x i entry execute
  have supported : ∀ b j k, j ≠ idRow → input (finProdFinEquiv (finProdFinEquiv (b,j),k)) = 0 := by
    intro b j k hj
    obtain ⟨small,h⟩ := (finCongr (ordinaryCompact_width M W)).surjective k
    obtain ⟨⟨a,k⟩,rfl⟩ := finProdFinEquiv.surjective small
    change (finProdFinEquiv (a,k)).cast (ordinaryCompact_width M W) = _ at h
    rw [← h,cells,ite_eq_right hj]
  obtain ⟨y,E,run,user,view,privateTape⟩ := scan_exec body scan owner u S native
  have left (j : Fin 95) (h : j ≠ 1) : E.L (slots j) = S.L (slots j) := (privateTape j h).1
  have right (j : Fin 95) (h : j ≠ 1) : E.R (slots j) = S.R (slots j) := (privateTape j h).2
  have counters (bank : Fin 12 ↪ Fin 95) (apart : ∀ k, k ≠ 0 → k ≠ 1 → bank k ≠ 1)
      {b n k} (ready : CropCounters (bank.trans slots) b n k S) : CropCounters (bank.trans slots) b n k E := by
    intro j h₀ h₁ z
    simp only [Function.Embedding.trans_apply,left _ (apart j h₀ h₁),right _ (apart j h₀ h₁)]
    exact ready j h₀ h₁ z
  have live : WordAtZero output (E.L (slots 1)) (E.R (slots 1)) := by
    rw [← view] at word
    simpa only [slots,aroundScanner_owner,embStk,Function.comp_apply,Fin.castAddEmb_apply] using word
  obtain ⟨z,F,m,staged,finish,paid,same,out,action,_⟩ :=
    exit hb hw input output reads checked units supported y E
      (fun j l => by
        have h := (by decide : ∀ j, outputHeaders j ≠ 1) j
        simpa only [Function.Embedding.trans_apply,left _ h,right _ h] using headers j l)
      (fun j h₀ h₁ => by
        have h := (by decide : ∀ j : Fin 14, j ≠ 10 → outputRotation j ≠ 1) j h₀
        exact ⟨(left _ h).trans (rotation j h₀ h₁).1,(right _ h).trans (rotation j h₀ h₁).2⟩)
      live (fun l => by simpa only [Function.Embedding.trans_apply,left _ (by decide : outputRotation 11 ≠ 1),right _ (by decide : outputRotation 11 ≠ 1)] using dest l)
      (counters _ (by decide) crop)
      (fun l => by simpa only [Function.Embedding.trans_apply,left _ (by decide : outputCrop 1 ≠ 1),right _ (by decide : outputCrop 1 ≠ 1)] using cropDest l)
      ((right 94 (by decide)).trans tailWidth) ((right (outputHeaders 0) (by decide)).trans rowWidth)
      (fun j => (right _ ((by decide : ∀ j, outputTranspose j ≠ 1) j)).trans (transpose j))
      ((left (outputTranspose 1) (by decide)).trans left₁) ((left (outputTranspose 6) (by decide)).trans left₆)
      (counters _ (by decide) pad)
      (fun l => by simpa only [left _ (by decide : (0 : Fin 95) ≠ 1),right _ (by decide : (0 : Fin 95) ≠ 1)] using staging l)
  change m ≤ 22982*(B*(N*K))+599 at paid
  refine ⟨z,F,_,staged,Exec.seq run finish,?_,same.trans (user.trans sameUser),out,
    reads.stagedExchange input output (x i) staged units cells action⟩
  have fee : (m : ℝ) ≤ 22982*(B*(N*K) : ℕ)+599 := by exact_mod_cast paid
  push_cast at fee ⊢
  linarith

end OrdinaryHandoff
end IntegerMultBounds.MathlibTM2.M6.BitNode
