module

public import IntegerMultBounds.MathlibTM2.M6.BitRemainderScheduledReturn
public import IntegerMultBounds.MathlibTM2.M6.BitRemainderRowAddress

public import IntegerMultBounds.MathlibTM2.Cover.FallbackRecordVolumeHeaders

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

/-- Once the forward shift is written at row-count width, one subtraction
and two trims produce both canonical rotation headers. -/
theorem rotationHeaders_exec {T Q : ℕ} {P U : Type} (body : P → Pr P T Q prime U)
    (r : Fin 7 ↪ Fin T) :
    ∃ code, ∀ (N g : ℕ) (hg : g ≤ N) (u : HS T Q prime U) (S : Stacks T prime),
      S.R (r 0) = binSyms N.size N → S.R (r 1) = binSyms N.size g →
      (∀ i : Fin 7, 2 ≤ i → i < 6 → S.R (r i) = []) →
      ∃ z, z.user = u.user ∧ Exec body code (mk u S) (16*N.size+20)
        (mk z {S with R := Function.update (Function.update S.R (r 2)
          (binSyms (N-g).size (N-g))) (r 1) (binSyms g.size g)}) := by
  refine ⟨(bsub (r 0) (r 1) (r 2) (r 3) (r 4) (r 5) (r 6)).seq
    ((Routing.binaryCanonicalProgram (r 2) (r 3)).seq (Routing.binaryCanonicalProgram (r 1) (r 3))),?_⟩
  intro N g hg u S rows shift free
  have hn := Nat.lt_size_self N
  obtain ⟨v,vu,_,_,sub⟩ := bsub_exec body (a := r 0) (b := r 1) (c := r 2)
    (tx := r 3) (ty := r 4) (tz := r 5) (cy := r 6) (by simp [List.nodup_cons,r.injective.eq_iff])
    (r.injective.ne (by decide)) (r.injective.ne (by decide)) hn (hg.trans_lt hn) u S rows shift
    (free 3 (by decide) (by decide)) (free 4 (by decide) (by decide)) (free 5 (by decide) (by decide))
  rw [free 2 (by decide) (by decide),List.append_nil,show N+2^N.size-g = (N-g)+2^N.size by omega,
    Nat.add_mod_right,Nat.mod_eq_of_lt ((Nat.sub_le N g).trans_lt hn)] at sub
  let D : Stacks T prime := {S with R := Function.update S.R (r 2) (binSyms N.size (N-g))}
  obtain ⟨bs,y,hc,hv,_,yv,back⟩ := Routing.binaryCanonical_exec body (r 2) (r 3)
    (r.injective.ne (by decide)) _ _ ((Nat.sub_le N g).trans_lt hn) v D (by simp [D])
    (by simp [D,r.injective.eq_iff,free 3 (by decide) (by decide)])
  have canonical {bs : List Bool} {x : ℕ} (hc : GrowingCounterData.Canonical bs) (hv : Counter.value bs = x) :
      bs.map (bitSymbol (a := prime)) = binSyms x.size x := by
    rw [BinaryCanonicalData.value_injective bs (bits x) hc (FlatCoordinateSchedule.bits_canonical _)
      (hv.trans (FlatCoordinateSchedule.bits_value _).symm),canonicalBits_symbols]
  simp only [canonical hc hv,D,Function.update_idem] at back
  let E : Stacks T prime := {S with R := Function.update S.R (r 2) (binSyms (N-g).size (N-g))}
  obtain ⟨bs,z,hc,hv,_,zy,fwd⟩ := Routing.binaryCanonical_exec body (r 1) (r 3)
    (r.injective.ne (by decide)) _ _ (hg.trans_lt hn) y E (by simp [E,r.injective.eq_iff,shift])
    (by simp [E,r.injective.eq_iff,free 3 (by decide) (by decide)])
  rw [canonical hc hv] at fwd
  exact ⟨z,zy.trans (yv.trans vu),(Exec.seq sub (Exec.seq back fwd)).cast (by omega) rfl⟩

/-- Construct the ordinary row width from the retained tail and the modulus.
The dimension program restores both inputs and every temporary register. -/
theorem ordinaryRowWidth_exec {T Q : ℕ} {P U : Type} (body : P → Pr P T Q prime U)
    (r : Fin 10 ↪ Fin T) (M W : ℕ) (u : HS T Q prime U) (S : Stacks T prime)
    (base : S.R (r 0) = binSyms M.size M)
    (tail : S.R (r 1) = binSyms (M^112*W).size (M^112*W))
    (free : ∀ i : Fin 10, 2 ≤ i → i < 9 → S.R (r i) = []) :
    let J := (M^112*W).size
    let K := M^128*W
    ∃ v t, v.user = u.user ∧ t ≤ Cover.Fallback.dimensionTime M.size J 16 + (4*(16*M.size+J)+6) ∧
      Exec body (Cover.Fallback.swapPrefix r 16) (mk u S) t
        (mk v {S with R := Function.update S.R (r 2) (binSyms K.size K)}) := by
  have width : M^16*(M^112*W) = M^128*W := by rw [← Nat.mul_assoc,← pow_add]
  simpa only [Cover.Fallback.canonicalBits_symbols,width] using
    Cover.Fallback.scaledPrefix_exec body r 16 M.size (M^112*W).size M (M^112*W)
      (Nat.lt_size_self _) (Nat.lt_size_self _) u S base tail free

/-- Read the modulus in the scanner entry bank. The tail and result use retained
ports 6 and 0. The remaining seven tapes borrow idle handoff slots. -/
def widthRegisters {T : ℕ} (base : Fin T) : Fin 10 ↪ Fin (T+99) where
  toFun := Fin.cases (base.castAdd 99) (fun i : Fin 9 =>
    ((![98,92,1,2,3,4,5,6,7] : Fin 9 → Fin 99) i).natAdd T)
  inj' := by
    intro i j
    cases i using Fin.cases <;> cases j using Fin.cases <;> simp
    all_goals intro h
    all_goals first
      | exact (by decide : Function.Injective (![98,92,1,2,3,4,5,6,7] : Fin 9 → Fin 99)) h
      | have e := congrArg Fin.val h; simp at e; omega

private theorem ScheduledReturn.roundTripWithOffsets [M8.Machine.Net] {V size back Q w B W : ℕ} {U : Type}
    {stage : SharedBankStage.Stage _ 1 prime (phaseOwners (N := V))} {words : Fin size → List (Fin (prime+4))}
    {interval : ℕ × ℕ} {parent : Fin 64 → ZMod (prime^(w+1))}
    {c : Certificates.PR589.Nine.PortCertificate} {checked : c.Checked}
    {body : Unit → Pr Unit ((size+stage.tapes+back)+99) Q prime U} {scan rate}
    (scheduled : ScheduledReturn (w := w) (B := B) (W := W) interval parent c checked
      (((stage.slots 0).natAdd size).castAdd back) (ScannerReady stage size back words) body scan rate)
    (modulus : Fin size) (modulusWord : words modulus = binSyms (prime^(w+1)).size (prime^(w+1)))
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
    let offset := diagonalPrefix (M^65) 64
    ∀ (x : Fin 142081 → Fin (A*(B*tail)) → ZMod 2) i u S,
      ScannerReady stage size back words (embStk old S) →
      S.R (retainedPort T 0) = [] →
      (∀ j : Fin 7, j ≠ 0 → let n := (![K,N,offset,B,N-offset,A*B,tail] : Fin 7 → ℕ) j
        S.R (retainedPort T j) = binSyms n.size n) →
      WordAtZero (singleLabelBank (firstRowLabel (w+1)) x i) (S.L (slots 0)) (S.R (slots 0)) →
      (∀ j, j ≠ 0 → S.L (slots j) = [] ∧ S.R (slots j) = []) →
      ∃ v F t, ∃ staged : Fin (M^16*(B*(M^112*W))) → ZMod 2, Exec body code (mk u S) t (mk v F) ∧
        (t : ℝ) ≤ (packedChartRate (0 : Fin 1) c checked false layout.width +
          packedChartRate (0 : Fin 1) c checked true layout.width + (366+16*64*64+19*64+344) +
          rate*((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau + 64*(8*64+21+28+(prime.size : ℝ)))*
          volume prime (role layout 142080) + 13 + 46486*(B*(N*K) : ℕ)+1226 + (dimensionTime M.size tail.size 16 + (4*(16*M.size+tail.size)+6) : ℕ) ∧ v.user = u.user ∧
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
  let src := (modulus.castAdd stage.tapes).castAdd back
  let r := widthRegisters src
  have seedPort : r 1 = retainedPort _ 6 := rfl
  have widthPort : r 2 = retainedPort _ 0 := rfl
  refine ⟨(swapPrefix r 16).seq (load.seq code),?_⟩
  intro T _ _ old layout M A tail N K offset x i u S initial widthEmpty sources live fresh
  have base : S.R (r 0) = binSyms M.size M := (initial.2.1 modulus).2.trans modulusWord
  have free (j : Fin 10) (lo : 2 ≤ j) (hi : j < 9) : S.R (r j) = [] := by
    fin_cases j <;> first | exact False.elim (by revert lo hi; decide) | exact widthEmpty | first
      | exact (fresh 2 (by decide)).2
      | exact (fresh 3 (by decide)).2
      | exact (fresh 4 (by decide)).2
      | exact (fresh 5 (by decide)).2
      | exact (fresh 6 (by decide)).2
      | exact (fresh 7 (by decide)).2
  let g := ordinaryIdentityRow (w+1)
  let idRow := LabelAddress.address (1 : LabelPadding.Label 64 (w+1))
  let vals : Fin 7 → ℕ := ![K,N,g.val,B,(0-idRow).val,A*B,tail]
  obtain ⟨v,s,vu,hs,widthRun⟩ := ordinaryRowWidth_exec body r M W u S base
    (seedPort ▸ sources 6 (by decide)) free
  let C : Stacks _ prime := {S with R := Function.update S.R (r 2) (binSyms K.size K)}
  have kept (j : Fin 93) : C.R (slots j) = S.R (slots j) := by
    exact Function.update_of_ne ((widthPort ▸ retainedPort_private owner 0 j).symm) _ _
  obtain ⟨y,D,loadRun,same,headers,off⟩ := copy vals v C (by
    intro j
    by_cases zero : j = 0
    · subst j
      simp [C,widthPort,vals,K]
    have distinct : retainedPort T j ≠ r 2 := by
      rw [widthPort]
      intro eq
      apply zero
      apply Fin.ext
      have h := congrArg Fin.val eq
      simp [retainedPort,T] at h
      omega
    rw [show C.R (retainedPort T j) = _ from Function.update_of_ne distinct _ _]
    have h := ordinaryRotationOffsets w
    dsimp only [vals,g,idRow]
    rw [h.1,h.2]
    exact sources j zero)
    (fun j => ⟨(fresh _ ((by decide : ∀ i, headerPorts i ≠ 0) j)).1,
      (kept _).trans (fresh _ ((by decide : ∀ i, headerPorts i ≠ 0) j)).2⟩)
    ((kept _).trans (fresh 13 (by decide)).2) ((kept _).trans (fresh 14 (by decide)).2)
  have untouched (j : Fin 93) (h : ∀ i, headerPorts i ≠ j) := off (slots j) (fun i => slots.injective.ne (h i))
  have empty (j : Fin 93) (h : j ≠ 0 ∧ ∀ i, headerPorts i ≠ j) : D.L (slots j) = [] ∧ D.R (slots j) = [] :=
    ⟨(untouched j h.2).1.trans (fresh j h.1).1,(untouched j h.2).2.trans ((kept j).trans (fresh j h.1).2)⟩
  have blankAt (j : Fin 93) (h : j ≠ 0 ∧ ∀ i, headerPorts i ≠ j) (z : ℤ) :
      readAt blank (D.L (slots j)) (D.R (slots j)) z = blank := by
    rw [(empty j h).1,(empty j h).2,readAt_nil_left,wordTape_nil]
  have ready : ScannerReady stage size back words (embStk old D) := by
    apply initial.of_owner_change
    intro j _
    have h := off _ (fun i => (aroundScanner_private owner _ ((by decide : ∀ i, headerPorts i ≠ 1) i) j).symm)
    refine ⟨h.1,h.2.trans (Function.update_of_ne ?_ _ _)⟩
    rw [widthPort]
    intro eq
    have e := congrArg Fin.val eq
    simp [retainedPort] at e
    omega
  have srcLive := untouched 0 (by decide)
  have trans (j : Fin 8) := empty _ ((by decide : ∀ j, inputTranspose j ≠ 0 ∧ ∀ i, headerPorts i ≠ inputTranspose j) j)
  have ret (j : Fin 8) := empty _ ((by decide : ∀ j, outputTranspose j ≠ 0 ∧ ∀ i, headerPorts i ≠ outputTranspose j) j)
  obtain ⟨z,F,t,staged,run,time,user,word,cells⟩ := execute x i y D ready headers
    (fun b j hj => empty _ ((by decide +kernel : ∀ b (j : Fin 12), 2 ≤ j.val → paddingBanks b j ≠ 0 ∧ ∀ i, headerPorts i ≠ paddingBanks b j) b j hj))
    (by change WordAtZero _ (D.L (slots 0)) (D.R (slots 0)); rwa [srcLive.1,srcLive.2,kept])
    (blankAt _ (by decide : inputCrop 1 ≠ 0 ∧ ∀ i, headerPorts i ≠ inputCrop 1))
    (trans 0).1 (trans 1).1 (fun j => (trans j).2)
    (blankAt _ (by decide : inputPad 1 ≠ 0 ∧ ∀ i, headerPorts i ≠ inputPad 1))
    (fun j _ _ => empty _ ((by decide : ∀ j, inputRotation j ≠ 0 ∧ ∀ i, headerPorts i ≠ inputRotation j) j))
    (blankAt 1 (by decide))
    (fun j _ _ => empty _ ((by decide : ∀ j, outputRotation j ≠ 0 ∧ ∀ i, headerPorts i ≠ outputRotation j) j))
    (blankAt _ (by decide : outputRotation 11 ≠ 0 ∧ ∀ i, headerPorts i ≠ outputRotation 11))
    (blankAt _ (by decide : outputCrop 1 ≠ 0 ∧ ∀ i, headerPorts i ≠ outputCrop 1))
    (fun j => (ret j).2) (ret 1).1 (ret 6).1
  refine ⟨z,F,_,staged,Exec.seq widthRun (Exec.seq loadRun run),?_,user.trans (same.trans vu),word,cells⟩
  let V := B*(N*K)
  have charge := headerCharge (w := w) hb hw
  have fee : ((((List.finRange 7).map (fun i => 6*(vals i).size+6)).sum+2 : ℕ) : ℝ) ≤ 42*(V : ℝ)+44 := by exact_mod_cast charge
  change (t : ℝ) ≤ _ + 46444*(V : ℝ)+1182 at time
  change (((s + (_ + t) : ℕ) : ℝ)) ≤ _ + 46486*(V : ℝ)+1226 + _
  rw [Nat.cast_add,Nat.cast_add]
  have widthCost : (s : ℝ) ≤ (dimensionTime M.size tail.size 16 + (4*(16*M.size+tail.size)+6) : ℕ) := by exact_mod_cast hs
  linarith

private def clockRegisters {T : ℕ} (clock : Fin T) : Fin 7 ↪ Fin (T+99) where
  toFun := Fin.cases (clock.castAdd 99) (fun i : Fin 6 =>
    ((![1,2,94,3,93,4] : Fin 6 → Fin 99) i).natAdd T)
  inj' := by
    intro i j
    cases i using Fin.cases <;> cases j using Fin.cases <;> simp
    all_goals intro h
    all_goals first
      | exact (by decide : Function.Injective (![1,2,94,3,93,4] : Fin 6 → Fin 99)) h
      | have hc := clock.isLt; have e := congrArg Fin.val h; simp at e; omega

private def forwardRegisters {T : ℕ} (clock : Fin T) : Fin 7 ↪ Fin (T+99) :=
  (⟨![1,2,3,4,5,6,0],by decide⟩ : Fin 7 ↪ Fin 7).trans (clockRegisters clock)

theorem ScheduledReturn.roundTrip [M8.Machine.Net] {V size back Q w B W : ℕ} {U : Type}
    {stage : SharedBankStage.Stage _ 1 prime (phaseOwners (N := V))} {words : Fin size → List (Fin (prime+4))}
    {interval : ℕ × ℕ} {parent : Fin 64 → ZMod (prime^(w+1))}
    {c : Certificates.PR589.Nine.PortCertificate} {checked : c.Checked}
    {body : Unit → Pr Unit ((size+stage.tapes+back)+99) Q prime U} {scan rate}
    (scheduled : ScheduledReturn (w := w) (B := B) (W := W) interval parent c checked
      (((stage.slots 0).natAdd size).castAdd back) (ScannerReady stage size back words) body scan rate)
    (modulus : Fin size) (modulusWord : words modulus = binSyms (prime^(w+1)).size (prime^(w+1)))
    (precision : Fin size) (precisionWord : (words precision).length = w+1)
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
    let offset := diagonalPrefix (M^65) 64
    ∀ (x : Fin 142081 → Fin (A*(B*tail)) → ZMod 2) i u S,
      ScannerReady stage size back words (embStk old S) →
      S.R (retainedPort T 0) = [] →
      S.R (retainedPort T 2) = [] → S.R (retainedPort T 4) = [] →
      (∀ j : Fin 7, j ≠ 0 → j ≠ 2 → j ≠ 4 → let n := (![K,N,offset,B,N-offset,A*B,tail] : Fin 7 → ℕ) j
        S.R (retainedPort T j) = binSyms n.size n) →
      WordAtZero (singleLabelBank (firstRowLabel (w+1)) x i) (S.L (slots 0)) (S.R (slots 0)) →
      (∀ j, j ≠ 0 → S.L (slots j) = [] ∧ S.R (slots j) = []) →
      ∃ v F t, ∃ staged : Fin (M^16*(B*(M^112*W))) → ZMod 2, Exec body code (mk u S) t (mk v F) ∧
        (t : ℝ) ≤ (packedChartRate (0 : Fin 1) c checked false layout.width +
          packedChartRate (0 : Fin 1) c checked true layout.width + (366+16*64*64+19*64+344) +
          rate*((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau + 64*(8*64+21+28+(prime.size : ℝ)))*
          volume prime (role layout 142080) + 13 + 46486*(B*(N*K) : ℕ)+1226 + (dimensionTime M.size tail.size 16 + (4*(16*M.size+tail.size)+6) : ℕ) + (16*N.size+20 : ℕ) +
            (1+64*(4*(w+1)+5)+(4*N.size+4)+64*(65*(w+1))*(7*N.size+prime+17)+6 : ℕ) ∧ v.user = u.user ∧
        WordAtZero (singleLabelBank (firstRowLabel (w+1)) (fun _ => staged) 0) (F.L (slots 0)) (F.R (slots 0)) ∧
      let proj := IntegerMultBounds.Swap.Modular.reduce M ((c.span interval.1 interval.2).submatrix stageAxis.symm stageAxis.symm)
      let frame := Matrix.fromBlocks (Matrix.diagonal parent) 0 0 (M8.ReversedExchange.rev 64)
      let addr := fun b y (k : Fin W) => stagedOwnerIndex b (FlatCoordinateLayout.index
        ((frame.mulVec y) ∘ (finSumFinEquiv : (Fin 64 ⊕ Fin 64) ≃ Fin 128).symm) k)
      ∀ b y k, staged (addr b ((Matrix.fromBlocks (1-proj) proj proj (1-proj)).mulVec y) k) = x i (addr b y k) := by
  let T := size+stage.tapes+back
  let owner := ((stage.slots 0).natAdd size).castAdd back
  let regs := (⟨![93,94,96,1,2,3,4],by decide⟩ : Fin 7 ↪ Fin 99).trans (Fin.natAddEmb T)
  obtain ⟨prepare,subtract⟩ := rotationHeaders_exec body regs
  obtain ⟨code,run⟩ := scheduled.roundTripWithOffsets modulus modulusWord hb hw fits
  let bank := forwardRegisters ((precision.castAdd stage.tapes).castAdd back)
  obtain ⟨generate,write⟩ := generateForwardOffset_exec body bank
  refine ⟨generate.seq (prepare.seq code),?_⟩
  intro _ _ slots old layout M A tail N K offset x i u S ready width shift backEmpty sources live fresh
  have forward : regs 1 = retainedPort T 2 := rfl
  have reverse : regs 2 = retainedPort T 4 := rfl
  have fitsOffset : offset ≤ N := by
    dsimp only [offset,M]
    rw [← (ordinaryRotationOffsets w).1]
    have lt := (ordinaryIdentityRow (w+1)).isLt
    apply lt.le.trans
    dsimp [N,M]
    rw [← pow_mul]
    apply Nat.pow_le_pow_right Shared50ModularControl.prime_prime.pos
    omega
  have row := sources 1 (by decide) (by decide) (by decide)
  have positive : 0 < N := pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _
  have sizePos : 0 < N.size := by
    by_contra! h
    have bound := Nat.lt_size_self N
    rw [show N.size = 0 by omega] at bound
    simp at bound
    omega
  obtain ⟨y,m,yu,hm,generated⟩ := write w N.size sizePos u S
    ((congrArg List.length (ready.2.1 precision).2).trans precisionWord)
    (by change (S.R (retainedPort T 1)).length = N.size; rw [row,length_binSyms]; rfl) (by
      intro j a b
      fin_cases j <;> first | exact False.elim (by revert a b; decide) | exact shift
                            | exact (fresh 2 (by decide)).2 | exact (fresh 3 (by decide)).2
                            | exact (fresh 4 (by decide)).2 | exact (fresh 5 (by decide)).2)
  let C : Stacks _ prime := {S with R := Function.update S.R (regs 1) (binSyms N.size offset)}
  have genKeep (j : Fin 7) (h : j ≠ 1) : C.R (regs j) = S.R (regs j) := Function.update_of_ne (regs.injective.ne h) _ _
  obtain ⟨v,vu,prepared⟩ := subtract N offset fitsOffset y C ((genKeep 0 (by decide)).trans row) (Function.update_self ..) (by
    intro j lo hi
    rw [genKeep j (by omega)]
    fin_cases j <;> first | exact False.elim (by revert lo hi; decide) | exact backEmpty
                          | exact (fresh 2 (by decide)).2 | exact (fresh 3 (by decide)).2 | exact (fresh 4 (by decide)).2)
  let D : Stacks _ prime := {C with R := Function.update (Function.update C.R (regs 2)
    (binSyms (N-offset).size (N-offset))) (regs 1) (binSyms offset.size offset)}
  have off (j) (hf : j ≠ retainedPort T 2) (hb : j ≠ retainedPort T 4) : D.R j = S.R j := by
    simp [D,C,forward,reverse,Function.update_of_ne,hf,hb]
  have retained : Function.Injective (retainedPort T) := by
    intro j k h
    apply Fin.ext
    simpa [retainedPort] using congrArg Fin.val h
  have keep (j) := off (slots j) (retainedPort_private owner 2 j).symm (retainedPort_private owner 4 j).symm
  have entry : embStk old D = embStk old S := by
    unfold embStk
    congr 1
    funext j
    apply off <;> intro eq <;> have e := congrArg Fin.val eq <;> simp [old,retainedPort,T] at e <;> omega
  obtain ⟨z,F,t,staged,execute,time,user,word,cells⟩ := run x i v D (entry ▸ ready)
    ((off _ (retained.ne (by decide)) (retained.ne (by decide))).trans width) (by
      intro j nz
      by_cases f : j = 2
      · subst j; change D.R (regs 1) = binSyms offset.size offset; simp [D]
      by_cases b : j = 4
      · subst j; change D.R (regs 2) = binSyms (N-offset).size (N-offset); simp [D,regs.injective.eq_iff]
      exact (off _ (retained.ne f) (retained.ne b)).trans (sources j nz f b))
    (by change WordAtZero _ _ (D.R (slots 0)); rwa [keep])
    (fun j hj => ⟨(fresh j hj).1,(keep j).trans (fresh j hj).2⟩)
  refine ⟨z,F,_,staged,Exec.seq generated (Exec.seq prepared execute),?_,user.trans (vu.trans yu),word,cells⟩
  rw [Nat.cast_add,Nat.cast_add]
  have cost := Nat.cast_le (α := ℝ).mpr hm
  linarith

end OrdinaryHandoff
end IntegerMultBounds.MathlibTM2.M6.BitNode
