module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackScanState
public import IntegerMultBounds.MathlibTM2.Cover.FallbackRecordMasks
public import IntegerMultBounds.MathlibTM2.Cover.FallbackRecordCleanup
public import IntegerMultBounds.MathlibTM2.Cover.FallbackLeafFrame
import IntegerMultBounds.MathlibTM2.Cover.FallbackArchivedResidual

/-! Identify the generated live and padding words with the signed pass's matrix archive. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
noncomputable section
open IntegerMultBounds.Networks.Shared50ModularControl (prime prime_prime)
open IntegerMultBounds.Swap.Modular (reduce Admissible)
variable {r d w W : ℕ}
local notation "M" => prime^(w+1)
local instance : NeZero M := ⟨(pow_pos prime_prime.pos _).ne'⟩

def ScanData.physical (a : ScanData r d w W) (e : (Fin r ⊕ Fin r) ≃ Fin (d+1))
    (P : Matrix (Fin r) (Fin r) ℚ) (α α' : Fin r → ZMod M) : ScanData r d w W :=
  let φ := LabelRing.res prime (w+1) (by omega)
  {a with
    matrix := fun j => if LabelStock.live r (w+1) 1 j then
      projectorResidual e (reduce M P) α α' (physicalLabel r (w+1) j) else 1
    table := projectorResidual e (reduce prime P) (φ ∘ α) (φ ∘ α')
    matrixTail := []}

theorem ScanData.physical_archive (a : ScanData r d w W) (e : (Fin r ⊕ Fin r) ≃ Fin (d+1))
    (P : Matrix (Fin r) (Fin r) ℚ) (α α' : Fin r → ZMod M) :
    (a.physical e P α α').matrices 0 = (List.range a.records).flatMap fun j =>
      if LabelStock.live r (w+1) 1 j then matrixWords prime a.H
        (projectorResidual e (reduce M P) α α' (physicalLabel r (w+1) j))
      else matrixWords prime a.H (1 : Matrix (Fin (d+1)) (Fin (d+1)) (ZMod M)) := by
  simp only [ScanData.matrices,ScanData.physical,List.drop_zero,List.append_nil]
  congr 1
  funext j
  split <;> rfl

theorem ScanData.physical_live (a : ScanData r d w W) (e : (Fin r ⊕ Fin r) ≃ Fin (d+1))
    (P : Matrix (Fin r) (Fin r) ℚ) (hp : P*P = P) (adm : Admissible prime P)
    (α α' : Fin r → ZMod M) (ha : ∀ i, α i * α' i = 1) (j : ℕ)
    (live : LabelStock.live r (w+1) 1 j = true) :
    let data := a.physical e P α α'
    ((data.matrix j).det = 1 ∨ (data.matrix j).det = -1) ∧
      (LabelRing.res prime (w+1) (by omega)).mapMatrix (data.matrix j) =
        data.table (LabelStock.residue r (w+1) 1 j) := by
  simpa only [ScanData.physical,live,ite_true] using
    physicalProjector_spec (by omega : 0 < w+1) j live e P hp adm α α' ha

local instance (b : ℕ) : NeZero (IntegerMultBounds.Machine.ActualAffineScaling.modulus b) :=
  ⟨(IntegerMultBounds.Machine.ActualAffineScaling.modulus_pos b).ne'⟩

/-- Counter, payload, saved counter, temporary tape, schedule, and return buffer
in the generated directory's caller bank. -/
def directoryAnchorPorts : Fin 6 ↪ Fin 66 := ⟨![58,24,59,60,54,61],by decide⟩

def directoryAnchorBank (d K : ℕ) (room : Record.size d ≤ K) :
    Fin (Record.size d+6) ↪ Fin (66+K) :=
  (((finSumFinEquiv.symm.toEmbedding.trans (Equiv.sumComm _ _).toEmbedding).trans
    (directoryAnchorPorts.sumMap (Fin.castLEEmb room))).trans finSumFinEquiv.toEmbedding)

theorem directoryAnchorBank_port {K : ℕ} (room : Record.size d ≤ K) (i : Fin 6) :
    directoryAnchorBank d K room (Fin.natAdd (Record.size d) i) = (directoryAnchorPorts i).castAdd K := by
  simp [directoryAnchorBank]

theorem directoryAnchorBank_off {K : ℕ} (room : Record.size d ≤ K) (j : Fin 58)
    (payload : j ≠ 24) (schedule : j ≠ 54) (k : Fin (Record.size d+6)) :
    directoryAnchorBank d K room k ≠ (j.castAdd 8).castAdd K := by
  induction k using Fin.addCases with
  | left k =>
    intro eq
    have val := congrArg Fin.val eq
    simp [directoryAnchorBank] at val
    omega
  | right i =>
    rw [directoryAnchorBank_port]
    apply (Fin.castAddEmb K).injective.ne
    fin_cases i <;> intro eq <;> have val := congrArg Fin.val eq <;>
      simp [directoryAnchorPorts] at val <;> apply_rules [payload,schedule,Fin.ext] <;> omega

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host Record in
/-- Read the sign from an exceptional schedule, apply the anchor, and return
the signed payload to the front of the input queue in forward order. -/
theorem scheduledAnchor_exec {K Q : ℕ} {P U : Type} (room : size d ≤ K)
    (capacity : (anchorProgram d true).1+(anchorProgram d false).1+1 ≤ Q)
    (C : Matrix (Fin (d+1)) (Fin (d+1)) (ZMod prime)) (positive : 0 < W)
    (a : Record.Array d 1 (w+1) W) (word : Fin (M^(d+1)*W) → ZMod 2)
    (encoded : scalarArray a = SparseRoleCircuit.encode ∘ word)
    (body : P → Pr P (66+K) Q prime U) (u : HS (66+K) Q prime U) (whole : Stacks (66+K) prime)
    (tail rest : List (Fin (prime+4))) :
    let ports := Function.Embedding.refl (Fin 6)
    let host := directoryAnchorBank d K room
    let S := embStk host whole
    Record.Ready d 1 (w+1) W S →
    (S.R (port d ports 0)).length = M^(d+1)*W →
    S.R (port d ports 1) = payloadWord a ++ tail →
    (∀ i ∈ ([2,3,5] : List (Fin 6)), S.R (port d ports i) = []) →
    S.R (port d ports 4) = residualSchedule C ++ rest →
    let pos : 0 < (anchorProgram d true).1+(anchorProgram d false).1+1 := Nat.zero_lt_succ _
    let rows := classPivots C
    let neg := negativeAnchor rows C
    ∃ a' : Record.Array d 1 (w+1) W, ∃ next z F n, let D := embStk host F; z.user = u.user ∧
      n ≤ 1 + (cost d 6 1 (w+1) W neg + (2*(M^(d+1)*W)+2)) ∧
      Exec body (statePlacedNormalized host capacity pos Empty.elim ((program d ports).seq (moveR (port d ports 5) (port d ports 1) id)))
        (mk u whole) n (mk z F) ∧
      (∀ j, (∀ i, host i ≠ j) → F.L j = whole.L j ∧ F.R j = whole.R j) ∧
      D.L (port d ports 1) = S.L (port d ports 1) ∧
      D.R (port d ports 1) = payloadWord (SparseRoleCircuit.encode ∘ next) ++ tail ∧
      D.R (port d ports 4) = scheduleCode rows ++ (orderedScheduleCode (List.finRange (d+1)).reverse rows ++ rest) ∧
      D.R (port d ports 5) = [] ∧ Record.Ready d 1 (w+1) W D ∧
      (∀ i : Fin 6, i ≠ ports 1 → i ≠ ports 4 → i ≠ ports 5 →
        D.R (Fin.natAdd (size d) i) = S.R (Fin.natAdd (size d) i)) ∧ scalarArray a' = SparseRoleCircuit.encode ∘ next ∧
      ∀ x k, next (FlatCoordinateLayout.index (signedAddress neg x) k) = word (FlatCoordinateLayout.index x k) := by
  intro ports host S ready count input free schedule pos rows neg
  let localUser := stateLiftDown pos (embDn host u)
  let localBody : Empty → Pr Empty (size d+6) ((anchorProgram d true).1+(anchorProgram d false).1+1) prime U := Empty.elim
  let pivots := scheduleCode (A := prime) rows ++ (orderedScheduleCode (List.finRange (d+1)).reverse rows ++ rest)
  have sign : S.R (port d ports 4) = bitSymbol neg :: pivots := by
    simpa only [residualSchedule,List.cons_append,List.append_assoc,neg,rows,pivots] using schedule
  obtain ⟨out,y,F,t,run,neutral,user,_,_,left,price,frame,action⟩ := Record.runs ports neg (by decide : 0 < 1)
    (by omega : 0 < w+1) positive a localBody localUser S tail pivots ready (by simpa [ActualAffineScaling.modulus] using count)
    input (free 2 (by simp)) (free 3 (by simp)) sign
  have atPort (i : Fin 6) := frame (ports i)
  have acc : F.R (port d ports 5) = (payloadWord out).reverse := by
    simpa [port,free 5 (by simp)] using atPort 5
  have src : F.R (port d ports 1) = tail := by simpa [port,ports.injective.eq_iff] using atPort 1
  have steps : (F.R (port d ports 5)).length = M^(d+1)*W := by simp [acc,payloadWord,ActualAffineScaling.modulus]
  have distinct (i j : Fin 6) (h : i ≠ j) : port d ports i ≠ port d ports j :=
    (Fin.natAdd_injective _ _).ne (ports.injective.ne h)
  obtain ⟨z,hz,rewind⟩ := moveR_exec localBody (port d ports 5) (port d ports 1) (distinct 5 1 (by decide)) id y F
  rw [steps] at rewind
  obtain ⟨next,output,perm⟩ := signedPayload neg a out action word encoded
  obtain ⟨finish,_,hUser,placed⟩ := statePlaced_exec_normalized host host.injective capacity pos Empty.elim
    (body' := body) (fun e => nomatch e) u whole (Exec.seq run rewind)
  let endBank := {F with R := movedR F.R (port d ports 5) (port d ports 1) id (F.R (port d ports 5))}
  let result := embOvr host endBank.get whole
  have bank : embStk host result = endBank := embStk_ovr host.injective _ _
  refine ⟨out,next,finish,result,_,hUser.trans (hz.trans user),Nat.add_le_add_left (Nat.add_le_add_right price _) 1,placed,
    fun j off => embOvr_off endBank.get whole off,?_⟩
  rw [bank]
  dsimp only [endBank]
  refine ⟨left,?_,?_,?_,?_,?_,output,perm⟩
  · rw [← output,Record.payloadWord_scalarArray]
    simp [movedR,acc,src]
  · simpa [movedR,distinct 4 1 (by decide),distinct 4 5 (by decide),port,ports.injective.eq_iff] using atPort 4
  · simp [movedR,distinct 5 1 (by decide)]
  · intro i j
    have off (k : Fin 6) : Fin.castAdd 6 i ≠ port d ports k := by
      intro eq; have h := congrArg Fin.val eq
      change i.val = size d + (ports k).val at h
      exact (Nat.not_le_of_lt i.isLt) (h ▸ Nat.le_add_right _ _)
    simpa only [movedR,Function.update_of_ne (off 1),Function.update_of_ne (off 5)] using neutral i j
  · intro i src sign acc
    simpa [movedR,port,src,sign,acc] using frame i

/-- Place the residual workspace after the anchor and connect its pivot reader
to the schedule tape that the anchor just advanced. -/
def directoryResidualBank {K n : ℕ} (d : ℕ) (room : Record.size d+n ≤ K) (pivot : Fin n) :
    Fin n ↪ Fin (66+K) :=
  let privateBank := ((Fin.natAddEmb (Record.size d)).trans (Fin.castLEEmb room)).trans (Fin.natAddEmb 66)
  privateBank.trans (Equiv.swap (privateBank pivot) ((54 : Fin 66).castAdd K)).toEmbedding

theorem directoryResidualBank_pivot {K n : ℕ} (room : Record.size d+n ≤ K) (pivot : Fin n) :
    directoryResidualBank d room pivot pivot = (54 : Fin 66).castAdd K := Equiv.swap_apply_left ..

theorem directoryResidualBank_private {K n : ℕ} (room : Record.size d+n ≤ K) (pivot i : Fin n)
    (off : i ≠ pivot) :
    (directoryResidualBank d room pivot i).val = 66+(Record.size d+i.val) := by
  let bank := ((Fin.natAddEmb (Record.size d) (m := n)).trans (Fin.castLEEmb room)).trans (Fin.natAddEmb 66)
  have privatePort : bank i ≠ (54 : Fin 66).castAdd K := by
    intro eq; have h := congrArg Fin.val eq; change 66+(Record.size d+i.val) = 54 at h; omega
  change (Equiv.swap (bank pivot) ((54 : Fin 66).castAdd K) (bank i)).val = _
  rw [Equiv.swap_apply_of_ne_of_ne (bank.injective.ne off) privatePort]
  rfl

theorem directoryResidualBank_off {K n : ℕ} (room : Record.size d+n ≤ K) (pivot i : Fin n)
    (j : Fin 66) (off : j ≠ 54) : directoryResidualBank d room pivot i ≠ j.castAdd K := by
  by_cases same : i = pivot
  · subst i; rw [directoryResidualBank_pivot]; exact (Fin.castAddEmb K).injective.ne off.symm
  · intro eq
    have val := congrArg Fin.val eq
    rw [directoryResidualBank_private room pivot i same] at val
    change 66+(Record.size d+i.val) = j.val at val
    omega

theorem directoryAnchor_residual_disjoint {K n : ℕ} (room : Record.size d+n ≤ K) (pivot i : Fin n)
    (off : i ≠ pivot) (k : Fin (Record.size d+6)) :
    directoryAnchorBank d K ((Nat.le_add_right ..).trans room) k ≠ directoryResidualBank d room pivot i := by
  intro eq
  have val := congrArg Fin.val eq
  rw [directoryResidualBank_private room pivot i off] at val
  induction k using Fin.addCases with
  | left k =>
    simp [directoryAnchorBank] at val
    omega
  | right k =>
    rw [directoryAnchorBank_port] at val
    change (directoryAnchorPorts k).val = 66+(Record.size d+i.val) at val
    have bound := (directoryAnchorPorts k).isLt
    omega

def residualHeaderPorts : Fin 5 ↪ Fin 35 := ⟨![2,27,28,32,33],by decide⟩

def residualCallerHeaders : Fin 5 ↪ Fin 66 := ⟨![2,53,28,44,45],by decide⟩

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host in
/-- Install the modulus, trailing width, both units and reciprocal clock from
the directory caller. The matrix archive and the two payload tapes are framed. -/
theorem directoryResidualHeaders_exec [M8.Machine.Net] {K Q : ℕ} {P U : Type} (d : ℕ)
    (body : P → Pr P (66+K) Q prime U) (u : HS (66+K) Q prime U) (S : Stacks (66+K) prime)
    (H J w W : ℕ) (G : Matrix (Fin (d+1)) (Fin (d+1)) (ZMod (prime^(w+1))))
    (tail : List (Fin (prime+4))) (word : Fin ((prime^(w+1))^(d+1)*W) → ZMod 2) :
    let N := rowSwapBlock.tapes+35
    ∀ (room : Record.size d+(N+2) ≤ K),
    let caller := Fin.castAddEmb (n := 66) K
    let src := residualCallerHeaders.trans caller
    let ports := directoryResidualBank d room (Fin.last N).castSucc
    let bank := (columnBank.trans (archivePorts 0)).trans ports
    let dst := residualHeaderPorts.trans bank
    S.R (src 0) = binSyms H (prime^(w+1)) → S.R (src 1) = binSyms J W →
    S.R (src 2) = binSyms 1 1 → S.R (src 3) = binSyms H (1 : ZMod (prime^(w+1))).val →
    (S.R (src 4)).length = w → S.R (caller 64) = [] → S.R (caller 65) = [] →
    (∀ i : Fin 35, i ≠ 34 → S.L (bank i) = [] ∧ S.R (bank i) = []) →
    S.R (bank 34) = matrixWords prime H G ++ tail →
    ∃ z F, z.user = u.user ∧ Exec body (Record.copyLeafHeaders src dst (caller 64) (caller 65) (List.finRange 5))
      (mk u S) (6*(2*H+J+w)+37) (mk z F) ∧
      ShearReady bank H J G tail (fun _ : ZMod 2 => blank) (fun _ => blank) (fun _ => blank) 0 0 word F ∧
      (∀ z, readAt blank (F.L (bank 24)) (F.R (bank 24)) z = blank) ∧ F.L = S.L ∧ ∀ k, (∀ i, dst i ≠ k) → F.R k = S.R k := by
  intro N room caller src ports bank dst modulus width one padded clock tmp aux free archive
  have off (i : Fin 5) (k : Fin 66) (h : k ≠ 54) : dst i ≠ caller k :=
    directoryResidualBank_off room _ _ k h
  have srcOff : ∀ i : Fin 5, residualCallerHeaders i ≠ 54 ∧ residualCallerHeaders i ≠ 64 ∧
      residualCallerHeaders i ≠ 65 := by decide
  have apart (i j : Fin 5) : src i ≠ dst j := (off j _ (srcOff i).1).symm
  have separate (i : Fin 5) : [src i,dst i,caller 64,caller 65].Nodup := by
    simp [List.nodup_cons,apart,show src i ≠ caller 64 from caller.injective.ne (srcOff i).2.1,
      show src i ≠ caller 65 from caller.injective.ne (srcOff i).2.2,off i 64 (by decide),off i 65 (by decide),
      caller.injective.ne (by decide : (64 : Fin 66) ≠ 65)]
  obtain ⟨z,F,user,run,left,loaded,frame⟩ := Record.copyLeafHeaders_exec body src dst (caller 64) (caller 65)
    apart separate _ (List.nodup_finRange 5) u S tmp aux (fun i _ => (free (residualHeaderPorts i) ((by decide : ∀ j, residualHeaderPorts j ≠ 34) i)).2)
  have get (i) := loaded i (List.mem_finRange i)
  have bill : ((List.finRange 5).map fun i => 6*(S.R (src i)).length+6).sum+1 = 6*(2*H+J+w)+37 := by
    rw [show List.finRange 5 = [0,1,2,3,4] from rfl]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,modulus,width,one,padded,clock,length_binSyms]
    omega
  have unchanged (k : Fin 35) (hk : ∀ i, residualHeaderPorts i ≠ k) :
      F.R (bank k) = S.R (bank k) := frame _ (fun i _ => bank.injective.ne (hk i))
  have empty (k : Fin 35) (hk : k ≠ 34) (hc : ∀ i, residualHeaderPorts i ≠ k) :
      F.L (bank k) = [] ∧ F.R (bank k) = [] :=
    ⟨(congrFun left _).trans (free k hk).1,(unchanged k hc).trans (free k hk).2⟩
  have blankAt (k : Fin 35) (hk : k ≠ 34) (hc : ∀ i, residualHeaderPorts i ≠ k) (z : ℤ) :
      readAt blank (F.L (bank k)) (F.R (bank k)) z = blank := by
    rw [(empty k hk hc).1,(empty k hk hc).2,readAt_nil_left,wordTape_nil]
  have payload := blankAt 24 (by decide) (by decide)
  refine ⟨z,F,user,bill ▸ run,⟨(get 0).trans modulus,(get 1).trans width,(get 2).trans one,(get 3).trans padded,
    (congrArg List.length (get 4)).trans clock,(unchanged 34 (by decide)).trans archive,?_,?_,?_⟩,
    payload,left,fun k h => frame k (fun i _ => h i)⟩
  · intro i hi
    exact empty i ((by decide : ∀ i ∈ shearWork, i ≠ 34) i hi)
      ((by decide : ∀ i ∈ shearWork, ∀ j, residualHeaderPorts j ≠ i) i hi)
  · intro z
    rw [sub_zero,payload]
    simp only [Function.comp_def,List.ofFn_const,Record.putWord_blanks]
    rfl
  · intro z
    rw [sub_zero,blankAt 25 (by decide) (by decide)]
    rfl

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host in
/-- Execute a single live projector residual from the pivot codes of its residue
class. Only this record is consumed, so skipped labels need no pivot codes. -/
theorem physicalResidualRecord_exec [M8.Machine.Net] {K : ℕ} {P U : Type}
    (e : (Fin r ⊕ Fin r) ≃ Fin (d+1)) (proj : Matrix (Fin r) (Fin r) ℚ)
    (idem : proj*proj = proj) (adm : Admissible prime proj)
    (α inv : Fin r → ZMod M) (reciprocal : ∀ i, α i * inv i = 1)
    (j : ℕ) (live : LabelStock.live r (w+1) 1 j = true)
    (H J : ℕ) (hm : M < 2^H) (hw : W < 2^J) (positive : 0 < W) :
    let N := rowSwapBlock.tapes+35
    let G := projectorResidual e (reduce M proj) α inv (physicalLabel r (w+1) j)
    let φ := LabelRing.res prime (w+1) (by omega)
    let C := projectorResidual e (reduce prime proj) (φ ∘ α) (φ ∘ inv) (LabelStock.residue r (w+1) 1 j)
    let rows := classPivots C
    ∀ (room : Record.size d+(N+2) ≤ K),
      let ports := directoryResidualBank d room (Fin.last N).castSucc
      let count := (58 : Fin 66).castAdd K
      let src := (24 : Fin 66).castAdd K
      let saved := (59 : Fin 66).castAdd K
      let tmp := (60 : Fin 66).castAdd K
      ∀ (body : P → Pr P (66+K) columnCapacity prime U) (u : HS (66+K) columnCapacity prime U) (S : Stacks (66+K) prime)
        (tail rest queueTail : List (Fin (prime+4))) (dest : ℤ → Fin 4) (q : ℤ)
        (original word : Fin (M^(d+1)*W) → ZMod 2),
      (∀ z, q ≤ z → z < q+(M^(d+1)*W : ℕ) → dest z = blank) →
      let bank := columnBank.trans (archivePorts 0)
      let dst := ports (bank 24)
      let clean := fun (D : Stacks (66+K) prime) => ∀ i : Fin N, 35 ≤ i.val →
        D.L (ports (columnPorts i).castSucc) = [] ∧ D.R (ports (columnPorts i).castSucc) = []
      ShearReady bank H J G tail (fun _ : ZMod 2 => blank) (fun _ => blank) dest 0 q original (embStk ports S) →
      clean S → (∀ x j, word (FlatCoordinateLayout.index (Record.signedAddress (negativeAnchor rows C) x) j) = original (FlatCoordinateLayout.index x j)) →
      S.R src = payloadWord (SparseRoleCircuit.encode ∘ word) ++ queueTail → (S.R count).length = M^(d+1)*W →
      (∀ z, readAt blank (S.L dst) (S.R dst) z = blank) → S.R saved = [] → S.R tmp = [] →
      S.R (ports (Fin.last N).castSucc) = scheduleCode rows ++ orderedScheduleCode (List.finRange (d+1)).reverse rows ++ rest →
      ∃ z F n, z.user = u.user ∧ n ≤ 6*(M^(d+1)*W)+6+(1+signedResidualTime U rows w W H J) ∧
        Exec body (queuedResidual ports count src saved tmp d) (mk u S) n (mk z F) ∧
        ColumnReady bank H J G tail SparseRoleCircuit.encode (fun _ => blank) dest 0 q original (fun x => G.mulVec x) (embStk ports F) ∧
        clean F ∧ F.R (ports (Fin.last N).castSucc) = rest ∧ F.R src = queueTail ∧
        F.R (ports (archivePorts 1 (columnBank 34))) = S.R (ports (archivePorts 1 (columnBank 34))) ∧
        F.L src = S.L src ∧
        ∀ j, j ≠ src → (∀ i, ports i ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  intro N G φ C rows room ports count src saved tmp body u S tail rest queueTail dest q
    original word empty bank dst clean layout free placed queue width blankDst savedFree tmpFree code
  have off (i : Fin (N+2)) (k : Fin 66) (h : k ≠ 54) : ports i ≠ k.castAdd K :=
    directoryResidualBank_off room _ i k h
  have outside (i) : ports i ≠ src := off i 24 (by decide)
  have separate : [count,src,ports (archivePorts 0 (columnBank 24)),saved,tmp].Nodup := by
    simp [count,src,saved,tmp,List.nodup_cons,off _ 58 (by decide),off _ 24 (by decide),
      off _ 59 (by decide),off _ 60 (by decide),Ne.symm (off _ 58 (by decide)),Ne.symm (off _ 24 (by decide))]
  let : Fact prime.Prime := ⟨prime_prime⟩
  obtain ⟨det,lift⟩ := physicalProjector_spec (by omega : 0 < w+1) j live e proj idem adm α inv reciprocal
  change G.det = 1 ∨ G.det = -1 at det
  change φ.mapMatrix G = C at lift
  have unit : IsUnit C.det := by
    rw [← lift,← RingHom.map_det]
    rcases det with h | h <;> simp [h]
  have reduced : Itinerary.Valid rows (φ.mapMatrix G) (d+1) := lift.symm ▸ classPivots_valid C unit
  have valid := (Itinerary.valid_map_iff φ (fun a ha =>
    (LabelRing.isUnit_iff_res prime (w+1) (by omega) a).mpr ha.ne_zero) rows G (d+1)).mpr reduced
  have anchor := anchor_of_itinerary IntegerMultBounds.Networks.Shared50ModularControl.prime_odd
    (by omega : 0 < w+1) rows G valid det
  rw [show (LabelRing.res prime (w+1) (by omega)).mapMatrix G = C from lift] at anchor
  let sign : (ZMod M)ˣ := if negativeAnchor rows C then -1 else 1
  have signed : (Itinerary.run rows G (d+1)).det = (sign : ZMod M) := by
    cases h : negativeAnchor rows C <;> simpa [sign,h] using anchor
  exact queuedResidual_exec ports outside separate rows G valid sign signed H J hm hw positive body u S
    tail rest queueTail dest q empty original word layout free placed queue width blankDst savedFree tmpFree code

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host in
theorem returnedPayload_reads {volume : ℕ} (out : Fin volume → Fin 4)
    (source : ℤ → Fin 4) (p : ℤ) (left old tail : List (Fin (prime+4))) (len : old.length = volume)
    (outside : ∀ k, k < p ∨ p+volume ≤ k →
      RadixToBinary.binaryEncoding.encode (source k) =
        readAt blank left (old ++ tail) (k-p)) (k : ℤ) :
    RadixToBinary.binaryEncoding.encode (putWord source p (List.ofFn out) k) =
      readAt blank left (payloadWord out ++ tail) (k-p) := by
  by_cases before : k < p
  · rw [putWord_outside _ _ _ _ (.inl before),outside k (.inl before)]
    simp only [readAt,ite_eq_right (show ¬ 0 ≤ k-p by omega)]
  · let i := (k-p).toNat
    have offset : k-p = (i : ℤ) := by dsimp [i]; omega
    by_cases inside : i < volume
    · have atCell := BinaryDivide.putWord_getElem source p (List.ofFn out) i (by simpa using inside)
      rw [show p+(i : ℤ) = k by omega] at atCell
      rw [atCell,offset,readAt_nonneg,List.getElem?_append_left (by simpa [payloadWord] using inside)]
      simp [payloadWord,inside]
    · have after : p+volume ≤ k := by omega
      rw [putWord_outside _ _ _ _ (.inr (by simpa using after)),outside k (.inr after),offset]
      simp only [readAt_nonneg]
      rw [List.getElem?_append_right (by simpa [len] using Nat.le_of_not_gt inside),
        List.getElem?_append_right (by simpa [payloadWord] using Nat.le_of_not_gt inside)]
      simp [payloadWord,len]

open IntegerMultBounds.Machine in
private theorem payload_prefix_of_read {n : ℕ} (word : Fin n → ZMod 2) (source : ℤ → Fin 4) (head : ℤ)
    (L R : List (Fin (prime+4))) (read : ∀ z, readAt blank L R (z-head) =
      RadixToBinary.binaryEncoding.encode (putWord source head ((List.ofFn word).map SparseRoleCircuit.encode) z)) :
    R = payloadWord (SparseRoleCircuit.encode ∘ word) ++ R.drop n := by
  have cell (i : Fin n) : R[i.val]?.getD blank =
      RadixToBinary.binaryEncoding.encode (SparseRoleCircuit.encode (word i)) := by
    have tape := read (head+i.val)
    rw [add_sub_cancel_left,readAt_nonneg,BinaryDivide.putWord_getElem source head _ i.val
      (by simpa using i.isLt)] at tape
    simpa using tape
  have inside (i : Fin n) : i.val < R.length := by
    by_contra! shorter
    have h := cell i
    rw [List.getElem?_eq_none shorter] at h
    by_cases one : word i = 1 <;> simp [SparseRoleCircuit.encode,one,bitSymbol,blank,RadixToBinary.binaryEncoding] at h
  have len : n ≤ R.length := by
    by_contra! short
    exact (inside ⟨R.length,short⟩).false
  have first : R.take n = payloadWord (SparseRoleCircuit.encode ∘ word) := by
    apply List.ext_getElem
    · simp [payloadWord,Nat.min_eq_left len]
    · intro i hi hj
      have lt : i < n := by simpa [payloadWord] using hj
      have h := cell ⟨i,lt⟩
      rw [List.getElem?_eq_getElem (inside ⟨i,lt⟩)] at h
      simpa [payloadWord] using h
  rw [← first,List.take_append_drop]

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host in
open IntegerMultBounds.MathlibTM2.Fast.Main in
/-- Apply the anchor and then the projector residual on the same directory tapes. -/
theorem scheduledProjectorRecord_exec [M8.Machine.Net] {K : ℕ} {P U : Type}
    (e : (Fin r ⊕ Fin r) ≃ Fin (d+1)) (proj : Matrix (Fin r) (Fin r) ℚ)
    (idem : proj*proj = proj) (adm : Admissible prime proj)
    (α inv : Fin r → ZMod M) (reciprocal : ∀ i, α i * inv i = 1)
    (j : ℕ) (live : LabelStock.live r (w+1) 1 j = true)
    (H J : ℕ) (hm : M < 2^H) (hw : W < 2^J) (positive : 0 < W) :
    let N := rowSwapBlock.tapes+35
    let G := projectorResidual e (reduce M proj) α inv (physicalLabel r (w+1) j)
    let φ := LabelRing.res prime (w+1) (by omega)
    let C := projectorResidual e (reduce prime proj) (φ ∘ α) (φ ∘ inv) (LabelStock.residue r (w+1) 1 j)
    let rows := classPivots C
    ∀ (room : Record.size d+(N+2) ≤ K),
      let ports := directoryResidualBank d room (Fin.last N).castSucc
      let count := (58 : Fin 66).castAdd K
      let src := (24 : Fin 66).castAdd K
      let saved := (59 : Fin 66).castAdd K
      let tmp := (60 : Fin 66).castAdd K
      let anchor := directoryAnchorBank d K ((Nat.le_add_right ..).trans room)
      let regs := Function.Embedding.refl (Fin 6)
      ∀ (capacity : (anchorProgram d true).1+(anchorProgram d false).1+1 ≤ columnCapacity)
        (body : P → Pr P (66+K) columnCapacity prime U) (u : HS (66+K) columnCapacity prime U) (S : Stacks (66+K) prime)
        (tail rest : List (Fin (prime+4))) (dest : ℤ → Fin 4) (q : ℤ)
        (original : Fin (M^(d+1)*W) → ZMod 2) (source : ℤ → Fin 4) (head : ℤ),
      let queueTail := (S.R src).drop (M^(d+1)*W)
      (∀ z, q ≤ z → z < q+(M^(d+1)*W : ℕ) → dest z = blank) →
      let bank := columnBank.trans (archivePorts 0)
      let dst := ports (bank 24)
      let clean := fun (D : Stacks (66+K) prime) => ∀ i : Fin N, 35 ≤ i.val →
        D.L (ports (columnPorts i).castSucc) = [] ∧ D.R (ports (columnPorts i).castSucc) = []
      ShearReady bank H J G tail (fun _ : ZMod 2 => blank) (fun _ => blank) dest 0 q original (embStk ports S) →
      clean S → Record.Ready d 1 (w+1) W (embStk anchor S) →
      (∀ z, readAt blank (S.L src) (S.R src) (z-head) = RadixToBinary.binaryEncoding.encode
        (putWord source head ((List.ofFn original).map SparseRoleCircuit.encode) z)) → (S.R count).length = M^(d+1)*W →
      (∀ z, readAt blank (S.L dst) (S.R dst) z = blank) →
      (∀ i ∈ ([2,3,5] : List (Fin 6)), S.R (anchor (Record.port d regs i)) = []) →
      S.R ((54 : Fin 66).castAdd K) = residualSchedule C ++ rest →
      let sign := statePlacedNormalized anchor capacity (Nat.zero_lt_succ _) Empty.elim
        ((Record.program d regs).seq (moveR (Record.port d regs 5) (Record.port d regs 1) id))
      let V := M^(d+1)*W
      let returnWord := (Mult.ShortConv.transfer count dst saved tmp).seq (moveR saved src id)
      let record := (sign.seq (queuedResidual ports count src saved tmp d)).seq returnWord
      let recordTime := ((1+(Record.cost d 6 1 (w+1) W (negativeAnchor rows C)+(2*V+2))) +
        (6*V+6+(1+signedResidualTime U rows w W H J))) + ((4*V+4)+(2*V+2))
      let privateTapes := (List.finRange (66+K)).filter fun i => decide (58 ≤ i.val)
      let initialClear := (privateTapes.map fun i => 4*(S.L i).length+2*(S.R i).length+4).sum+1
      ∀ c, (∀ f, mnProgPush (body f) ≤ c) →
      ∀ (prefixes : ℕ → List (Fin (prime+4))) (pending : List ℕ) (archiveTail : List (Fin (prime+4))),
      let slots : Fin 7 ↪ Fin 58 := ⟨![45,46,2,47,48,44,49],by decide⟩
      let caller := (Fin.castAddEmb (n := 58) 8).trans (Fin.castAddEmb K)
      let scan := (goodRecordScanPorts.trans slots).trans caller
      S.R (scan 2) = (j :: pending).flatMap (LabelDirectory.entry prefixes r (w+1)) ++ archiveTail →
      (S.R (scan 0)).length = (prefixes j).length → (S.R (scan 1)).length = w → S.R (scan 3) = [] →
      ∃ z F n next, z.user = u.user ∧ n ≤ recordTime + (initialClear + 6*(max (mnProgPush record) c * recordTime)) +
          (1+(4*(prefixes j).length+4+(r*r*(4*(w+1)+4)+1)+1)) ∧
        Exec body ((record.seq (clearWorkTapes privateTapes)).seq (readWithSuccessorClock (scan 1) (advanceDirectory r scan))) (mk u S) n (mk z F) ∧
        (∀ i : Fin (66+K), 58 ≤ i.val → F.L i = [] ∧ F.R i = []) ∧
        (∀ x k, next (FlatCoordinateLayout.index (G.mulVec x) k) = original (FlatCoordinateLayout.index x k)) ∧
        F.R ((54 : Fin 66).castAdd K) = rest ∧ (∀ z, readAt blank (F.L src) (F.R src) (z-head) = RadixToBinary.binaryEncoding.encode
          (putWord source head ((List.ofFn next).map SparseRoleCircuit.encode) z)) ∧
        F.R (scan 2) = pending.flatMap (LabelDirectory.entry prefixes r (w+1)) ++ archiveTail ∧
        ∀ j : Fin 58, j ≠ 24 → j ≠ 54 → j ≠ 46 → let i := (j.castAdd 8).castAdd K
          F.L i = S.L i ∧ F.R i = S.R i := by
  intro N G φ C rows room ports count src saved tmp anchor regs capacity body u S tail rest dest q
    original source head queueTail empty bank dst clean layout free ready read width blankDst scratch schedule sign V returnWord
    record recordTime privateTapes initialClear c bodyBound
  intro prefixes pending archiveTail slots caller scan directory prefixWidth clock fresh
  suffices finished : ∃ z F n next, z.user = u.user ∧ n ≤ recordTime + (initialClear + 6*(max (mnProgPush record) c * recordTime)) ∧
        Exec body (record.seq (clearWorkTapes privateTapes)) (mk u S) n (mk z F) ∧
        (∀ i : Fin (66+K), 58 ≤ i.val → F.L i = [] ∧ F.R i = []) ∧
        (∀ x k, next (FlatCoordinateLayout.index (G.mulVec x) k) = original (FlatCoordinateLayout.index x k)) ∧
        F.R ((54 : Fin 66).castAdd K) = rest ∧ F.R src = payloadWord (SparseRoleCircuit.encode ∘ next) ++ queueTail ∧ F.L src = S.L src ∧
        ∀ j : Fin 58, j ≠ 24 → j ≠ 54 → let i := (j.castAdd 8).castAdd K
          F.L i = S.L i ∧ F.R i = S.R i by
    obtain ⟨z,F,n,next,user,time,run,clear,effect,queue,output,left,preserved⟩ := finished
    have before (i : Fin 6) (hp : (goodRecordScanPorts.trans slots) i ≠ 24)
        (hs : (goodRecordScanPorts.trans slots) i ≠ 54) : F.R (scan i) = S.R (scan i) :=
      (preserved _ hp hs).2
    obtain ⟨finish,hz,advance⟩ := advanceDirectoryRecord_exec body scan r w j prefixes pending archiveTail z F
      ((before 2 (by decide) (by decide)).trans directory)
      ((congrArg List.length (before 0 (by decide) (by decide))).trans prefixWidth)
      ((congrArg List.length (before 1 (by decide) (by decide))).trans clock)
      ((before 3 (by decide) (by decide)).trans fresh)
    have port : scan 2 = (46 : Fin 66).castAdd K := rfl
    let remaining := pending.flatMap (LabelDirectory.entry prefixes r (w+1)) ++ archiveTail
    refine ⟨finish,_,_,next,hz.trans user,Nat.add_le_add_right time _,Exec.seq run advance,?_,effect,
      (Function.update_of_ne (show (54 : Fin 66).castAdd K ≠ scan 2 by rw [port]; exact (Fin.castAddEmb K).injective.ne (by decide)) remaining F.R).trans queue,
      ?_,
      Function.update_self (scan 2) (pending.flatMap (LabelDirectory.entry prefixes r (w+1)) ++ archiveTail) F.R,?_⟩
    · intro i hi
      have off : i ≠ scan 2 := by intro eq; subst i; change 58 ≤ 46 at hi; omega
      exact ⟨(clear i hi).1,(Function.update_of_ne off remaining F.R).trans (clear i hi).2⟩
    · intro k
      have away : src ≠ scan 2 := by rw [port]; exact (Fin.castAddEmb K).injective.ne (by decide)
      dsimp only
      rw [Function.update_of_ne away,left,output]
      have orig := payload_prefix_of_read original source head _ _ read
      have outside (z : ℤ) (h : z < head ∨ head+(M^(d+1)*W : ℕ) ≤ z) := (read z).symm
      have replaced := returnedPayload_reads (SparseRoleCircuit.encode ∘ next) source head (S.L src)
        (payloadWord (SparseRoleCircuit.encode ∘ original)) queueTail (by simp [payloadWord]) (by
          intro z h
          have old := outside z h
          rw [putWord_outside _ _ _ _ (by simpa using h)] at old
          rw [← orig]; exact old) k
      simpa only [List.map_ofFn] using replaced.symm
    · intro k hp hs hd i
      have off : i ≠ scan 2 := caller.injective.ne hd
      exact ⟨(preserved k hp hs).1,(Function.update_of_ne off remaining F.R).trans (preserved k hp hs).2⟩
  let a : Record.Array d 1 (w+1) W := fun i => SparseRoleCircuit.encode (original (i.cast (by simp [ActualAffineScaling.modulus])))
  have encoded : Record.scalarArray a = SparseRoleCircuit.encode ∘ original := rfl
  have queue : S.R src = payloadWord a ++ queueTail := by
    rw [← Record.payloadWord_scalarArray a,encoded]
    exact payload_prefix_of_read original source head _ _ read
  have reg (i : Fin 6) : anchor (Record.port d regs i) = (directoryAnchorPorts i).castAdd K :=
    directoryAnchorBank_port _ i
  have cell (B : Stacks (66+K) prime) (i : Fin 6) :
      (embStk anchor B).R (Record.port d regs i) = B.R ((directoryAnchorPorts i).castAdd K) :=
    congrArg B.R (reg i)
  obtain ⟨_,word,y,D,t,hu,ht,run,frame,anchorLeft,input,pivots,_,_,keep,_,placed⟩ := scheduledAnchor_exec
    ((Nat.le_add_right ..).trans room) capacity C positive a original encoded body u S queueTail rest ready
    ((congrArg List.length (cell S 0)).trans width) ((cell S 1).trans queue)
    scratch ((cell S 4).trans schedule)
  have outside (i : Fin (N+2)) (h : i ≠ (Fin.last N).castSucc) :=
    frame (ports i) (directoryAnchor_residual_disjoint room _ i h)
  have bankFrame (i : Fin 35) := outside (bank i) (by
    intro eq; have val := congrArg Fin.val eq
    change i.val = rowSwapBlock.tapes+35 at val; omega)
  have layoutD : ShearReady bank H J G tail (fun _ : ZMod 2 => blank) (fun _ => blank) dest 0 q
      original (embStk ports D) := by
    apply layout.returnPayload (fun i _ => bankFrame i)
    intro z
    change _ = readAt blank (D.L (ports (bank 24))) (D.R (ports (bank 24))) _
    rw [(bankFrame 24).1,(bankFrame 24).2]
    exact (layout.src z).symm
  have cleanD : clean D := by
    intro i hi
    have pair := outside (columnPorts i).castSucc (by
      intro eq; have val := congrArg Fin.val eq; exact i.isLt.ne val)
    exact ⟨pair.1.trans (free i hi).1,pair.2.trans (free i hi).2⟩
  have control (i : Fin 6) (h₁ : i ≠ 1) (h₄ : i ≠ 4) (h₅ : i ≠ 5) :
      D.R (anchor (Record.port d regs i)) = S.R (anchor (Record.port d regs i)) := keep i h₁ h₄ h₅
  obtain ⟨z,F,n,hz,hn,res,result,cleanF,endCode,endInput,archive,residualLeft,off⟩ :=
    physicalResidualRecord_exec e proj idem adm α inv reciprocal j live H J hm hw positive room body y D tail rest
      queueTail dest q original word empty layoutD cleanD placed ((cell D 1).symm.trans input)
      (by have h := control 0 (by decide) (by decide) (by decide); rw [reg] at h; exact (congrArg List.length h).trans width)
      (fun z => by rw [(bankFrame 24).1,(bankFrame 24).2]; exact blankDst z)
      ((cell D 2).symm.trans ((control 2 (by decide) (by decide) (by decide)).trans (scratch 2 (by simp))))
      ((cell D 3).symm.trans ((control 3 (by decide) (by decide) (by decide)).trans (scratch 3 (by simp))))
      (by rw [directoryResidualBank_pivot]; apply (cell D 4).symm.trans; simpa only [List.append_assoc] using pivots)
  obtain ⟨next,after,effect⟩ := result
  have privateOff (k : Fin 66) (h : k ≠ 54) (i) := directoryResidualBank_off room (Fin.last N).castSucc i k h
  have countF := (off count ((Fin.castAddEmb K).injective.ne (by decide)) (privateOff 58 (by decide))).2
  have tmpF := (off tmp ((Fin.castAddEmb K).injective.ne (by decide)) (privateOff 60 (by decide))).2
  have savedF := (off saved ((Fin.castAddEmb K).injective.ne (by decide)) (privateOff 59 (by decide))).2
  have countD := control 0 (by decide) (by decide) (by decide)
  have tmpD := (control 3 (by decide) (by decide) (by decide)).trans (scratch 3 (by simp))
  have savedD := (control 2 (by decide) (by decide) (by decide)).trans (scratch 2 (by simp))
  rw [reg] at countD tmpD savedD
  have regsOff : [count,dst,saved,tmp].Nodup := by
    simp [count,dst,saved,tmp,List.nodup_cons]
    exact ⟨(privateOff 58 (by decide) _).symm,privateOff 59 (by decide) _,privateOff 60 (by decide) _⟩
  obtain ⟨last,hLast,collect,_⟩ := collectPayload_exec body regsOff (SparseRoleCircuit.encode ∘ next) z F
    ((congrArg List.length (countF.trans countD)).trans width) (tmpF.trans tmpD)
    (fun k => by have read := (after.src k).symm; rw [sub_zero] at read; exact read)
  let packed := payloadWord (SparseRoleCircuit.encode ∘ next)
  let B := {F with R := Function.update (Function.update F.R dst ((F.R dst).drop V)) saved (packed.reverse ++ F.R saved)}
  have acc : B.R saved = packed.reverse := by simp [B,savedF.trans savedD]
  have sep (i j : Fin 66) (h : i ≠ j) := (Fin.castAddEmb K).injective.ne h
  have oldSrc : B.R src = queueTail := by
    dsimp only [B]
    rw [Function.update_of_ne (show src ≠ saved from sep 24 59 (by decide)),Function.update_of_ne (show src ≠ dst from (privateOff 24 (by decide) _).symm),endInput]
  obtain ⟨finish,user,rewind⟩ := moveR_exec body saved src (sep 59 24 (by decide)) id last B
  have len : (B.R saved).length = V := by simp [acc,packed,payloadWord,V]
  rw [len] at rewind
  let finalBank := {B with R := movedR B.R saved src id (B.R saved)}
  have kept (i : Fin 66) (hsrc : i ≠ 24) (hbuf : i ≠ 59) (hdst : i.castAdd K ≠ dst) :
      finalBank.R (i.castAdd K) = F.R (i.castAdd K) := by
    have ns : i.castAdd K ≠ src := sep i 24 hsrc
    have nb : i.castAdd K ≠ saved := sep i 59 hbuf
    simp only [finalBank,movedR,B,Function.update_of_ne ns,Function.update_of_ne nb,Function.update_of_ne hdst]
  have schedOff : (54 : Fin 66).castAdd K ≠ dst := by
    rw [← directoryResidualBank_pivot (d := d) room (Fin.last N).castSucc]
    apply ports.injective.ne
    intro eq; have h := congrArg Fin.val eq; change rowSwapBlock.tapes+35 = 24 at h; omega
  have executed : Exec body record (mk u S) _ (mk finish finalBank) :=
    Exec.seq (Exec.seq run res) (Exec.seq collect rewind)
  have time : t+n+((4*V+4)+(2*V+2)) ≤ recordTime := Nat.add_le_add_right (Nat.add_le_add ht hn) _
  have unique : privateTapes.Nodup := (List.nodup_finRange _).filter _
  obtain ⟨z',same,clear⟩ := clearWorkTapes_exec body privateTapes unique finish finalBank
  have price := recordCleanup_cost_le privateTapes unique executed (le_max_left (mnProgPush record) c)
    (fun f => (bodyBound f).trans (le_max_right _ _))
  have mem (i : Fin (66+K)) : i ∈ privateTapes ↔ 58 ≤ i.val := by simp [privateTapes]
  have callerOff (j : Fin 58) : (j.castAdd 8).castAdd K ∉ privateTapes := by
    rw [mem]; exact Nat.not_le_of_lt j.isLt
  have queueOut : finalBank.R src = packed ++ queueTail := by simp [finalBank,movedR,acc,oldSrc]
  refine ⟨z',_,_,next,same.trans (user.trans (hLast.trans (hz.trans hu))),Nat.add_le_add time
    (price.trans (Nat.add_le_add_left (Nat.mul_le_mul_left 6 (Nat.mul_le_mul_left _ time)) _)),
    Exec.seq executed clear,?_,effect,?_,?_,?_,?_⟩
  · intro i hi; simp [(mem i).mpr hi]
  · apply (ite_eq_right (show (54 : Fin 66).castAdd K ∉ privateTapes from callerOff 54)).trans
    exact (kept 54 (by decide) (by decide) schedOff).trans (by simpa only [ports,directoryResidualBank_pivot] using endCode)
  · exact (ite_eq_right (callerOff 24)).trans queueOut
  · have originalLeft : D.L src = S.L src := by
      change D.L (anchor (Record.port d regs 1)) = S.L (anchor (Record.port d regs 1)) at anchorLeft
      rw [reg] at anchorLeft
      exact anchorLeft
    exact (ite_eq_right (callerOff 24)).trans (residualLeft.trans originalLeft)
  intro k hp hs i
  simp only [ite_eq_right (show i ∉ privateTapes from callerOff k)]
  have h₁ := frame i (directoryAnchorBank_off _ k hp hs)
  have h₂ := off i (by intro eq; apply hp; have h := congrArg Fin.val eq; exact Fin.ext h)
    (fun l => directoryResidualBank_off room _ l _ (by intro eq; apply hs; have h := congrArg Fin.val eq; exact Fin.ext h))
  have keepR := kept (k.castAdd 8) (by intro eq; apply hp; have h := congrArg Fin.val eq; exact Fin.ext h)
    (by intro eq; have h := congrArg Fin.val eq; change k.val = 59 at h; omega)
    (privateOff _ (by intro eq; apply hs; have h := congrArg Fin.val eq; exact Fin.ext h) _).symm
  exact ⟨h₂.1.trans h₁.1,keepR.trans (h₂.2.trans h₁.2)⟩

open IntegerMultBounds.Machine.FlatCoordinateLayout in
/-- The live output bit of the physical identity scan occurs at the enclosing
weighted child's address, for every trailing position. -/
theorem ScanData.physicalIdentity_bit (a : ScanData r d w W) (e : (Fin r ⊕ Fin r) ≃ Fin (d+1))
    (α inv : Fin r → ZMod M) (inverse : ∀ i, α i * inv i = 1) (j : ℕ)
    (live : LabelStock.live r (w+1) 1 j = true) (x : Fin (d+1) → ZMod M) (k : Fin W) :
    let data := a.physical e 1 α inv
    let result := Weighted.child r α inv (x ∘ e ∘ Sum.inl, x ∘ e ∘ Sum.inr)
    imageWord (data.matrix j) (a.input j) (index (Sum.elim result.1 result.2 ∘ e.symm) k) =
      a.input j (index x k) := by
  intro data result
  have signs := (a.physical_live e 1 (by simp) (IntegerMultBounds.Swap.Modular.admissible_one prime)
    α inv inverse j live).1
  have unit : IsUnit (data.matrix j).det := by rcases signs with h | h <;> rw [h] <;> simp
  have addr : (data.matrix j).mulVec x = Sum.elim result.1 result.2 ∘ e.symm := by
    simpa only [data,ScanData.physical,live,ite_true,result] using
      physicalIdentity_address (by omega : 0 < w+1) e j live α inv x
  rw [← addr]
  simp [imageWord,index,Matrix.mulVec_mulVec,Matrix.nonsing_inv_mul _ unit]

open IntegerMultBounds.Machine IntegerMultBounds.Machine.FlatCoordinateLayout in
/-- At a live record the scan writes the bit at its weighted image. A padding
record writes the same bit at its original address. -/
theorem ScanData.physicalIdentity_record (a : ScanData r d w W) (e : (Fin r ⊕ Fin r) ≃ Fin (d+1))
    (α inv : Fin r → ZMod M) (inverse : ∀ i, α i * inv i = 1) (j : ℕ)
    (x : Fin (d+1) → ZMod M) (k : Fin W) :
    let active := LabelStock.live r (w+1) 1
    let data := a.physical e 1 α inv
    let result := Weighted.child r α inv (x ∘ e ∘ Sum.inl, x ∘ e ∘ Sum.inr)
    let address := if active j then Sum.elim result.1 result.2 ∘ e.symm else x
    (outputRecord active data.matrix a.input j)[(index address k).val]? =
      some (RadixToBinary.binaryEncoding.encode (SparseRoleCircuit.encode (a.input j (index x k)))) := by
  intro active data result address
  have cell {N : ℕ} (word : Fin N → Fin 4) (i : Fin N) :
      (payloadWord word)[i.val]? = some (RadixToBinary.binaryEncoding.encode (word i)) := by
    rw [List.getElem?_eq_getElem (by simpa [payloadWord] using i.isLt)]
    simp [payloadWord]
  unfold outputRecord
  rw [cell]
  cases h : active j with
  | false => simp only [address,h,Bool.false_eq_true,ite_false,Function.comp_apply]
  | true =>
    simp only [address,h,ite_true,Function.comp_apply]
    rw [a.physicalIdentity_bit e α inv inverse j h x k]

private theorem recordQueue_lookup {α : Type*} {width : ℕ} (record : ℕ → List α)
    (length : ∀ j, (record j).length = width) (count j : ℕ) (hj : j < count) (k : Fin width)
    (tail : List α) :
    (((List.range count).flatMap record) ++ tail)[j*width+k.val]? = (record j)[k.val]? := by
  have size (n : ℕ) : ((List.range n).flatMap record).length = n*width := by
    induction n with
    | zero => simp
    | succ n ih => simp [List.range_succ,ih,length,Nat.succ_mul]
  induction count generalizing tail with
  | zero => omega
  | succ n ih =>
    rw [List.range_succ,List.flatMap_append,List.flatMap_singleton,List.append_assoc]
    by_cases eq : j = n
    · subst j
      rw [List.getElem?_append_right (by rw [size]; omega),size,Nat.add_sub_cancel_left,
        List.getElem?_append_left (by rw [length]; exact k.isLt)]
    · exact ih (by omega) _

open IntegerMultBounds.Machine IntegerMultBounds.Machine.FlatCoordinateLayout in
theorem ScanData.physicalIdentity_queue (a : ScanData r d w W) (e : (Fin r ⊕ Fin r) ≃ Fin (d+1))
    (α inv : Fin r → ZMod M) (inverse : ∀ i, α i * inv i = 1) (j : Fin a.records)
    (x : Fin (d+1) → ZMod M) (k : Fin W) :
    let active := LabelStock.live r (w+1) 1
    let data := a.physical e 1 α inv
    let queue := (List.range a.records).flatMap (outputRecord active data.matrix a.input) ++ a.inputTail
    let result := Weighted.child r α inv (x ∘ e ∘ Sum.inl, x ∘ e ∘ Sum.inr)
    let address := if active j then Sum.elim result.1 result.2 ∘ e.symm else x
    queue[j.val*(M^(d+1)*W)+(index address k).val]? =
      some (RadixToBinary.binaryEncoding.encode (SparseRoleCircuit.encode (a.input j (index x k)))) := by
  intro active data queue result address
  exact (recordQueue_lookup (outputRecord active data.matrix a.input)
    (fun _ => by simp [outputRecord,payloadWord]) _ j j.isLt (index address k) a.inputTail).trans
    (a.physicalIdentity_record e α inv inverse j x k)


end
end IntegerMultBounds.MathlibTM2.Cover.Fallback
