module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackScanState
public import IntegerMultBounds.MathlibTM2.Cover.FallbackRecordMasks
public import IntegerMultBounds.MathlibTM2.Cover.FallbackRecordCleanup
public import IntegerMultBounds.MathlibTM2.Cover.FallbackLeafFrame
import IntegerMultBounds.MathlibTM2.Cover.ProjectorWitness
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

/-- Materialize the payload length on caller tape 58 from the modulus and width.
The binary product and all temporary registers are restored after conversion. -/
def directoryCountPorts (K : ℕ) : Fin 10 ↪ Fin (66+K) :=
  let slots : Fin 10 ↪ Fin 66 := ⟨![2,53,59,60,61,62,63,64,65,58],by decide⟩
  slots.trans (Fin.castAddEmb K)

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host Node in
theorem directoryCount_exec {K Q A : ℕ} {P U : Type} (body : P → Pr P (66+K) Q A U)
    (fields H J modulus width : ℕ) (hm : modulus < 2^H) (hw : width < 2^J)
    (u : HS (66+K) Q A U) (S : Stacks (66+K) A) :
    let r := directoryCountPorts K
    let V := modulus^fields*width
    let L := fields*H+J
    S.R (r 0) = binSyms H modulus → S.R (r 1) = binSyms J width →
    (∀ i : Fin 10, 2 ≤ i → S.R (r i) = []) →
    ∃ z n, z.user = u.user ∧ n ≤ dimensionTime H J fields + 6*V + 13*L + 8 ∧
      Exec body ((dimensionPower r fields).seq ((toUnary (r 2) (r 9) (r 3) (r 4) (r 5)).seq
        (bclear (r 2)))) (mk u S) n
        (mk z {S with R := Function.update S.R (r 9) (List.replicate V tick)}) := by
  intro r V L base seed free
  obtain ⟨v,t,hu,ht,power⟩ := dimensionPower_exec body fields r H J modulus width hm hw u S
    base seed (fun i hi _ => free i hi)
  let D : Stacks (66+K) A := {S with R := Function.update S.R (r 2) (binSyms L V)}
  have fits : V < 2^L := by
    rw [show 2^L = (2^H)^fields * 2^J by simp [L,pow_add,← pow_mul,Nat.mul_comm H fields]]
    exact (Nat.mul_le_mul_right width (Nat.pow_le_pow_left hm.le fields)).trans_lt
      (Nat.mul_lt_mul_of_pos_left hw (by positivity))
  have blank (i : Fin 10) (hi : 2 < i) : D.R (r i) = [] := by
    simpa [D,Function.update_of_ne (r.injective.ne hi.ne'),free i hi.le]
  obtain ⟨y,m,hy,hm',convert⟩ := toUnary_exec_linear body
    (a := r 2) (z := r 9) (w := r 3) (t := r 4) (t₂ := r 5)
    (by simp [r.injective.eq_iff]) fits v D (by simp [D])
    (blank 3 (by decide)) (blank 4 (by decide)) (blank 5 (by decide))
  rw [blank 9 (by decide),List.append_nil] at convert
  let E : Stacks (66+K) A := {D with R := Function.update D.R (r 9) (List.replicate V tick)}
  obtain ⟨z,hz,_,clear⟩ := bclear_exec body (r 2) y E
  have len : (E.R (r 2)).length = L := by simp [E,D,r.injective.eq_iff,length_binSyms]
  rw [len] at clear
  refine ⟨z,_,hz.trans (hy.trans hu),?_,Exec.seq power (Exec.seq convert (clear.cast rfl ?_))⟩
  · omega
  · apply congrArg (mk z)
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases h : k = r 2
    · subst k
      simp [E,D,r.injective.eq_iff,free]
    · simp [E,D,Function.update_of_ne h,Function.update_apply]

/-- The installer reads the caller's trailing width and reciprocal clock. Its five
outputs are the descriptor and control cells in the anchor's private frame. -/
def directoryAnchorInstaller {K : ℕ} (room : 22 ≤ K) : Fin 17 ↪ Fin (66+K) :=
  let slots : Fin 17 ↪ Fin (66+22) := ⟨![0,1,2,66,67,68,71,72,73,9,53,70,45,69,84,85,86],by decide⟩
  (((slots.trans finSumFinEquiv.symm.toEmbedding).trans
    ((Function.Embedding.refl (Fin 66)).sumMap (Fin.castLEEmb room))).trans finSumFinEquiv.toEmbedding)

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host Record M8 in
theorem directoryAnchorFrame_exec {K Q : ℕ} {P U : Type} (room : size d ≤ K)
    (body : P → Pr P (66+K) Q prime U) (u : HS (66+K) Q prime U) (S : Stacks (66+K) prime)
    (J w W : ℕ) (bound : W < 2^J) :
    let r := directoryAnchorInstaller ((Nat.le_add_right 22 _).trans room)
    let host := directoryAnchorBank d K room
    let privateBank := (Fin.castAddEmb (n := size d) 6).trans host
    S.R ((53 : Fin 66).castAdd K) = binSyms J W → (S.R ((45 : Fin 66).castAdd K)).length = w →
    (∀ i, S.L (privateBank i) = [] ∧ S.R (privateBank i) = []) →
    ∃ z F n, z.user = u.user ∧ n ≤ (10*J+12)+(21*(w+1)+12)+1 ∧
      Exec body (installFieldHeaders r) (mk u S) n (mk z F) ∧ Ready d 1 (w+1) W (embStk host F) ∧
      ∀ h, h ∉ fieldMarkers r → F.L h = S.L h ∧ F.R h = S.R h := by
  intro r host privateBank width clock free
  have atSlot (i : Fin (size d)) : (privateBank i).val = 66+i.val := by
    simp [privateBank,host,directoryAnchorBank]
  have num (n : ℕ) (hn : n < 22) : ((OfNat.ofNat n : Fin (size d))).val = n :=
    Nat.mod_eq_of_lt (hn.trans_le (Nat.le_add_right 22 _))
  have key (i : Fin 17) (n : ℕ) (hn : n < 22) (v : (r i).val = 66+n) :
      r i = privateBank (OfNat.ofNat n) := Fin.ext (by rw [atSlot,num n hn]; exact v)
  obtain ⟨z,F,n,user,time,run,frame,keep⟩ := installFieldFrame_exec body r privateBank
    (key 13 3 (by decide) rfl) (key 11 4 (by decide) rfl) (key 14 18 (by decide) rfl)
    (key 15 19 (by decide) rfl) (key 16 20 (by decide) rfl) J bound u S width clock
    (by intro j lo hi
        have scratch (i : Fin 17) (n : ℕ) (hn : n < 22) (v : (r i).val = 66+n) :
            S.R (r i) = [] := (congrArg S.R (key i n hn v)).trans (free _).2
        fin_cases j <;> first | (exfalso; revert lo; decide) | (exfalso; revert hi; decide) |
          exact scratch _ 0 (by decide) rfl | exact scratch _ 1 (by decide) rfl |
          exact scratch _ 2 (by decide) rfl | exact scratch _ 5 (by decide) rfl |
          exact scratch _ 6 (by decide) rfl | exact scratch _ 7 (by decide) rfl)
    (fun k _ => free k)
  refine ⟨z,F,n,user,time,run,?_,keep⟩
  intro k x
  by_cases hk : k.val = 17
  · have eq : k = 17 := Fin.ext (hk.trans (num 17 (by decide)).symm)
    subst k
    have off : privateBank 17 ∉ fieldMarkers r := by
      simp only [fieldMarkers,List.mem_cons,List.not_mem_nil,or_false]
      intro h
      rcases h with h | h | h | h | h <;> have v := congrArg Fin.val h <;>
        rw [atSlot,num 17 (by decide)] at v <;> first
          | exact (by decide : (83 : ℕ) ≠ 69) v | exact (by decide : (83 : ℕ) ≠ 70) v
          | exact (by decide : (83 : ℕ) ≠ 84) v | exact (by decide : (83 : ℕ) ≠ 85) v
          | exact (by decide : (83 : ℕ) ≠ 86) v
    have stable := keep _ off
    change _ = readAt blank (F.L (privateBank 17)) (F.R (privateBank 17)) _
    rw [stable.1,stable.2,(free _).1,(free _).2,readAt_nil_left,wordTape_nil]
    simp [AtomBank.outer,Nat.mod_eq_of_lt (show 17 < 22+anchorSlots d by omega)]
  · exact frame k hk x

/-- Only five cells of the private anchor bank receive headers. -/
theorem directoryAnchorMarker_private {K : ℕ} (room : Record.size d ≤ K) (k : Fin (66+K))
    (marked : k ∈ fieldMarkers (directoryAnchorInstaller ((Nat.le_add_right 22 _).trans room))) :
    ∃ i : Fin (Record.size d), directoryAnchorBank d K room (i.castAdd 6) = k := by
  simp only [fieldMarkers,List.mem_cons,List.not_mem_nil,or_false] at marked
  rcases marked with h | h | h | h | h <;> subst k
  all_goals first | exact ⟨3,rfl⟩ | exact ⟨4,rfl⟩ | exact ⟨18,rfl⟩ | exact ⟨19,rfl⟩ | exact ⟨20,rfl⟩

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

/-- Omit the exceptional matrix archive from the generated ordinary branch's
workspace. The remaining private tapes can still be cleared after every call. -/
def directoryMatrixTape [M8.Machine.Net] {K : ℕ}
    (room : Record.size d+(rowSwapBlock.tapes+35+2) ≤ K) : Fin (66+K) :=
  directoryResidualBank d room (Fin.last (rowSwapBlock.tapes+35)).castSucc (archivePorts 0 (columnBank 34))

def directoryOrdinaryBank [M8.Machine.Net] {K : ℕ}
    (room : Record.size d+(rowSwapBlock.tapes+35+2) ≤ K+1) : Fin (66+K) ↪ Fin (66+(K+1)) :=
  (directoryMatrixTape room).succAboveEmb

theorem directoryOrdinaryBank_caller [M8.Machine.Net] {K : ℕ}
    (room : Record.size d+(rowSwapBlock.tapes+35+2) ≤ K+1) (i : Fin 66) :
    directoryOrdinaryBank room (i.castAdd K) = i.castAdd (K+1) := by
  apply Fin.succAbove_of_castSucc_lt
  change i.val < (directoryMatrixTape room).val
  unfold directoryMatrixTape
  rw [directoryResidualBank_private room _ _ (by
    intro eq; have h := congrArg Fin.val eq; change 34 = rowSwapBlock.tapes+35 at h; omega)]
  omega

open IntegerMultBounds.MathlibTM2.Stack Host in
/-- The ordinary branch's blank-workspace invariant is exactly the exceptional
branch's cleanup guarantee, with the matrix stream left available. -/
theorem directoryOrdinaryBank_clear_iff [M8.Machine.Net] {K A : ℕ}
    (room : Record.size d+(rowSwapBlock.tapes+35+2) ≤ K+1) (S : Stacks (66+(K+1)) A) :
    let bank := directoryOrdinaryBank room
    (∀ i : Fin (66+K), 58 ≤ i.val → (embStk bank S).L i = [] ∧ (embStk bank S).R i = []) ↔
      ∀ k, 58 ≤ k.val → k ≠ directoryMatrixTape room → S.L k = [] ∧ S.R k = [] := by
  intro bank
  have privatePort (i : Fin (66+K)) : 58 ≤ (bank i).val ↔ 58 ≤ i.val := by
    constructor
    · intro high
      by_contra! low
      let j : Fin 66 := ⟨i.val,by omega⟩
      have eq : i = j.castAdd K := Fin.ext rfl
      rw [eq,directoryOrdinaryBank_caller] at high
      exact (Nat.not_le_of_lt low) high
    · intro high
      by_contra! low
      let j : Fin 66 := ⟨(bank i).val,by omega⟩
      have eq : bank i = bank (j.castAdd K) := by rw [directoryOrdinaryBank_caller]; exact Fin.ext rfl
      have h := congrArg Fin.val (bank.injective eq)
      change i.val = (bank i).val at h
      omega
  constructor
  · intro clear k high off
    obtain ⟨i,eq⟩ := Fin.exists_succAbove_eq off
    change bank i = k at eq
    subst k
    exact clear i ((privatePort i).1 high)
  · intro clear i high
    exact clear (bank i) ((privatePort i).2 high) (Fin.succAbove_ne _ _)

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host in
/-- Run a good or padding branch on its own tapes, including its cleanup, then
consume exactly its matrix from the shared archive outside that bank. -/
theorem ScanData.advanceEmbeddedRecord_exec {T K Q : ℕ} {P F U : Type}
    (data : ScanData r d w W) (j : ℕ) (inside : j < data.records)
    (bank : Fin T ↪ Fin K) (archive : Fin K) (outside : ∀ i, bank i ≠ archive)
    (width tmp : Fin T) (apart : width ≠ tmp) (labels : P → F)
    (body : P → Pr P T Q prime U) (host : F → Pr F K Q prime U)
    (calls : ∀ f, host (labels f) = embProg bank labels (body f))
    (branch : Pr P T Q prime U) (u : HS K Q prime U) (S : Stacks K prime)
    (v : HS T Q prime U) (D : Stacks T prime) (n : ℕ)
    (run : Exec body branch (Host.mk (embDn bank u) (embStk bank S)) n (Host.mk v D))
    (clock : (D.R width).length = data.H) (free : D.R tmp = [])
    (queue : S.R archive = data.matrices j) :
    ∃ z B, z.user = v.user ∧ embStk bank B = D ∧ B.R archive = data.matrices (j+1) ∧
      (∀ k, (∀ i, bank i ≠ k) → B.L k = S.L k ∧ (k ≠ archive → B.R k = S.R k)) ∧
      Exec host ((embProg bank labels branch).seq (dropWords (bank width) archive (bank tmp) ((d+1)*(d+1))))
        (Host.mk u S) (n+((d+1)*(d+1)*(4*data.H+4)+1)) (Host.mk z B) := by
  obtain ⟨y,E,placed,_,user,localBank,frame⟩ := exec_emb bank.injective calls run u rfl S rfl
  have cell (i : Fin T) : E.R (bank i) = D.R i := congrArg (fun B => Stacks.R B i) localBank
  obtain ⟨z,hz,consume⟩ := dropWords_exec host (outside width) (bank.injective.ne apart)
    (outside tmp).symm ((d+1)*(d+1)) data.H y E ((congrArg List.length (cell width)).trans clock)
    ((cell tmp).trans free)
  rw [(frame archive outside).2,queue,data.matrices_succ inside,
    ← length_matrixWords prime data.H (data.matrix j),List.drop_left] at consume
  refine ⟨z,_,hz.trans user,?_,Function.update_self ..,?_,Exec.seq placed consume⟩
  · rw [← localBank]
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    exact Function.update_of_ne (outside i) _ _
  · intro k off
    exact ⟨(frame k off).1,fun ne => (Function.update_of_ne ne _ _).trans (frame k off).2⟩

/-- At canonical width the entire matrix advance fits in one payload traversal. -/
theorem matrixAdvance_le_volume (d w W : ℕ) (positive : 0 < W) :
    (d+1)*(d+1)*(4*(prime^(w+1)).size+4)+1 ≤ (prime^(w+1))^(d+1)*W := by
  let m := prime^(w+1)
  have big : 32 ≤ m := by
    have exp : 5 ≤ IntegerMultBounds.Networks.coefficientExponent :=
      IntegerMultBounds.Networks.le_coefficientExponent (by
        exact (by decide : 5 ≤ 2^3).trans (Nat.pow_le_pow_right (by decide) (by decide : 3 ≤ 53000)))
    exact (IntegerMultBounds.Networks.two_pow_le_coefficientBound exp).trans
      (IntegerMultBounds.Networks.Shared50ModularControl.coefficientBound_lt_prime.le.trans
        (Nat.le_self_pow (by omega : w+1 ≠ 0) prime))
  have digits (k : ℕ) (hk : 5 ≤ k) : 4*(k+1)+5 ≤ 2^k := by
    induction k, hk using Nat.le_induction with
    | base => decide
    | succ k hk ih => rw [pow_succ]; omega
  have header : 4*m.size+5 ≤ m := by
    have lower : 5 < m.size := Nat.lt_size.mpr big
    obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m.size ≠ 0)
    rw [hk]
    exact (digits k (by omega)).trans (Nat.lt_size.mp (by omega : k < m.size))
  have side : d+1 ≤ 2^d := Nat.lt_two_pow_self
  have square : (d+1)*(d+1) ≤ m^d := by
    calc
      _ ≤ (2^d)*(2^d) := Nat.mul_le_mul side side
      _ = 4^d := (mul_pow 2 2 d).symm
      _ ≤ m^d := Nat.pow_le_pow_left (by omega) _
  calc
    _ ≤ (d+1)*(d+1)*(4*m.size+5) := by change _ ≤ _; dsimp [m]; nlinarith
    _ ≤ m^d*m := Nat.mul_le_mul square header
    _ ≤ m^(d+1)*W := Nat.le_mul_of_pos_right _ positive

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host in
/-- The classified scan shares one archive. Good and padding programs operate on
the embedded bank, while the exceptional program consumes its matrix directly. -/
theorem ScanData.classifiedArchive_exec [M8.Machine.Net] {K Q : ℕ} {P F U : Type}
    (data : ScanData r d w W) (room : Record.size d+(rowSwapBlock.tapes+35+2) ≤ K+1)
    (labels : P → F) (projector : Matrix (Fin r) (Fin r) ℚ) (idem : projector*projector = projector)
    (factor : IntegerMultBounds.Swap.LowerTriangular.Factorization Finset.univ Finset.univ projector)
    (small : ∀ k ∈ IntegerMultBounds.Swap.Modular.factorizationDenominators factor, k < prime)
    (rankFits : projector.rank ≤ r) :
    let proj := reduce M projector
    let live := LabelStock.live r (w+1) 1
    let bad := fun j => fallbackBit rankFits proj (physicalLabel r (w+1) j)
    let bank := directoryOrdinaryBank room
    let archive := directoryMatrixTape room
    let width := (2 : Fin 66).castAdd K
    let tmp := (59 : Fin 66).castAdd K
    let liveMask := (57 : Fin 66).castAdd K
    let mode := (56 : Fin 66).castAdd K
    ∀ (body : P → Pr P (66+K) Q prime U) (host : F → Pr F (66+(K+1)) Q prime U)
    (calls : ∀ f, host (labels f) = embProg bank labels (body f))
    (good skip : Pr P (66+K) Q prime U) (exceptional : Pr F (66+(K+1)) Q prime U)
    (ordinaryCost badCost : ℕ → ℕ) (ready : ℕ → Stacks (66+K) prime → Prop)
    (release : ∀ j S k bits, k = liveMask ∨ k = mode → ready j S →
      ready j {S with R := Function.update S.R k bits})
    (ordinary : ∀ j, j < data.records → ¬ (live j = true ∧ bad j = true) →
      ∀ u S, ready j S → ∃ v D n, v.user = u.user ∧ ready (j+1) D ∧
        D.R liveMask = S.R liveMask ∧ D.R mode = S.R mode ∧ (D.R width).length = data.H ∧
        D.R tmp = [] ∧ n ≤ ordinaryCost j ∧
        Exec body (if live j then good else skip) (Host.mk u S) n (Host.mk v D))
    (repair : ∀ j, j < data.records → live j = true → bad j = true →
      ∀ u S, ready j (embStk bank S) → S.R archive = data.matrices j →
      ∃ v D n, v.user = u.user ∧ ready (j+1) (embStk bank D) ∧ D.R archive = data.matrices (j+1) ∧
        D.R (bank liveMask) = S.R (bank liveMask) ∧ D.R (bank mode) = S.R (bank mode) ∧
        n ≤ badCost j ∧ Exec host exceptional (Host.mk u S) n (Host.mk v D))
    (u : HS (66+(K+1)) Q prime U) (S : Stacks (66+(K+1)) prime) (start : ready 0 (embStk bank S))
    (queue : S.R archive = data.matrices 0)
    (liveBits : S.R (bank liveMask) = (List.range data.records).map fun j => bitSymbol (live j))
    (badBits : S.R (bank mode) = (List.range data.records).map fun j => bitSymbol (bad j)),
    let advance := dropWords (bank width) archive (bank tmp) ((d+1)*(d+1))
    let cost := fun j => if live j && bad j then badCost j else ordinaryCost j + ((d+1)*(d+1)*(4*data.H+4)+1)
    let exceptionalCount := ((∑ k ∈ Finset.range projector.rank, (k+1)*(r+1))*data.records)/prime
    let priced := fun n => ∀ parents baseline budget, data.records = parents*M^(r*r) →
      let ordinaryTime := data.records*(baseline+6)+2
      ordinaryTime ≤ budget →
      (∀ j < data.records, ¬ (live j = true ∧ bad j = true) →
        ordinaryCost j + ((d+1)*(d+1)*(4*data.H+4)+1) ≤ baseline ∨
        (data.H = Nat.size (prime^(w+1)) ∧ 0 < W ∧ ordinaryCost j + M^(d+1)*W ≤ baseline)) →
      (0 < exceptionalCount → ∀ j < data.records, live j = true → bad j = true →
        badCost j ≤ baseline+(budget-ordinaryTime)/exceptionalCount) → n ≤ budget
    ∃ z B n, z.user = u.user ∧ (ready data.records (embStk bank B) ∧ B.R archive = data.matrixTail) ∧
      B.R (bank liveMask) = [] ∧ B.R (bank mode) = [] ∧ priced n ∧ n ≤ ((List.range data.records).map fun j => cost j+2+4).sum+2 ∧
      Exec host (classifiedScan (bank liveMask) (bank mode) ((embProg bank labels good).seq advance)
        exceptional ((embProg bank labels skip).seq advance)) (Host.mk u S) n (Host.mk z B) := by
  intro proj live bad bank archive width tmp liveMask mode body host calls good skip exceptional ordinaryCost badCost ready
    release ordinary repair u S start queue liveBits badBits advance cost exceptionalCount priced
  have outside (i : Fin (66+K)) : bank i ≠ archive := Fin.succAbove_ne _ _
  have apart : width ≠ tmp := (Fin.castAddEmb K).injective.ne (by decide : (2 : Fin 66) ≠ 59)
  have selectors : liveMask ≠ mode := (Fin.castAddEmb K).injective.ne (by decide : (57 : Fin 66) ≠ 56)
  let inv := fun j B => ready j (embStk bank B) ∧ B.R archive = data.matrices j
  have releaseAt (j) (B : Stacks (66+(K+1)) prime) (k : Fin (66+K)) (bits) (sel : k = liveMask ∨ k = mode)
      (h : inv j B) : inv j {B with R := Function.update B.R (bank k) bits} := by
    refine ⟨?_,(Function.update_of_ne (outside k).symm _ _).trans h.2⟩
    convert release j (embStk bank B) k bits sel h.1 using 1
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    change Function.update B.R (bank k) bits (bank i) = Function.update (B.R ∘ bank) k bits i
    by_cases eq : i = k
    · subst i; simp
    · simp [eq,bank.injective.ne eq]
  have last : data.matrices data.records = data.matrixTail := by
    simp [ScanData.matrices,List.drop_of_length_le (List.length_range.le)]
  suffices scan : ∃ z B n, z.user = u.user ∧ inv data.records B ∧ B.R (bank liveMask) = [] ∧
      B.R (bank mode) = [] ∧ n ≤ ((List.range data.records).map fun j => cost j+2+4).sum+2 ∧
      Exec host (classifiedScan (bank liveMask) (bank mode) ((embProg bank labels good).seq advance)
        exceptional ((embProg bank labels skip).seq advance)) (Host.mk u S) n (Host.mk z B) by
    obtain ⟨z,B,n,user,done,l,m,time,run⟩ := scan
    refine ⟨z,B,n,user,⟨done.1,done.2.trans last⟩,l,m,?_,time,run⟩
    intro parents baseline budget shape ordinaryTime fits ordinaryBound exceptionalBound
    have ordinaryPrice (j : ℕ) (hj : j < data.records) (h : ¬ (live j = true ∧ bad j = true)) :
        ordinaryCost j + ((d+1)*(d+1)*(4*data.H+4)+1) ≤ baseline := by
      rcases ordinaryBound j hj h with direct | ⟨canonical,positive,bound⟩
      · exact direct
      · rw [canonical]
        exact (Nat.add_le_add_left (matrixAdvance_le_volume d w W positive) _).trans bound
    obtain ⟨g₀,unit,generic⟩ := LabelProjector.residue_witness (w := w+1) (by omega) projector idem factor small rankFits
    obtain ⟨extra,allowance,exceptionalPrice⟩ := fallbackAllowance (List.range data.records) badCost
      (fun j => live j = true ∧ bad j = true) exceptionalCount baseline (budget-ordinaryTime)
      (fun pos j hj h => exceptionalBound pos j (List.mem_range.mp hj) h.1 h.2)
    suffices total : n ≤ data.records*(baseline+6)+exceptionalCount*extra+2 by
      dsimp only [ordinaryTime] at fits allowance
      omega
    apply time.trans (classifiedRecordTime_le w projector.rank parents rankFits proj data.records shape g₀ unit generic
      cost baseline extra ?_ ?_ ?_)
    · intro j hj hl hb
      have no : ¬ (live j = true ∧ bad j = true) := fun h => Bool.noConfusion (hb.symm.trans h.2)
      simpa only [cost,show live j = true from hl,show bad j = false from hb,Bool.and_false,ite_false,
        Bool.false_eq_true] using ordinaryPrice j hj no
    · intro j hj hl
      have no : ¬ (live j = true ∧ bad j = true) := fun h => Bool.noConfusion (hl.symm.trans h.1)
      simpa [cost,show live j = false from hl] using ordinaryPrice j hj no
    · intro j hj hl hb
      simpa [cost,show live j = true from hl,show bad j = true from hb] using exceptionalPrice j (List.mem_range.mpr hj) ⟨hl,hb⟩
  apply classifiedScan_exec host _ _ (bank.injective.ne selectors) _ _ _ data.records live bad cost inv
    (fun j B k bits sel h => by rcases sel with rfl | rfl
                                · exact releaseAt j B _ bits (Or.inl rfl) h
                                · exact releaseAt j B _ bits (Or.inr rfl) h) _ u S ⟨start,queue⟩ liveBits badBits
  intro j inside v B current
  by_cases both : live j = true ∧ bad j = true
  · obtain ⟨z,D,n,user,next,tail,l,m,price,run⟩ := repair j inside both.1 both.2 v B current.1 current.2
    exact ⟨z,D,n,user,⟨next,tail⟩,l,m,by simpa [cost,both.1,both.2] using price,by simpa [both.1,both.2] using run⟩
  obtain ⟨y,D,n,user,next,l,m,clock,free,price,run⟩ := ordinary j inside both (embDn bank v) (embStk bank B) current.1
  obtain ⟨z,E,hu,localBank,tail,_,step⟩ := data.advanceEmbeddedRecord_exec j inside bank archive outside
    width tmp apart labels body host calls _ v B y D n run clock free current.2
  have cell (i : Fin (66+K)) : E.R (bank i) = D.R i := congrArg (fun C => Stacks.R C i) localBank
  refine ⟨z,E,n+((d+1)*(d+1)*(4*data.H+4)+1),hu.trans user,⟨by rw [localBank]; exact next,tail⟩,(cell _).trans l,(cell _).trans m,?_,?_⟩
  · simpa [cost,both] using price
  · cases hl : live j <;> cases hb : bad j <;> first | simpa [hl,hb,advance] using step | exact (both ⟨hl,hb⟩).elim

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host in
open IntegerMultBounds.MathlibTM2.Fast.Main in
/-- Apply the anchor and then the projector residual on the same directory tapes. -/
theorem scheduledProjectorRecord_exec [M8.Machine.Net] {K : ℕ} {P U : Type}
    (e : (Fin r ⊕ Fin r) ≃ Fin (d+1)) (proj : Matrix (Fin r) (Fin r) ℚ)
    (idem : proj*proj = proj) (adm : Admissible prime proj)
    (α inv : Fin r → ZMod M) (reciprocal : ∀ i, α i * inv i = 1)
    (j : ℕ) (live : LabelStock.live r (w+1) 1 j = true)
    (data : ScanData r d w W) (inside : j < data.records) (J : ℕ) (hm : M < 2^data.H) (hw : W < 2^J) (positive : 0 < W) :
    let H := data.H
    let physical := data.physical e proj α inv
    let tail := physical.matrices (j+1)
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
        (body : P → Pr P (66+K) columnCapacity prime U) (u : HS (66+K) columnCapacity prime U) (initial : Stacks (66+K) prime)
        (rest : List (Fin (prime+4)))
        (original : Fin (M^(d+1)*W) → ZMod 2) (source : ℤ → Fin 4) (head : ℤ),
      let counters := directoryCountPorts K
      let countProgram := (dimensionPower counters (d+1)).seq
        ((toUnary (counters 2) count (counters 3) (counters 4) (counters 5)).seq (bclear (counters 2)))
      let setupTime := dimensionTime H J (d+1) + 6*(M^(d+1)*W) + 13*((d+1)*H+J) + 8
      initial.R (counters 0) = binSyms H M → initial.R (counters 1) = binSyms J W →
      (∀ k, 58 ≤ k.val → k ≠ directoryMatrixTape room → initial.L k = [] ∧ initial.R k = []) →
      let S := {initial with R := Function.update initial.R count (List.replicate (M^(d+1)*W) Node.tick)}
      let queueTail := (S.R src).drop (M^(d+1)*W)
      let bank := columnBank.trans (archivePorts 0)
      let dst := ports (bank 24)
      let clean := fun (D : Stacks (66+K) prime) => ∀ i : Fin N, 35 ≤ i.val →
        D.L (ports (columnPorts i).castSucc) = [] ∧ D.R (ports (columnPorts i).castSucc) = []
      let headerSrc := residualCallerHeaders.trans (Fin.castAddEmb K)
      let headerDst := residualHeaderPorts.trans (bank.trans ports)
      let headers := Record.copyLeafHeaders headerSrc headerDst ((64 : Fin 66).castAdd K)
        ((65 : Fin 66).castAdd K) (List.finRange 5)
      S.R (headerSrc 2) = binSyms 1 1 → S.R (headerSrc 3) = binSyms H (1 : ZMod M).val →
      S.R (ports (bank 34)) = physical.matrices j →
      (∀ z, readAt blank (S.L src) (S.R src) (z-head) = RadixToBinary.binaryEncoding.encode
        (putWord source head ((List.ofFn original).map SparseRoleCircuit.encode) z)) →
      S.R ((54 : Fin 66).castAdd K) = residualSchedule C ++ rest →
      let installer := directoryAnchorInstaller ((Nat.le_add_right 22 _).trans ((Nat.le_add_right ..).trans room : Record.size d ≤ K))
      let sign := (installFieldHeaders installer).seq (statePlacedNormalized anchor capacity (Nat.zero_lt_succ _) Empty.elim
        ((Record.program d regs).seq (moveR (Record.port d regs 5) (Record.port d regs 1) id)))
      let V := M^(d+1)*W
      let returnWord := (Mult.ShortConv.transfer count dst saved tmp).seq (moveR saved src id)
      let matrixTape := directoryMatrixTape room
      let advanceMatrix := dropWords (ports (bank 2)) matrixTape (ports (bank 0)) ((d+1)*(d+1))
      let record := (((sign.seq headers).seq (queuedResidual ports count src saved tmp d)).seq returnWord).seq advanceMatrix
      let recordTime := (((10*J+12)+(21*(w+1)+12)+1) + (1+(Record.cost d 6 1 (w+1) W (negativeAnchor rows C)+(2*V+2)))) +
        (6*(2*H+J+w)+37) + (6*V+6+(1+signedResidualTime U rows w W H J)) + ((4*V+4)+(2*V+2)) + ((d+1)*(d+1)*(4*H+4)+1)
      let privateTapes := (List.finRange (66+K)).filter fun i => decide (58 ≤ i.val ∧ i ≠ matrixTape)
      let initialClear := privateTapes.length*4+2*V+1
      ∀ c, (∀ f, mnProgPush (body f) ≤ c) →
      ∀ (prefixes : ℕ → List (Fin (prime+4))) (pending : List ℕ) (archiveTail : List (Fin (prime+4))),
      let slots : Fin 7 ↪ Fin 58 := ⟨![45,46,2,47,48,44,49],by decide⟩
      let caller := (Fin.castAddEmb (n := 58) 8).trans (Fin.castAddEmb K)
      let scan := (goodRecordScanPorts.trans slots).trans caller
      S.R (scan 2) = (j :: pending).flatMap (LabelDirectory.entry prefixes r (w+1)) ++ archiveTail →
      (S.R (scan 0)).length = (prefixes j).length → (S.R (scan 1)).length = w → S.R (scan 3) = [] →
      ∃ z F n next, z.user = u.user ∧ n ≤ setupTime + (recordTime + (initialClear + 6*(max (mnProgPush record) c * recordTime)) +
          (1+(4*(prefixes j).length+4+(r*r*(4*(w+1)+4)+1)+1))) ∧
        Exec body (countProgram.seq ((record.seq (clearWorkTapes privateTapes)).seq (readWithSuccessorClock (scan 1) (advanceDirectory r scan)))) (mk u initial) n (mk z F) ∧
        F.R matrixTape = tail ∧ (∀ i : Fin (66+K), 58 ≤ i.val → i ≠ matrixTape → F.L i = [] ∧ F.R i = []) ∧
        (∀ x k, next (FlatCoordinateLayout.index (G.mulVec x) k) = original (FlatCoordinateLayout.index x k)) ∧
        F.R ((54 : Fin 66).castAdd K) = rest ∧ (∀ z, readAt blank (F.L src) (F.R src) (z-head) = RadixToBinary.binaryEncoding.encode
          (putWord source head ((List.ofFn next).map SparseRoleCircuit.encode) z)) ∧
        F.R (scan 2) = pending.flatMap (LabelDirectory.entry prefixes r (w+1)) ++ archiveTail ∧
        ∀ j : Fin 58, j ≠ 24 → j ≠ 54 → j ≠ 46 → let i := (j.castAdd 8).castAdd K
          F.L i = S.L i ∧ F.R i = S.R i := by
  intro H physical tail N G φ C rows room ports count src saved tmp anchor regs capacity body initialUser initial rest
    original source head counters countProgram setupTime base seed initialBlank S queueTail bank dst clean headerSrc headerDst headers one padded matrix read schedule installer sign V returnWord
    matrixTape advanceMatrix record recordTime privateTapes initialClear c bodyBound
  intro prefixes pending archiveTail slots caller scan directory prefixWidth clock fresh
  have archiveVal : matrixTape.val = 66+(Record.size d+34) :=
    directoryResidualBank_private room _ _ (by intro eq; have h := congrArg Fin.val eq
                                               change 34 = rowSwapBlock.tapes+35 at h; omega)
  have afterCount (k : Fin (66+K)) (hi : 58 < k.val) (off : k ≠ matrixTape) :
      S.L k = [] ∧ S.R k = [] := by
    have ne : k ≠ count := fun eq => by rw [eq] at hi; exact (Nat.lt_irrefl 58) hi
    exact ⟨(initialBlank k hi.le off).1,(Function.update_of_ne ne _ _).trans (initialBlank k hi.le off).2⟩
  have vacant (i : Fin 10) (hi : 2 ≤ i) : initial.R (counters i) = [] := by
    have range : 58 ≤ (counters i).val ∧ (counters i).val < 66 := by
      let slots : Fin 10 → Fin 66 := ![2,53,59,60,61,62,63,64,65,58]
      exact (by decide : ∀ k : Fin 10, 2 ≤ k → 58 ≤ (slots k).val ∧ (slots k).val < 66) i hi
    exact (initialBlank _ range.1 (fun eq => by have h := congrArg Fin.val eq; change _ = matrixTape.val at h; omega)).2
  have blankPort (i : Fin (N+2)) (np : i ≠ (Fin.last N).castSucc) (na : i ≠ bank 34) :=
    afterCount (ports i) (by rw [directoryResidualBank_private room _ _ np]; omega) (ports.injective.ne na)
  have emptyBank (i : Fin 35) (off : i ≠ 34) := blankPort (bank i) (by
    intro eq; have h := congrArg Fin.val eq; change i.val = rowSwapBlock.tapes+35 at h; omega) (bank.injective.ne off)
  have free : clean S := by
    intro i hi
    exact blankPort _ (by intro eq; have h := congrArg Fin.val eq; exact i.isLt.ne h)
      (by intro eq; have h := congrArg Fin.val eq; change i.val = 34 at h; omega)
  have vacantAnchor (i : Fin (Record.size d)) : S.L (anchor (i.castAdd 6)) = [] ∧ S.R (anchor (i.castAdd 6)) = [] := by
    have val : (anchor (i.castAdd 6)).val = 66+i.val := by simp [anchor,directoryAnchorBank]
    apply afterCount _ (by omega)
    intro eq; have h := congrArg Fin.val eq; omega
  have scratch (i : Fin 6) (hi : i ∈ ([2,3,5] : List (Fin 6))) :
      S.R (anchor (Record.port d regs i)) = [] := by
    have v : (anchor (Record.port d regs i)).val = (directoryAnchorPorts i).val :=
      congrArg Fin.val (directoryAnchorBank_port _ i)
    have lo : 58 < (directoryAnchorPorts i).val := (by decide : ∀ k ∈ ([2,3,5] : List (Fin 6)), 58 < (directoryAnchorPorts k).val) i hi
    exact (afterCount _ (by omega) (fun eq => by have h := congrArg Fin.val eq; omega)).2
  obtain ⟨u,st,startUser,startTime,start⟩ := directoryCount_exec body (d+1) H J M W hm hw initialUser initial
    base seed vacant
  have currentMatrix : S.R (ports (bank 34)) = matrixWords prime H G ++ tail := by
    apply matrix.trans
    have step := physical.matrices_succ (j := j) inside
    simpa only [physical,ScanData.physical,live,if_true,H,G,tail] using step
  have width : (S.R count).length = M^(d+1)*W := by simp [S]
  suffices finished : ∃ z F n next, z.user = u.user ∧ n ≤ recordTime + (initialClear + 6*(max (mnProgPush record) c * recordTime)) ∧
        Exec body (record.seq (clearWorkTapes privateTapes)) (mk u S) n (mk z F) ∧
        F.R matrixTape = tail ∧ (∀ i : Fin (66+K), 58 ≤ i.val → i ≠ matrixTape → F.L i = [] ∧ F.R i = []) ∧
        (∀ x k, next (FlatCoordinateLayout.index (G.mulVec x) k) = original (FlatCoordinateLayout.index x k)) ∧
        F.R ((54 : Fin 66).castAdd K) = rest ∧ F.R src = payloadWord (SparseRoleCircuit.encode ∘ next) ++ queueTail ∧ F.L src = S.L src ∧
        ∀ j : Fin 58, j ≠ 24 → j ≠ 54 → let i := (j.castAdd 8).castAdd K
          F.L i = S.L i ∧ F.R i = S.R i by
    obtain ⟨z,F,n,next,user,time,run,archiveRest,clear,effect,queue,output,left,preserved⟩ := finished
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
    refine ⟨finish,_,_,next,(hz.trans user).trans startUser,Nat.add_le_add startTime (Nat.add_le_add_right time _),
      Exec.seq start (Exec.seq run advance),
      (Function.update_of_ne (show matrixTape ≠ scan 2 from port ▸ directoryResidualBank_off room _ _ 46 (by decide)) remaining F.R).trans archiveRest,?_,effect,
      (Function.update_of_ne (show (54 : Fin 66).castAdd K ≠ scan 2 by rw [port]; exact (Fin.castAddEmb K).injective.ne (by decide)) remaining F.R).trans queue,
      ?_,
      Function.update_self (scan 2) (pending.flatMap (LabelDirectory.entry prefixes r (w+1)) ++ archiveTail) F.R,?_⟩
    · intro i hi ne
      have off : i ≠ scan 2 := by intro eq; subst i; change 58 ≤ 46 at hi; omega
      exact ⟨(clear i hi ne).1,(Function.update_of_ne off remaining F.R).trans (clear i hi ne).2⟩
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
  have anchorRoom : Record.size d ≤ K := (Nat.le_add_right ..).trans room
  have widthHeader : S.R ((53 : Fin 66).castAdd K) = binSyms J W := by
    change Function.update initial.R count (List.replicate (M^(d+1)*W) Node.tick) ((53 : Fin 66).castAdd K) = _
    rw [Function.update_of_ne (show (53 : Fin 66).castAdd K ≠ count from (Fin.castAddEmb K).injective.ne (by decide))]
    exact seed
  obtain ⟨v,prepared,b,vu,bt,install,ready,stable⟩ := directoryAnchorFrame_exec anchorRoom body u S J w W hw
    widthHeader clock vacantAnchor
  have before (k : Fin (66+K)) (h : ∀ i : Fin (Record.size d), anchor (i.castAdd 6) ≠ k) :=
    stable k (fun marked => by obtain ⟨i,eq⟩ := directoryAnchorMarker_private anchorRoom k marked; exact h i eq)
  have controlBefore (i : Fin 6) := before (anchor (Record.port d regs i)) (fun k eq => by
    have v := congrArg Fin.val (anchor.injective eq)
    change k.val = Record.size d + (regs i).val at v
    omega)
  have preparedCell (i : Fin 6) : (embStk anchor prepared).R (Record.port d regs i) =
      S.R ((directoryAnchorPorts i).castAdd K) := by
    change prepared.R (anchor (Record.port d regs i)) = _
    exact (controlBefore i).2.trans (congrArg S.R (reg i))
  obtain ⟨_,word,y,D,t,hu,ht,run,frameB,anchorLeft,input,pivots,_,_,keep,_,placed⟩ := scheduledAnchor_exec
    anchorRoom capacity C positive a original encoded body v prepared queueTail rest ready
    ((congrArg List.length (preparedCell 0)).trans width)
    ((preparedCell 1).trans queue)
    (fun i hi => (controlBefore i).2.trans (scratch i hi)) ((preparedCell 4).trans schedule)
  have frame (k : Fin (66+K)) (off : ∀ i, anchor i ≠ k) :=
    And.intro ((frameB k off).1.trans (before k (fun i => off _)).1)
      ((frameB k off).2.trans (before k (fun i => off _)).2)
  have outside (i : Fin (N+2)) (h : i ≠ (Fin.last N).castSucc) :=
    frame (ports i) (directoryAnchor_residual_disjoint room _ i h)
  have bankFrame (i : Fin 35) := outside (bank i) (by
    intro eq; have val := congrArg Fin.val eq
    change i.val = rowSwapBlock.tapes+35 at val; omega)
  have untouched (k : Fin 66) (h : ∀ i, directoryAnchorPorts i ≠ k) :
      D.R (k.castAdd K) = S.R (k.castAdd K) := (frame _ (by
    intro i
    induction i using Fin.addCases with
    | left i =>
      intro eq
      have v := congrArg Fin.val eq
      simp [anchor,directoryAnchorBank] at v
      omega
    | right i => rw [show anchor (Fin.natAdd (Record.size d) i) = _ from directoryAnchorBank_port anchorRoom i]; exact (Fin.castAddEmb K).injective.ne (h i))).2
  have initialAt (k : Fin 66) (h : k ≠ 58) :
      S.R (k.castAdd K) = initial.R (k.castAdd K) :=
    Function.update_of_ne ((Fin.castAddEmb K).injective.ne h) _ _
  obtain ⟨yH,DH,hUser,copy,layoutH,blankH,leftH,rightH⟩ :=
    directoryResidualHeaders_exec d body y D H J w W G tail original room
      ((untouched 2 (by decide)).trans ((initialAt 2 (by decide)).trans base))
      ((untouched 53 (by decide)).trans widthHeader) ((untouched 28 (by decide)).trans one)
      ((untouched 44 (by decide)).trans padded)
      ((congrArg List.length (untouched 45 (by decide))).trans clock)
      ((untouched 64 (by decide)).trans ((initialAt 64 (by decide)).trans (vacant 7 (by decide))))
      ((untouched 65 (by decide)).trans ((initialAt 65 (by decide)).trans (vacant 8 (by decide))))
      (fun i hi => ⟨(bankFrame i).1.trans (emptyBank i hi).1,(bankFrame i).2.trans (emptyBank i hi).2⟩)
      ((bankFrame 34).2.trans currentMatrix)
  have callerH (k : Fin 66) : DH.R (k.castAdd K) = D.R (k.castAdd K) := rightH _ (by
    intro i eq
    have val := congrArg Fin.val eq
    change (ports (bank (residualHeaderPorts i))).val = k.val at val
    rw [directoryResidualBank_private room _ _ (by
      intro same; have v := congrArg Fin.val same
      change (residualHeaderPorts i).val = rowSwapBlock.tapes+35 at v
      omega)] at val
    omega)
  have cleanD : clean DH := by
    intro i hi
    have pair := outside (columnPorts i).castSucc (by
      intro eq; have val := congrArg Fin.val eq; exact i.isLt.ne val)
    have unchanged := rightH (ports (columnPorts i).castSucc) (by
      intro j eq
      have v := congrArg Fin.val (ports.injective eq)
      change (residualHeaderPorts j).val = i.val at v
      omega)
    exact ⟨(congrFun leftH _).trans (pair.1.trans (free i hi).1),unchanged.trans (pair.2.trans (free i hi).2)⟩
  have control (i : Fin 6) (h₁ : i ≠ 1) (h₄ : i ≠ 4) (h₅ : i ≠ 5) :
      D.R (anchor (Record.port d regs i)) = S.R (anchor (Record.port d regs i)) := (keep i h₁ h₄ h₅).trans (controlBefore i).2
  obtain ⟨z,F,n,hz,hn,res,result,cleanF,endCode,endInput,archive,residualLeft,off⟩ :=
    physicalResidualRecord_exec e proj idem adm α inv reciprocal j live H J hm hw positive room body yH DH tail rest
      queueTail (fun _ => blank) 0 original word (by simp)
      ⟨layoutH.modulus,layoutH.width,layoutH.one,layoutH.padded,layoutH.clock,layoutH.archive,
        layoutH.scratch,layoutH.src,layoutH.dst⟩ cleanD placed ((callerH 24).trans ((cell D 1).symm.trans input))
      (by have h := control 0 (by decide) (by decide) (by decide); rw [reg] at h; exact (congrArg List.length ((callerH 58).trans h)).trans width)
      blankH
      ((callerH 59).trans ((cell D 2).symm.trans ((control 2 (by decide) (by decide) (by decide)).trans (scratch 2 (by simp)))))
      ((callerH 60).trans ((cell D 3).symm.trans ((control 3 (by decide) (by decide) (by decide)).trans (scratch 3 (by simp)))))
      (by rw [directoryResidualBank_pivot]; apply (callerH 54).trans; apply (cell D 4).symm.trans; simpa only [List.append_assoc] using pivots)
  obtain ⟨next,after,effect⟩ := result
  have privateOff (k : Fin 66) (h : k ≠ 54) (i) := directoryResidualBank_off room (Fin.last N).castSucc i k h
  have countF := ((off count ((Fin.castAddEmb K).injective.ne (by decide)) (privateOff 58 (by decide))).2).trans (callerH 58)
  have tmpF := ((off tmp ((Fin.castAddEmb K).injective.ne (by decide)) (privateOff 60 (by decide))).2).trans (callerH 60)
  have savedF := ((off saved ((Fin.castAddEmb K).injective.ne (by decide)) (privateOff 59 (by decide))).2).trans (callerH 59)
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
  let returned := {B with R := movedR B.R saved src id (B.R saved)}
  have returnedCell (i : Fin 35) (ne : i ≠ 24) : returned.R (ports (bank i)) = F.R (ports (bank i)) := by
    have ns : ports (bank i) ≠ src := privateOff 24 (by decide) _
    have nb : ports (bank i) ≠ saved := privateOff 59 (by decide) _
    have nd : ports (bank i) ≠ dst := ports.injective.ne (bank.injective.ne ne)
    simp only [returned,movedR,B,Function.update_of_ne ns,Function.update_of_ne nb,Function.update_of_ne nd]
  obtain ⟨advanced,advancedUser,consume⟩ := consumeMatrix_exec (bank.trans ports) body finish returned H G tail
    ((returnedCell 34 (by decide)).trans after.archive)
    ((congrArg List.length ((returnedCell 2 (by decide)).trans after.modulus)).trans (length_binSyms ..))
    ((returnedCell 0 (by decide)).trans (after.scratch 0 (by decide)).2)
  let finalBank := {returned with R := Function.update returned.R matrixTape tail}
  have matrixOff (i : Fin 66) (h : i ≠ 54) : i.castAdd K ≠ matrixTape := (privateOff i h _).symm
  have matrixPivot : (54 : Fin 66).castAdd K ≠ matrixTape := by
    rw [← directoryResidualBank_pivot (d := d) room (Fin.last N).castSucc]
    apply ports.injective.ne
    intro eq; have v := congrArg Fin.val eq; change rowSwapBlock.tapes+35 = 34 at v; omega
  have unchanged (i : Fin 66) : finalBank.R (i.castAdd K) = returned.R (i.castAdd K) :=
    Function.update_of_ne (by by_cases eq : i = 54; · exact eq ▸ matrixPivot
                              · exact matrixOff i eq) _ _
  have kept (i : Fin 66) (hsrc : i ≠ 24) (hbuf : i ≠ 59) (hdst : i.castAdd K ≠ dst) :
      finalBank.R (i.castAdd K) = F.R (i.castAdd K) := by
    have ns : i.castAdd K ≠ src := sep i 24 hsrc
    have nb : i.castAdd K ≠ saved := sep i 59 hbuf
    rw [unchanged]
    simp only [returned,movedR,B,Function.update_of_ne ns,Function.update_of_ne nb,Function.update_of_ne hdst]
  have schedOff : (54 : Fin 66).castAdd K ≠ dst := by
    rw [← directoryResidualBank_pivot (d := d) room (Fin.last N).castSucc]
    apply ports.injective.ne
    intro eq; have h := congrArg Fin.val eq; change rowSwapBlock.tapes+35 = 24 at h; omega
  have executed : Exec body record (mk u S) _ (mk advanced finalBank) :=
    Exec.seq (Exec.seq (Exec.seq (Exec.seq (Exec.seq install run) copy) res) (Exec.seq collect rewind)) consume
  have time : (b+t)+(6*(2*H+J+w)+37)+n+((4*V+4)+(2*V+2))+((d+1)*(d+1)*(4*H+4)+1) ≤ recordTime := Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add_right (Nat.add_le_add bt ht) _) hn) _) _
  have unique : privateTapes.Nodup := (List.nodup_finRange _).filter _
  obtain ⟨z',same,clear⟩ := clearWorkTapes_exec body privateTapes unique advanced finalBank
  have price := recordCleanup_cost_le privateTapes unique executed (le_max_left (mnProgPush record) c)
    (fun f => (bodyBound f).trans (le_max_right _ _))
  have mem (i : Fin (66+K)) : i ∈ privateTapes ↔ 58 ≤ i.val ∧ i ≠ matrixTape := by simp [privateTapes]
  have initialCost : (privateTapes.map fun i => 4*(S.L i).length+2*(S.R i).length+4).sum+1 ≤ initialClear := by
    simpa only [initialClear,List.length_replicate] using counterFrameCleanup_le privateTapes unique initial
      (fun i hi => initialBlank i ((mem i).1 hi).1 ((mem i).1 hi).2) count (List.replicate V Node.tick)
  have callerOff (j : Fin 58) : (j.castAdd 8).castAdd K ∉ privateTapes := by
    rw [mem]; exact fun h => Nat.not_le_of_lt j.isLt h.1
  have queueOut : finalBank.R src = packed ++ queueTail := by rw [show finalBank.R src = returned.R src from unchanged 24]; simp [returned,movedR,acc,oldSrc]
  refine ⟨z',_,_,next,same.trans (advancedUser.trans (user.trans (hLast.trans (hz.trans (hUser.trans (hu.trans vu)))))),Nat.add_le_add time
    (price.trans (Nat.add_le_add initialCost (Nat.mul_le_mul_left 6 (Nat.mul_le_mul_left _ time)))),
    Exec.seq executed clear,?_,?_,effect,?_,?_,?_,?_⟩
  · exact (ite_eq_right (show matrixTape ∉ privateTapes by simp [mem])).trans (Function.update_self ..)
  · intro i hi ne; simp [(mem i).mpr ⟨hi,ne⟩]
  · apply (ite_eq_right (show (54 : Fin 66).castAdd K ∉ privateTapes from callerOff 54)).trans
    exact (kept 54 (by decide) (by decide) schedOff).trans (by simpa only [ports,directoryResidualBank_pivot] using endCode)
  · exact (ite_eq_right (callerOff 24)).trans queueOut
  · have originalLeft : D.L src = S.L src := by
      change D.L (anchor (Record.port d regs 1)) = prepared.L (anchor (Record.port d regs 1)) at anchorLeft
      have both := anchorLeft.trans (controlBefore 1).1
      rw [reg] at both
      exact both
    exact (ite_eq_right (callerOff 24)).trans (residualLeft.trans ((congrFun leftH _).trans originalLeft))
  intro k hp hs i
  simp only [ite_eq_right (show i ∉ privateTapes from callerOff k)]
  have h₁ := frame i (directoryAnchorBank_off _ k hp hs)
  have h₂ := off i (by intro eq; apply hp; have h := congrArg Fin.val eq; exact Fin.ext h)
    (fun l => directoryResidualBank_off room _ l _ (by intro eq; apply hs; have h := congrArg Fin.val eq; exact Fin.ext h))
  have keepR := kept (k.castAdd 8) (by intro eq; apply hp; have h := congrArg Fin.val eq; exact Fin.ext h)
    (by intro eq; have h := congrArg Fin.val eq; change k.val = 59 at h; omega)
    (privateOff _ (by intro eq; apply hs; have h := congrArg Fin.val eq; exact Fin.ext h) _).symm
  exact ⟨h₂.1.trans ((congrFun leftH _).trans h₁.1),keepR.trans (h₂.2.trans ((callerH _).trans h₁.2))⟩

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
