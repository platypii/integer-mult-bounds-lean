import IntegerMultBounds.Machine.ScalingControl
import IntegerMultBounds.Machine.CountedCopyReuse
import IntegerMultBounds.Machine.Placement
import IntegerMultBounds.Machine.WordSegments
import IntegerMultBounds.Machine.GrowingCounterData

/-! Literal finite-piece splitting for fixed-coefficient scaling. The program
is a fixed sequence of reusable counted copies, one per fixed coefficient
piece. Supplied binary piece lengths are preserved; no descriptor synthesis or
merge is hidden in the split. Source and output origins/backgrounds are arbitrary. -/

namespace IntegerMultBounds.Machine.ScalingSplit

/-- Physical payload offset of a clipped block boundary. -/
def offset (Q c B j : ℕ) : ℕ := ScalingControl.boundary Q c j * B

private theorem boundary_mono {Q c i j : ℕ} (hc : 0 < c) (hij : i ≤ j) :
    ScalingControl.boundary Q c i ≤ ScalingControl.boundary Q c j := by
  have hh : ScalingControl.ceiling (i*Q) c ≤ ScalingControl.ceiling (j*Q) c := by
    apply (ScalingControl.ceiling_le_iff hc).mpr
    have hright := (ScalingControl.ceiling_le_iff (x := j*Q) (y := ScalingControl.ceiling (j*Q) c) hc).mp le_rfl
    nlinarith
  exact min_le_min_left Q hh

theorem offset_mono {Q c B i j : ℕ} (hc : 0 < c) (hij : i ≤ j) :
    offset Q c B i ≤ offset Q c B j := Nat.mul_le_mul_right B (boundary_mono hc hij)

theorem offset_le (Q c B j : ℕ) : offset Q c B j ≤ Q*B :=
  Nat.mul_le_mul_right B (ScalingControl.boundary_le Q c j)

@[simp] theorem offset_zero {Q c B : ℕ} (hc : 0 < c) : offset Q c B 0 = 0 := by
  simp only [offset,ScalingControl.boundary_zero hc,zero_mul]

@[simp] theorem offset_last {Q c B : ℕ} (hc : 0 < c) : offset Q c B c = Q*B := by
  simp only [offset,ScalingControl.boundary_last hc]

/-- The exact contiguous payload piece, including possibly empty intervals. -/
def piece (Q c B : ℕ) (input : List (Fin 4)) (j : Fin c) : List (Fin 4) :=
  (input.drop (offset Q c B j.val)).take (offset Q c B (j.val+1)-offset Q c B j.val)

theorem piece_length {Q c B : ℕ} (hc : 0 < c) (input : List (Fin 4)) (hlen : input.length = Q*B)
    (j : Fin c) :
    (piece Q c B input j).length = offset Q c B (j.val+1)-offset Q c B j.val := by
  have hm := offset_mono (Q := Q) (B := B) hc (Nat.le_succ j.val)
  have hb := offset_le Q c B (j.val+1)
  simp only [piece,List.length_take,List.length_drop,hlen]
  omega

private theorem source_piece {Q c B : ℕ} (hc : 0 < c) (source : ℤ → Fin 4) (p : ℤ)
    (input : List (Fin 4)) (hlen : input.length = Q*B) (j : Fin c) :
    putWord (putWord source p input) (p+offset Q c B j.val) (piece Q c B input j) =
      putWord source p input := by
  let a := offset Q c B j.val
  let b := offset Q c B (j.val+1)
  have hab : a ≤ b := offset_mono hc (Nat.le_succ j.val)
  have ha : a ≤ input.length := by rw [hlen]; exact offset_le Q c B j.val
  have hdrop : (input.drop a).drop (b-a) = input.drop b := by
    rw [List.drop_drop]
    congr 1
    omega
  have hsplit : input.take a ++ (piece Q c B input j) ++ input.drop b = input := by
    change input.take a ++ (input.drop a).take (b-a) ++ input.drop b = input
    rw [List.append_assoc,← hdrop,List.take_append_drop,List.take_append_drop]
  have hh := WordSegments.middle source p (input.take a) (piece Q c B input j) (input.drop b)
  rw [hsplit,List.length_take,Nat.min_eq_left ha] at hh
  exact hh

abbrev TapeCount (c : ℕ) := 4+(c+c)

def outputSlot {c : ℕ} (j : Fin c) : Fin (TapeCount c) := Fin.natAdd 4 (Fin.castAdd c j)
def descriptorSlot {c : ℕ} (j : Fin c) : Fin (TapeCount c) := Fin.natAdd 4 (Fin.natAdd c j)

def slots {c : ℕ} (j : Fin c) : Fin (4+(c+c)) ≃ Fin (TapeCount c) :=
  (Equiv.swap 1 (outputSlot j)).trans (Equiv.swap 3 (descriptorSlot j))

/-- Source at zero, work clock at two, and two idle frame tapes. The two final
banks hold the arbitrary-origin piece buffers and immutable piece descriptors. -/
def bank {c : ℕ} (source : ℤ → Fin 4) (outputs : Fin c → ℤ → Fin 4)
    (descriptors : Fin c → List Bool) (p : ℤ) (origins : Fin c → ℤ) : Tapes (TapeCount c) 0 :=
  (CountedCopyReuse.bank source (fun _ => blank) CountedCopyReuse.empty (fun _ => blank) p 0 1 0).append
    ((⟨origins,outputs⟩ : Tapes c 0).append
      ⟨fun _ => 1,fun j => CountedCopyReuse.binary (descriptors j)⟩)

def stage {c : ℕ} (j : Fin c) : Program (TapeCount c) 16 0 :=
  Placement.placed (u := c+c) CountedCopyReuse.program (slots j)

private theorem low_ne_output {c : ℕ} (i : Fin 4) (j : Fin c) :
    Fin.castAdd (c+c) i ≠ outputSlot j := by
  intro h
  have hh := congrArg Fin.val h
  simp only [outputSlot,Fin.val_castAdd,Fin.val_natAdd] at hh
  have hi := i.isLt
  omega

private theorem low_ne_descriptor {c : ℕ} (i : Fin 4) (j : Fin c) :
    Fin.castAdd (c+c) i ≠ descriptorSlot j := by
  intro h
  have hh := congrArg Fin.val h
  simp only [descriptorSlot,Fin.val_castAdd,Fin.val_natAdd] at hh
  have hi := i.isLt
  omega

private theorem output_ne_descriptor {c : ℕ} (i j : Fin c) : outputSlot i ≠ descriptorSlot j := by
  intro h
  have hh := congrArg Fin.val h
  simp only [outputSlot,descriptorSlot,Fin.val_castAdd,Fin.val_natAdd] at hh
  have hi := i.isLt
  omega

private theorem slots_low {c : ℕ} (j : Fin c) (i : Fin 4) :
    slots j (Fin.castAdd (c+c) i) =
      ![Fin.castAdd (c+c) 0, outputSlot j, Fin.castAdd (c+c) 2, descriptorSlot j] i := by
  have hj := j.isLt
  fin_cases i <;> simp only [slots, Equiv.trans_apply, Equiv.swap_apply_def]
  all_goals split_ifs <;> try rfl
  all_goals simp only [Fin.ext_iff, Fin.val_castAdd, outputSlot, descriptorSlot,
    Fin.val_natAdd] at *
  all_goals norm_num [Nat.mod_eq_of_lt (by omega : 1 < 4+(c+c)),
    Nat.mod_eq_of_lt (by omega : 3 < 4+(c+c))] at *
  all_goals omega

private theorem slots_output {c : ℕ} (j k : Fin c) :
    slots j (outputSlot k) = if k = j then 1 else outputSlot k := by
  have hj := j.isLt
  have hk := k.isLt
  simp only [slots, Equiv.trans_apply, Equiv.swap_apply_def]
  split_ifs
  all_goals simp only [Fin.ext_iff, outputSlot, descriptorSlot,
    Fin.val_natAdd, Fin.val_castAdd] at *
  all_goals norm_num [Nat.mod_eq_of_lt (by omega : 1 < 4+(c+c)),
    Nat.mod_eq_of_lt (by omega : 3 < 4+(c+c))] at *
  all_goals omega

private theorem slots_descriptor {c : ℕ} (j k : Fin c) :
    slots j (descriptorSlot k) = if k = j then 3 else descriptorSlot k := by
  have hj := j.isLt
  have hk := k.isLt
  simp only [slots, Equiv.trans_apply, Equiv.swap_apply_def]
  split_ifs
  all_goals simp only [Fin.ext_iff, outputSlot, descriptorSlot,
    Fin.val_natAdd, Fin.val_castAdd] at *
  all_goals norm_num [Nat.mod_eq_of_lt (by omega : 1 < 4+(c+c)),
    Nat.mod_eq_of_lt (by omega : 3 < 4+(c+c))] at *
  all_goals omega

theorem active_bank {c : ℕ} (j : Fin c) (source : ℤ → Fin 4)
    (outputs : Fin c → ℤ → Fin 4) (descriptors : Fin c → List Bool) (p : ℤ) (origins : Fin c → ℤ) :
    Placement.active (s := 4) (slots j) (bank source outputs descriptors p origins) =
      CountedCopyReuse.bank source (outputs j) CountedCopyReuse.empty
        (CountedCopyReuse.binary (descriptors j)) p (origins j) 1 1 := by
  unfold Placement.active
  simp only [slots_low]
  unfold bank CountedCopyReuse.bank
  congr 1 <;> funext i <;> fin_cases i <;>
    simp [Tapes.append, outputSlot, descriptorSlot, Fin.addCases]

private theorem extra_bank {c : ℕ} (j : Fin c) (source source' : ℤ → Fin 4)
    (outputs : Fin c → ℤ → Fin 4) (output' : ℤ → Fin 4)
    (descriptors : Fin c → List Bool) (p p' r' : ℤ) (origins : Fin c → ℤ) :
    Placement.extra (s := 4) (slots j)
      (bank source' (Function.update outputs j output') descriptors p' (Function.update origins j r')) =
    Placement.extra (s := 4) (slots j) (bank source outputs descriptors p origins) := by
  unfold Placement.extra
  congr 1 <;> funext i <;> induction i using Fin.addCases with
  | left k =>
    rw [show Fin.natAdd 4 (Fin.castAdd c k) = outputSlot k from rfl,slots_output]
    by_cases hk : k = j
    · subst k
      simp only
      rw [show (1 : Fin (TapeCount c)) = Fin.castAdd (c+c) (1 : Fin 4) by
        apply Fin.ext
        simp [Nat.mod_eq_of_lt (by omega : 1 < 4+(c+c))]]
      simp [bank,Tapes.append,CountedCopyReuse.bank]
    · simp [hk,bank,Tapes.append,outputSlot,Fin.addCases]
  | right k =>
    rw [show Fin.natAdd 4 (Fin.natAdd c k) = descriptorSlot k from rfl,slots_descriptor]
    by_cases hk : k = j
    · subst k
      simp only
      rw [show (3 : Fin (TapeCount c)) = Fin.castAdd (c+c) (3 : Fin 4) by
        apply Fin.ext
        simp [Nat.mod_eq_of_lt (by omega : 3 < 4+(c+c))]]
      simp [bank,Tapes.append,CountedCopyReuse.bank]
    · simp [hk,bank,Tapes.append,descriptorSlot,Fin.addCases]

theorem replace_bank {c : ℕ} (j : Fin c) (source source' : ℤ → Fin 4)
    (outputs : Fin c → ℤ → Fin 4) (output' : ℤ → Fin 4)
    (descriptors : Fin c → List Bool) (p p' r' : ℤ) (origins : Fin c → ℤ) :
    Placement.replace (s := 4) (slots j) (bank source outputs descriptors p origins)
      (CountedCopyReuse.bank source' output' CountedCopyReuse.empty
        (CountedCopyReuse.binary (descriptors j)) p' r' 1 1) =
    bank source' (Function.update outputs j output') descriptors p' (Function.update origins j r') := by
  have ha := active_bank j source' (Function.update outputs j output') descriptors p'
    (Function.update origins j r')
  simp only [Function.update_self] at ha
  rw [Placement.replace,← ha,← extra_bank j source source' outputs output' descriptors p p' r' origins]
  exact Placement.view _ _

theorem stage_hoare {c : ℕ} (j : Fin c) (source : ℤ → Fin 4)
    (outputs : Fin c → ℤ → Fin 4) (descriptors : Fin c → List Bool)
    (p : ℤ) (origins : Fin c → ℤ) (xs : List (Fin 4))
    (hcount : Counter.value (descriptors j) = xs.length) :
    HoareTime (stage j)
      (fun v => v = bank (putWord source p xs) outputs descriptors p origins)
      (fun v => v = bank (putWord source p xs)
        (Function.update outputs j (putWord (outputs j) (origins j) xs)) descriptors
        (p+xs.length) (Function.update origins j (origins j+xs.length)))
      (5*xs.length+7*(descriptors j).length+16) := by
  have h := Placement.hoare_at
    (CountedCopyReuse.copy_hoare source (outputs j) p (origins j) xs (descriptors j) hcount)
    (slots j) (bank (putWord source p xs) outputs descriptors p origins)
    (active_bank j _ _ _ _ _)
  apply h.consequence (fun _ hv => hv) _ le_rfl
  rintro v ⟨w,rfl,rfl⟩
  exact replace_bank j _ _ _ _ _ _ _ _ _

def states : ℕ → ℕ
  | 0 => 1
  | n+1 => states n + 16

private def haltProgram (c : ℕ) : Program (TapeCount c) 1 0 :=
  ⟨by dsimp [TapeCount]; omega,0,fun _ _ => none⟩

/-- Compile exactly the first n fixed stages; input sizes do not enter the table. -/
def initialStages (c : ℕ) : (n : ℕ) → n ≤ c → Program (TapeCount c) (states n) 0
  | 0,_ => haltProgram c
  | n+1,hn => seq (initialStages c n (by omega)) (stage ⟨n,by omega⟩)

def program (c : ℕ) : Program (TapeCount c) (states c) 0 := initialStages c c le_rfl

/-- The complete buffer state after the first n fixed pieces. -/
def result {c : ℕ} (Q B : ℕ) (source : ℤ → Fin 4) (outputs : Fin c → ℤ → Fin 4)
    (descriptors : Fin c → List Bool) (p : ℤ) (origins : Fin c → ℤ)
    (input : List (Fin 4)) (n : ℕ) : Tapes (TapeCount c) 0 :=
  bank (putWord source p input)
    (fun j => if j.val < n then putWord (outputs j) (origins j) (piece Q c B input j) else outputs j)
    descriptors (p+offset Q c B n)
    (fun j => if j.val < n then origins j+(piece Q c B input j).length else origins j)

def widthSum {c : ℕ} (descriptors : Fin c → List Bool) (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range n, if hi : i < c then (descriptors ⟨i,hi⟩).length else 0

private theorem result_succ {c Q B : ℕ} (hc : 0 < c)
    (source : ℤ → Fin 4) (outputs : Fin c → ℤ → Fin 4)
    (descriptors : Fin c → List Bool) (p : ℤ) (origins : Fin c → ℤ)
    (input : List (Fin 4)) (hlen : input.length = Q*B) (j : Fin c) :
    bank (putWord source p input)
      (Function.update
        (fun k => if k.val < j.val then putWord (outputs k) (origins k) (piece Q c B input k) else outputs k)
        j (putWord (outputs j) (origins j) (piece Q c B input j)))
      descriptors (p+offset Q c B j.val+(piece Q c B input j).length)
      (Function.update
        (fun k => if k.val < j.val then origins k+(piece Q c B input k).length else origins k)
        j (origins j+(piece Q c B input j).length)) =
    result Q B source outputs descriptors p origins input (j.val+1) := by
  unfold result
  congr 1
  · funext k
    by_cases hk : k = j
    · subst k; simp
    · have hv : k.val ≠ j.val := fun h => hk (Fin.ext h)
      simp only [Function.update_of_ne hk]
      have he : k.val < j.val ↔ k.val < j.val+1 := by omega
      simp only [he]
  · rw [piece_length hc input hlen]
    have hm := offset_mono (Q := Q) (B := B) hc (Nat.le_succ j.val)
    rw [Nat.cast_sub hm]
    ring
  · funext k
    by_cases hk : k = j
    · subst k; simp
    · have hv : k.val ≠ j.val := fun h => hk (Fin.ext h)
      simp only [Function.update_of_ne hk]
      have he : k.val < j.val ↔ k.val < j.val+1 := by omega
      simp only [he]

private theorem result_stage {c Q B : ℕ} (hc : 0 < c)
    (source : ℤ → Fin 4) (outputs : Fin c → ℤ → Fin 4)
    (descriptors : Fin c → List Bool) (p : ℤ) (origins : Fin c → ℤ)
    (input : List (Fin 4)) (hlen : input.length = Q*B) (j : Fin c)
    (hcount : Counter.value (descriptors j) = (piece Q c B input j).length) :
    HoareTime (stage j)
      (fun v => v = result Q B source outputs descriptors p origins input j.val)
      (fun v => v = result Q B source outputs descriptors p origins input (j.val+1))
      (5*(piece Q c B input j).length+7*(descriptors j).length+16) := by
  have h := stage_hoare j (putWord source p input)
    (fun k => if k.val < j.val then putWord (outputs k) (origins k) (piece Q c B input k) else outputs k)
    descriptors (p+offset Q c B j.val)
    (fun k => if k.val < j.val then origins k+(piece Q c B input k).length else origins k)
    (piece Q c B input j) hcount
  rw [source_piece hc source p input hlen j] at h
  simp only [lt_self_iff_false,ite_false] at h
  rw [result_succ hc source outputs descriptors p origins input hlen j] at h
  exact h

/-- Every stage is an actual counted-copy run, with one charged transition at
 each sequential join. The clock and every descriptor are restored each time. -/
theorem initialStages_hoare {c Q B : ℕ} (hc : 0 < c)
    (source : ℤ → Fin 4) (outputs : Fin c → ℤ → Fin 4)
    (descriptors : Fin c → List Bool) (p : ℤ) (origins : Fin c → ℤ)
    (input : List (Fin 4)) (hlen : input.length = Q*B)
    (hcount : ∀ j, Counter.value (descriptors j) = (piece Q c B input j).length)
    (n : ℕ) (hn : n ≤ c) :
    HoareTime (initialStages c n hn)
      (fun v => v = result Q B source outputs descriptors p origins input 0)
      (fun v => v = result Q B source outputs descriptors p origins input n)
      (5*offset Q c B n+7*widthSum descriptors n+17*n) := by
  induction n with
  | zero =>
    intro v hv
    subst v
    refine ⟨0,_,by omega,rfl,?_,rfl⟩
    rfl
  | succ n ih =>
    have hnc : n < c := by omega
    have h := (ih (by omega)).seq
      (result_stage hc source outputs descriptors p origins input hlen ⟨n,hnc⟩ (hcount ⟨n,hnc⟩))
    apply h.consequence (fun _ hv => hv) (fun _ hv => hv) _
    rw [piece_length hc input hlen]
    simp only [widthSum,Finset.sum_range_succ,hnc,dite_true]
    have hm := offset_mono (Q := Q) (B := B) hc (Nat.le_succ n)
    change offset Q c B n ≤ offset Q c B (n+1) at hm
    change 5*offset Q c B n+7*(∑ i ∈ Finset.range n,
      if hi : i < c then (descriptors ⟨i,hi⟩).length else 0)+17*n+1+
      (5*(offset Q c B (n+1)-offset Q c B n)+7*(descriptors ⟨n,hnc⟩).length+16) ≤ _
    omega

/-- Fixed-c literal split of the full input into separate contiguous piece
buffers. Arbitrary source/output origins and all out-of-segment cells persist. -/
theorem split_hoare {c Q B : ℕ} (hc : 0 < c)
    (source : ℤ → Fin 4) (outputs : Fin c → ℤ → Fin 4)
    (descriptors : Fin c → List Bool) (p : ℤ) (origins : Fin c → ℤ)
    (input : List (Fin 4)) (hlen : input.length = Q*B)
    (hcount : ∀ j, Counter.value (descriptors j) = (piece Q c B input j).length) :
    HoareTime (program c)
      (fun v => v = bank (putWord source p input) outputs descriptors p origins)
      (fun v => v = bank (putWord source p input)
        (fun j => putWord (outputs j) (origins j) (piece Q c B input j)) descriptors
        (p+Q*B) (fun j => origins j+(piece Q c B input j).length))
      (5*(Q*B)+7*widthSum descriptors c+17*c) := by
  have h := initialStages_hoare hc source outputs descriptors p origins input hlen hcount c le_rfl
  simpa only [program,result,offset_zero hc,offset_last hc,Nat.not_lt_zero,ite_false,
    Nat.cast_zero,add_zero,Fin.isLt,ite_true,Nat.cast_mul] using h

/-- Canonical descriptors have linear aggregate width, even with empty pieces. -/
theorem widthSum_le {c Q B : ℕ} (hc : 0 < c)
    (descriptors : Fin c → List Bool) (input : List (Fin 4)) (hlen : input.length = Q*B)
    (hcount : ∀ j, Counter.value (descriptors j) = (piece Q c B input j).length)
    (hcanonical : ∀ j, GrowingCounterData.Canonical (descriptors j))
    (n : ℕ) (hn : n ≤ c) : widthSum descriptors n ≤ offset Q c B n+n := by
  induction n with
  | zero => simp [widthSum,offset_zero hc]
  | succ n ih =>
    have hnc : n < c := by omega
    have hi := ih (by omega)
    have hw := GrowingCounterData.canonical_width (descriptors ⟨n,hnc⟩) (hcanonical ⟨n,hnc⟩)
    have hl := Nat.log2_le_self (Counter.value (descriptors ⟨n,hnc⟩))
    rw [hcount ⟨n,hnc⟩,piece_length hc input hlen] at hw hl
    have hm := offset_mono (Q := Q) (B := B) hc (Nat.le_succ n)
    change offset Q c B n ≤ offset Q c B (n+1) at hm
    simp only [widthSum,Finset.sum_range_succ,hnc,dite_true] at *
    omega

/-- A concrete volume-linear split including every subroutine and stage join.
The fixed control depends only on c; Q, B, contents and descriptors are data. -/
theorem split_hoare_linear {c Q B : ℕ} (hc : 0 < c)
    (source : ℤ → Fin 4) (outputs : Fin c → ℤ → Fin 4)
    (descriptors : Fin c → List Bool) (p : ℤ) (origins : Fin c → ℤ)
    (input : List (Fin 4)) (hlen : input.length = Q*B)
    (hcount : ∀ j, Counter.value (descriptors j) = (piece Q c B input j).length)
    (hcanonical : ∀ j, GrowingCounterData.Canonical (descriptors j)) :
    HoareTime (program c)
      (fun v => v = bank (putWord source p input) outputs descriptors p origins)
      (fun v => v = bank (putWord source p input)
        (fun j => putWord (outputs j) (origins j) (piece Q c B input j)) descriptors
        (p+Q*B) (fun j => origins j+(piece Q c B input j).length))
      (12*(Q*B)+24*c) := by
  apply (split_hoare hc source outputs descriptors p origins input hlen hcount).consequence
    (fun _ hv => hv) (fun _ hv => hv)
  have hw := widthSum_le hc descriptors input hlen hcount hcanonical c le_rfl
  rw [offset_last hc] at hw
  omega

/-- Fixed finite-control size, independent of the input dimensions. -/
theorem states_eq (c : ℕ) : states c = 1+16*c := by
  induction c with
  | zero => rfl
  | succ c ih => simp only [states,ih]; omega

end IntegerMultBounds.Machine.ScalingSplit
