import IntegerMultBounds.Machine.ScalingSplit
import IntegerMultBounds.Machine.CountedSeek

/-! Literal return of every scaling-piece buffer head to its origin. The fixed
sequence of backward counted seeks preserves all payload cells, source head,
descriptors and reusable clock. This connects the split's end-position buffers
to a merge consuming each piece from its beginning. -/

namespace IntegerMultBounds.Machine.ScalingSplitRewind

open ScalingSplit

/-- Reserve local tape zero for the framed source; seek on tapes one to three. -/
def localSlots : Fin (3+1) ≃ Fin 4 where
  toFun := fun i => if i = 0 then 1 else if i = 1 then 2 else if i = 2 then 3 else 0
  invFun := fun i => if i = 0 then 3 else if i = 1 then 0 else if i = 2 then 1 else 2
  left_inv := by intro i; fin_cases i <;> decide
  right_inv := by intro i; fin_cases i <;> decide

def localProgram : Program 4 16 0 :=
  Placement.placed CountedSeek.backwardProgram localSlots

private theorem local_active (source payload : ℤ → Fin 4) (p q : ℤ) (bs : List Bool) :
    Placement.active localSlots
      (CountedCopyReuse.bank source payload CountedCopyReuse.empty
        (CountedCopyReuse.binary bs) p q 1 1) = CountedSeek.bank payload q bs := by
  unfold Placement.active localSlots CountedCopyReuse.bank CountedSeek.bank
  congr 1 <;> funext i <;> fin_cases i <;> rfl

private theorem local_replace (source payload : ℤ → Fin 4) (p q r : ℤ) (bs : List Bool) :
    Placement.replace localSlots
      (CountedCopyReuse.bank source payload CountedCopyReuse.empty
        (CountedCopyReuse.binary bs) p q 1 1) (CountedSeek.bank payload r bs) =
      CountedCopyReuse.bank source payload CountedCopyReuse.empty
        (CountedCopyReuse.binary bs) p r 1 1 := by
  unfold Placement.replace Placement.combine Placement.extra localSlots Tapes.reindex Tapes.append
    CountedCopyReuse.bank CountedSeek.bank
  congr 1 <;> funext i <;> fin_cases i <;> rfl

private theorem local_hoare (source payload : ℤ → Fin 4) (p q : ℤ) (bs : List Bool) :
    HoareTime localProgram
      (fun v => v = CountedCopyReuse.bank source payload CountedCopyReuse.empty
        (CountedCopyReuse.binary bs) p q 1 1)
      (fun v => v = CountedCopyReuse.bank source payload CountedCopyReuse.empty
        (CountedCopyReuse.binary bs) p (q-Counter.value bs) 1 1)
      (5*Counter.value bs+7*bs.length+16) := by
  have h := Placement.hoare_at (CountedSeek.seek_backward_hoare payload q bs) localSlots
    (CountedCopyReuse.bank source payload CountedCopyReuse.empty (CountedCopyReuse.binary bs) p q 1 1)
    (local_active source payload p q bs)
  apply h.consequence (fun _ hv => hv) _ le_rfl
  rintro v ⟨w,rfl,rfl⟩
  exact local_replace source payload p q _ bs

def stage {c : ℕ} (j : Fin c) : Program (TapeCount c) 16 0 :=
  Placement.placed (u := c+c) localProgram (slots j)

theorem stage_hoare {c : ℕ} (j : Fin c) (source : ℤ → Fin 4)
    (outputs : Fin c → ℤ → Fin 4) (descriptors : Fin c → List Bool)
    (p : ℤ) (heads : Fin c → ℤ) :
    HoareTime (stage j)
      (fun v => v = bank source outputs descriptors p heads)
      (fun v => v = bank source outputs descriptors p
        (Function.update heads j (heads j-Counter.value (descriptors j))))
      (5*Counter.value (descriptors j)+7*(descriptors j).length+16) := by
  have h := Placement.hoare_at (local_hoare source (outputs j) p (heads j) (descriptors j))
    (slots j) (bank source outputs descriptors p heads) (active_bank j _ _ _ _ _)
  apply h.consequence (fun _ hv => hv) _ le_rfl
  rintro v ⟨w,rfl,rfl⟩
  rw [replace_bank,Function.update_eq_self]

private def haltProgram (c : ℕ) : Program (TapeCount c) 1 0 :=
  ⟨by dsimp [TapeCount]; omega,0,fun _ _ => none⟩

def initialStages (c : ℕ) : (n : ℕ) → n ≤ c → Program (TapeCount c) (states n) 0
  | 0,_ => haltProgram c
  | n+1,hn => seq (initialStages c n (by omega)) (stage ⟨n,by omega⟩)

def program (c : ℕ) : Program (TapeCount c) (states c) 0 := initialStages c c le_rfl

def headsAfter {c : ℕ} (heads : Fin c → ℤ) (descriptors : Fin c → List Bool)
    (n : ℕ) (j : Fin c) : ℤ :=
  heads j - if j.val < n then (Counter.value (descriptors j) : ℤ) else 0

def volumeSum {c : ℕ} (descriptors : Fin c → List Bool) (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range n, if hi : i < c then Counter.value (descriptors ⟨i,hi⟩) else 0

private theorem headsAfter_succ {c : ℕ} (heads : Fin c → ℤ) (descriptors : Fin c → List Bool)
    (j : Fin c) :
    Function.update (headsAfter heads descriptors j.val) j
      (headsAfter heads descriptors j.val j-Counter.value (descriptors j)) =
      headsAfter heads descriptors (j.val+1) := by
  funext k
  by_cases hk : k = j
  · subst k; simp [headsAfter]
  · have hv : k.val ≠ j.val := fun h => hk (Fin.ext h)
    have he : k.val < j.val ↔ k.val < j.val+1 := by omega
    simp only [Function.update_of_ne hk,headsAfter,he]

theorem initialStages_hoare {c : ℕ} (source : ℤ → Fin 4)
    (outputs : Fin c → ℤ → Fin 4) (descriptors : Fin c → List Bool)
    (p : ℤ) (heads : Fin c → ℤ) (n : ℕ) (hn : n ≤ c) :
    HoareTime (initialStages c n hn)
      (fun v => v = bank source outputs descriptors p heads)
      (fun v => v = bank source outputs descriptors p (headsAfter heads descriptors n))
      (5*volumeSum descriptors n+7*widthSum descriptors n+17*n) := by
  induction n with
  | zero =>
    rintro v rfl
    refine ⟨0,_,by omega,rfl,rfl,?_⟩
    have hz : headsAfter heads descriptors 0 = heads := by
      funext j; simp [headsAfter]
    rw [hz]
    rfl
  | succ n ih =>
    have hnc : n < c := by omega
    have h := (ih (by omega)).seq
      (stage_hoare ⟨n,hnc⟩ source outputs descriptors p (headsAfter heads descriptors n))
    rw [headsAfter_succ heads descriptors ⟨n,hnc⟩] at h
    apply h.consequence (fun _ hv => hv) (fun _ hv => hv) _
    simp only [volumeSum,widthSum,Finset.sum_range_succ,hnc,dite_true]
    omega

/-- Return every supplied descriptor displacement, preserving all tape cells. -/
theorem rewind_hoare {c : ℕ} (source : ℤ → Fin 4)
    (outputs : Fin c → ℤ → Fin 4) (descriptors : Fin c → List Bool)
    (p : ℤ) (origins : Fin c → ℤ) :
    HoareTime (program c)
      (fun v => v = bank source outputs descriptors p
        (fun j => origins j+Counter.value (descriptors j)))
      (fun v => v = bank source outputs descriptors p origins)
      (5*volumeSum descriptors c+7*widthSum descriptors c+17*c) := by
  have h := initialStages_hoare source outputs descriptors p
    (fun j => origins j+Counter.value (descriptors j)) c le_rfl
  have he : headsAfter (fun j => origins j+Counter.value (descriptors j)) descriptors c = origins := by
    funext j; simp [headsAfter]
  rw [he] at h
  exact h

/-- Supplied piece counts telescope to the actual physical prefix length. -/
theorem volumeSum_eq {c Q B : ℕ} (hc : 0 < c)
    (descriptors : Fin c → List Bool) (input : List (Fin 4)) (hlen : input.length = Q*B)
    (hcount : ∀ j, Counter.value (descriptors j) = (piece Q c B input j).length)
    (n : ℕ) (hn : n ≤ c) : volumeSum descriptors n = offset Q c B n := by
  induction n with
  | zero => simp [volumeSum,offset_zero hc]
  | succ n ih =>
    have hnc : n < c := by omega
    have hi := ih (by omega)
    have hm := offset_mono (Q := Q) (B := B) hc (Nat.le_succ n)
    change offset Q c B n ≤ offset Q c B (n+1) at hm
    simp only [volumeSum,Finset.sum_range_succ,hnc,dite_true] at hi ⊢
    rw [hi,hcount ⟨n,hnc⟩,piece_length hc input hlen]
    exact Nat.add_sub_of_le hm

/-- Copy all pieces, then return their heads to the merge-ready origins. -/
def splitAndRewindProgram (c : ℕ) : Program (TapeCount c) (states c+states c) 0 :=
  seq (ScalingSplit.program c) (program c)

/-- Complete literal split-and-return contract with explicit descriptor widths. -/
theorem splitAndRewind_hoare {c Q B : ℕ} (hc : 0 < c)
    (source : ℤ → Fin 4) (outputs : Fin c → ℤ → Fin 4)
    (descriptors : Fin c → List Bool) (p : ℤ) (origins : Fin c → ℤ)
    (input : List (Fin 4)) (hlen : input.length = Q*B)
    (hcount : ∀ j, Counter.value (descriptors j) = (piece Q c B input j).length) :
    HoareTime (splitAndRewindProgram c)
      (fun v => v = bank (putWord source p input) outputs descriptors p origins)
      (fun v => v = bank (putWord source p input)
        (fun j => putWord (outputs j) (origins j) (piece Q c B input j)) descriptors
        (p+Q*B) origins)
      (10*(Q*B)+14*widthSum descriptors c+34*c+1) := by
  have hr := rewind_hoare (putWord source p input)
    (fun j => putWord (outputs j) (origins j) (piece Q c B input j)) descriptors
    (p+Q*B) origins
  simp only [hcount] at hr
  have h := (ScalingSplit.split_hoare hc source outputs descriptors p origins input hlen hcount).seq hr
  apply h.consequence (fun _ hv => hv) (fun _ hv => hv) _
  rw [volumeSum_eq hc descriptors input hlen hcount c le_rfl,offset_last hc]
  omega

/-- All split and rewind work is linear in payload volume plus the fixed
coefficient, with no nonempty-piece or coprimality assumption. -/
theorem splitAndRewind_hoare_linear {c Q B : ℕ} (hc : 0 < c)
    (source : ℤ → Fin 4) (outputs : Fin c → ℤ → Fin 4)
    (descriptors : Fin c → List Bool) (p : ℤ) (origins : Fin c → ℤ)
    (input : List (Fin 4)) (hlen : input.length = Q*B)
    (hcount : ∀ j, Counter.value (descriptors j) = (piece Q c B input j).length)
    (hcanonical : ∀ j, GrowingCounterData.Canonical (descriptors j)) :
    HoareTime (splitAndRewindProgram c)
      (fun v => v = bank (putWord source p input) outputs descriptors p origins)
      (fun v => v = bank (putWord source p input)
        (fun j => putWord (outputs j) (origins j) (piece Q c B input j)) descriptors
        (p+Q*B) origins)
      (24*(Q*B)+48*c+1) := by
  apply (splitAndRewind_hoare hc source outputs descriptors p origins input hlen hcount).consequence
    (fun _ hv => hv) (fun _ hv => hv)
  have hw := widthSum_le hc descriptors input hlen hcount hcanonical c le_rfl
  rw [offset_last hc] at hw
  omega

end IntegerMultBounds.Machine.ScalingSplitRewind
