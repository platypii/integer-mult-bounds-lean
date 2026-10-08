import IntegerMultBounds.Machine.ScalingSplitRewind
import IntegerMultBounds.Machine.ScratchReset

/-! Literal cleanup of all fixed-coefficient scaling buffers after consumption.
Every stage rewinds, erases its described segment, and rewinds again. Original
blank intervals, arbitrary outside backgrounds, immutable descriptors, shared
work clock and the source tape are retained in the complete-bank contract. -/

namespace IntegerMultBounds.Machine.ScalingBuffersReset

open ScalingSplit

/-- Frame the source while resetting payload, work clock and descriptor. -/
def localProgram : Program 4 50 0 :=
  Placement.placed ScratchReset.program ScalingSplitRewind.localSlots

private theorem local_active (source payload : ℤ → Fin 4) (p q : ℤ) (bs : List Bool) :
    Placement.active ScalingSplitRewind.localSlots
      (CountedCopyReuse.bank source payload CountedCopyReuse.empty
        (CountedCopyReuse.binary bs) p q 1 1) = ScratchReset.bank payload q bs := by
  unfold Placement.active ScalingSplitRewind.localSlots CountedCopyReuse.bank ScratchReset.bank CountedSeek.bank
  congr 1 <;> funext i <;> fin_cases i <;> rfl

private theorem local_replace (source payload payload' : ℤ → Fin 4) (p q r : ℤ) (bs : List Bool) :
    Placement.replace ScalingSplitRewind.localSlots
      (CountedCopyReuse.bank source payload CountedCopyReuse.empty
        (CountedCopyReuse.binary bs) p q 1 1) (ScratchReset.bank payload' r bs) =
      CountedCopyReuse.bank source payload' CountedCopyReuse.empty
        (CountedCopyReuse.binary bs) p r 1 1 := by
  unfold Placement.replace Placement.combine Placement.extra ScalingSplitRewind.localSlots
    Tapes.reindex Tapes.append CountedCopyReuse.bank ScratchReset.bank CountedSeek.bank
  congr 1 <;> funext i <;> fin_cases i <;> rfl

private theorem local_hoare (source background : ℤ → Fin 4) (p q : ℤ)
    (xs : List (Fin 4)) (bs : List Bool) (hcount : Counter.value bs = xs.length)
    (hblank : ∀ z, q ≤ z → z < q+xs.length → background z = blank) :
    HoareTime localProgram
      (fun v => v = CountedCopyReuse.bank source (putWord background q xs) CountedCopyReuse.empty
        (CountedCopyReuse.binary bs) p (q+xs.length) 1 1)
      (fun v => v = CountedCopyReuse.bank source background CountedCopyReuse.empty
        (CountedCopyReuse.binary bs) p q 1 1)
      (17*xs.length+21*bs.length+50) := by
  have h := Placement.hoare_at (ScratchReset.reset_word_hoare background q xs bs hcount hblank)
    ScalingSplitRewind.localSlots
    (CountedCopyReuse.bank source (putWord background q xs) CountedCopyReuse.empty
      (CountedCopyReuse.binary bs) p (q+xs.length) 1 1)
    (local_active _ _ _ _ _)
  apply h.consequence (fun _ hv => hv) _ le_rfl
  rintro v ⟨w,rfl,rfl⟩
  exact local_replace _ _ _ _ _ _ _

def stage {c : ℕ} (j : Fin c) : Program (TapeCount c) 50 0 :=
  Placement.placed (u := c+c) localProgram (slots j)

/-- One selected buffer is restored completely, with all other tapes framed. -/
theorem stage_hoare {c : ℕ} (j : Fin c) (source : ℤ → Fin 4)
    (outputs : Fin c → ℤ → Fin 4) (descriptors : Fin c → List Bool)
    (p : ℤ) (heads : Fin c → ℤ) (background : ℤ → Fin 4) (q : ℤ)
    (xs : List (Fin 4)) (hout : outputs j = putWord background q xs)
    (hhead : heads j = q+xs.length) (hcount : Counter.value (descriptors j) = xs.length)
    (hblank : ∀ z, q ≤ z → z < q+xs.length → background z = blank) :
    HoareTime (stage j)
      (fun v => v = bank source outputs descriptors p heads)
      (fun v => v = bank source (Function.update outputs j background) descriptors p
        (Function.update heads j q))
      (17*xs.length+21*(descriptors j).length+50) := by
  have hp := active_bank j source outputs descriptors p heads
  rw [hout,hhead] at hp
  have h := Placement.hoare_at (local_hoare source background p q xs (descriptors j) hcount hblank)
    (slots j) (bank source outputs descriptors p heads) hp
  apply h.consequence (fun _ hv => hv) _ le_rfl
  rintro v ⟨w,rfl,rfl⟩
  exact replace_bank _ _ _ _ _ _ _ _ _ _

def states : ℕ → ℕ
  | 0 => 1
  | n+1 => states n+50

private def haltProgram (c : ℕ) : Program (TapeCount c) 1 0 :=
  ⟨by dsimp [TapeCount]; omega,0,fun _ _ => none⟩

def initialStages (c : ℕ) : (n : ℕ) → n ≤ c → Program (TapeCount c) (states n) 0
  | 0,_ => haltProgram c
  | n+1,hn => seq (initialStages c n (by omega)) (stage ⟨n,by omega⟩)

def program (c : ℕ) : Program (TapeCount c) (states c) 0 := initialStages c c le_rfl

/-- State after cleaning the first n buffers in fixed order. -/
def result {c : ℕ} (source : ℤ → Fin 4) (backgrounds : Fin c → ℤ → Fin 4)
    (words : Fin c → List (Fin 4)) (descriptors : Fin c → List Bool)
    (p : ℤ) (origins : Fin c → ℤ) (n : ℕ) : Tapes (TapeCount c) 0 :=
  bank source (fun j => if j.val < n then backgrounds j else putWord (backgrounds j) (origins j) (words j))
    descriptors p (fun j => if j.val < n then origins j else origins j+(words j).length)

private theorem result_succ {c : ℕ} (source : ℤ → Fin 4) (backgrounds : Fin c → ℤ → Fin 4)
    (words : Fin c → List (Fin 4)) (descriptors : Fin c → List Bool)
    (p : ℤ) (origins : Fin c → ℤ) (j : Fin c) :
    bank source
      (Function.update
        (fun k => if k.val < j.val then backgrounds k else putWord (backgrounds k) (origins k) (words k))
        j (backgrounds j)) descriptors p
      (Function.update (fun k => if k.val < j.val then origins k else origins k+(words k).length)
        j (origins j)) = result source backgrounds words descriptors p origins (j.val+1) := by
  unfold result
  congr 1
  · funext k
    by_cases hk : k = j
    · subst k; simp
    · have hv : k.val ≠ j.val := fun h => hk (Fin.ext h)
      have he : k.val < j.val ↔ k.val < j.val+1 := by omega
      simp only [Function.update_of_ne hk,he]
  · funext k
    by_cases hk : k = j
    · subst k; simp
    · have hv : k.val ≠ j.val := fun h => hk (Fin.ext h)
      have he : k.val < j.val ↔ k.val < j.val+1 := by omega
      simp only [Function.update_of_ne hk,he]

private theorem result_stage {c : ℕ} (source : ℤ → Fin 4) (backgrounds : Fin c → ℤ → Fin 4)
    (words : Fin c → List (Fin 4)) (descriptors : Fin c → List Bool)
    (p : ℤ) (origins : Fin c → ℤ) (j : Fin c)
    (hcount : Counter.value (descriptors j) = (words j).length)
    (hblank : ∀ z, origins j ≤ z → z < origins j+(words j).length → backgrounds j z = blank) :
    HoareTime (stage j)
      (fun v => v = result source backgrounds words descriptors p origins j.val)
      (fun v => v = result source backgrounds words descriptors p origins (j.val+1))
      (17*(words j).length+21*(descriptors j).length+50) := by
  have h := stage_hoare j source
    (fun k => if k.val < j.val then backgrounds k else putWord (backgrounds k) (origins k) (words k))
    descriptors p (fun k => if k.val < j.val then origins k else origins k+(words k).length)
    (backgrounds j) (origins j) (words j) (by simp) (by simp) hcount hblank
  rw [result_succ] at h
  exact h

/-- Literal sequential execution, including every joining transition. -/
theorem initialStages_hoare {c : ℕ} (source : ℤ → Fin 4) (backgrounds : Fin c → ℤ → Fin 4)
    (words : Fin c → List (Fin 4)) (descriptors : Fin c → List Bool)
    (p : ℤ) (origins : Fin c → ℤ)
    (hcount : ∀ j, Counter.value (descriptors j) = (words j).length)
    (hblank : ∀ j z, origins j ≤ z → z < origins j+(words j).length → backgrounds j z = blank)
    (n : ℕ) (hn : n ≤ c) :
    HoareTime (initialStages c n hn)
      (fun v => v = result source backgrounds words descriptors p origins 0)
      (fun v => v = result source backgrounds words descriptors p origins n)
      (17*ScalingSplitRewind.volumeSum descriptors n+21*widthSum descriptors n+51*n) := by
  induction n with
  | zero =>
    rintro v rfl
    exact ⟨0,_,by omega,rfl,rfl,rfl⟩
  | succ n ih =>
    have hnc : n < c := by omega
    have h := (ih (by omega)).seq
      (result_stage source backgrounds words descriptors p origins ⟨n,hnc⟩ (hcount ⟨n,hnc⟩) (hblank ⟨n,hnc⟩))
    apply h.consequence (fun _ hv => hv) (fun _ hv => hv) _
    simp only [ScalingSplitRewind.volumeSum,widthSum,Finset.sum_range_succ,hnc,dite_true,hcount]
    omega

/-- Restore all original buffer backgrounds and heads after full consumption. -/
theorem reset_hoare {c : ℕ} (source : ℤ → Fin 4) (backgrounds : Fin c → ℤ → Fin 4)
    (words : Fin c → List (Fin 4)) (descriptors : Fin c → List Bool)
    (p : ℤ) (origins : Fin c → ℤ)
    (hcount : ∀ j, Counter.value (descriptors j) = (words j).length)
    (hblank : ∀ j z, origins j ≤ z → z < origins j+(words j).length → backgrounds j z = blank) :
    HoareTime (program c)
      (fun v => v = bank source (fun j => putWord (backgrounds j) (origins j) (words j)) descriptors p
        (fun j => origins j+(words j).length))
      (fun v => v = bank source backgrounds descriptors p origins)
      (17*ScalingSplitRewind.volumeSum descriptors c+21*widthSum descriptors c+51*c) := by
  have h := initialStages_hoare source backgrounds words descriptors p origins hcount hblank c le_rfl
  simpa only [program,result,Nat.not_lt_zero,ite_false,Fin.isLt,ite_true] using h

/-- Scaling-piece specialization with physical volume Q*B. -/
theorem reset_pieces_hoare {c Q B : ℕ} (hc : 0 < c)
    (source : ℤ → Fin 4) (backgrounds : Fin c → ℤ → Fin 4)
    (descriptors : Fin c → List Bool) (p : ℤ) (origins : Fin c → ℤ)
    (input : List (Fin 4)) (hlen : input.length = Q*B)
    (hcount : ∀ j, Counter.value (descriptors j) = (piece Q c B input j).length)
    (hblank : ∀ j z, origins j ≤ z → z < origins j+(piece Q c B input j).length → backgrounds j z = blank) :
    HoareTime (program c)
      (fun v => v = bank source (fun j => putWord (backgrounds j) (origins j) (piece Q c B input j)) descriptors p
        (fun j => origins j+(piece Q c B input j).length))
      (fun v => v = bank source backgrounds descriptors p origins)
      (17*(Q*B)+21*widthSum descriptors c+51*c) := by
  have h := reset_hoare source backgrounds (piece Q c B input) descriptors p origins hcount hblank
  rw [ScalingSplitRewind.volumeSum_eq hc descriptors input hlen hcount c le_rfl,offset_last hc] at h
  exact h

theorem reset_pieces_hoare_linear {c Q B : ℕ} (hc : 0 < c)
    (source : ℤ → Fin 4) (backgrounds : Fin c → ℤ → Fin 4)
    (descriptors : Fin c → List Bool) (p : ℤ) (origins : Fin c → ℤ)
    (input : List (Fin 4)) (hlen : input.length = Q*B)
    (hcount : ∀ j, Counter.value (descriptors j) = (piece Q c B input j).length)
    (hblank : ∀ j z, origins j ≤ z → z < origins j+(piece Q c B input j).length → backgrounds j z = blank)
    (hcanonical : ∀ j, GrowingCounterData.Canonical (descriptors j)) :
    HoareTime (program c)
      (fun v => v = bank source (fun j => putWord (backgrounds j) (origins j) (piece Q c B input j)) descriptors p
        (fun j => origins j+(piece Q c B input j).length))
      (fun v => v = bank source backgrounds descriptors p origins)
      (38*(Q*B)+72*c) := by
  apply (reset_pieces_hoare hc source backgrounds descriptors p origins input hlen hcount hblank).consequence
    (fun _ hv => hv) (fun _ hv => hv)
  have hw := widthSum_le hc descriptors input hlen hcount hcanonical c le_rfl
  rw [offset_last hc] at hw
  omega

theorem states_eq (c : ℕ) : states c = 1+50*c := by
  induction c with
  | zero => rfl
  | succ c ih => simp only [states,ih]; omega

end IntegerMultBounds.Machine.ScalingBuffersReset
