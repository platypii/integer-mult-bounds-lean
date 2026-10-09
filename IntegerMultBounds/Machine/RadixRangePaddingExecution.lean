import IntegerMultBounds.Machine.RowCropAny
import IntegerMultBounds.Machine.RangePaddingDimensions
import IntegerMultBounds.Machine.RadixRangePadding

/-! Paid rectangular range padding and cropping from the five immutable
canonical dimensions. Group prefix/suffix dimensions are synthesized on tape;
every scan, rewind, generated descriptor and cleanup is charged. -/
namespace IntegerMultBounds.Machine.RadixRangePaddingExecution
noncomputable section
open RangePaddingDimensions (bank input ready words values)

def dForward : Fin (12+5) ≃ Fin 17 where
  toFun := fun i => match i.val with
    | 0 => 0 | 1 => 1 | 2 => 8 | 3 => 3 | 4 => 6 | 5 => 5 | 6 => 11 | 7 => 12 | 8 => 13 | 9 => 14 | 10 => 15 | 11 => 16 | 12 => 2 | 13 => 4 | 14 => 7 | 15 => 9 | _ => 10
  invFun := fun i => match i.val with
    | 0 => 0 | 1 => 1 | 2 => 12 | 3 => 3 | 4 => 13 | 5 => 5 | 6 => 4 | 7 => 14 | 8 => 2 | 9 => 15 | 10 => 16 | 11 => 6 | 12 => 7 | 13 => 8 | 14 => 9 | 15 => 10 | _ => 11
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def hReverse : Fin (12+5) ≃ Fin 17 where
  toFun := fun i => match i.val with
    | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 6 | 5 => 10 | 6 => 11 | 7 => 12 | 8 => 13 | 9 => 14 | 10 => 15 | 11 => 16 | 12 => 4 | 13 => 5 | 14 => 7 | 15 => 8 | _ => 9
  invFun := fun i => match i.val with
    | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 12 | 5 => 13 | 6 => 4 | 7 => 14 | 8 => 15 | 9 => 16 | 10 => 5 | 11 => 6 | 12 => 7 | 13 => 8 | 14 => 9 | 15 => 10 | _ => 11
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def hForward : Fin (12+5) ≃ Fin 17 where
  toFun := fun i => match i.val with
    | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 6 | 5 => 10 | 6 => 11 | 7 => 12 | 8 => 13 | 9 => 14 | 10 => 15 | 11 => 16 | 12 => 4 | 13 => 5 | 14 => 7 | 15 => 8 | _ => 9
  invFun := fun i => match i.val with
    | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 12 | 5 => 13 | 6 => 4 | 7 => 14 | 8 => 15 | 9 => 16 | 10 => 5 | 11 => 6 | 12 => 7 | 13 => 8 | 14 => 9 | 15 => 10 | _ => 11
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def dReverse : Fin (12+5) ≃ Fin 17 where
  toFun := fun i => match i.val with
    | 0 => 1 | 1 => 0 | 2 => 8 | 3 => 3 | 4 => 6 | 5 => 5 | 6 => 11 | 7 => 12 | 8 => 13 | 9 => 14 | 10 => 15 | 11 => 16 | 12 => 2 | 13 => 4 | 14 => 7 | 15 => 9 | _ => 10
  invFun := fun i => match i.val with
    | 0 => 1 | 1 => 0 | 2 => 12 | 3 => 3 | 4 => 13 | 5 => 5 | 6 => 4 | 7 => 14 | 8 => 2 | 9 => 15 | 10 => 16 | 11 => 6 | 12 => 7 | 13 => 8 | 14 => 9 | 15 => 10 | _ => 11
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def prepared (source dest : ℤ → Fin 4) (hs : Fin 5 → List Bool) (xs : Fin 4 → List Bool) :=
  bank source dest hs (fun i => some (xs i))

theorem dForward_active (source dest : ℤ → Fin 4) (hs : Fin 5 → List Bool) (xs : Fin 4 → List Bool) :
    Placement.active dForward (prepared source dest hs xs) =
      RowPaddingConstructed.bank source dest 0 0 (xs 1) (hs 1) (hs 4) (hs 3) none none := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem dForward_extra (source dest source' dest' : ℤ → Fin 4) (hs : Fin 5 → List Bool) (xs : Fin 4 → List Bool) :
    Placement.extra dForward (prepared source dest hs xs) =
      Placement.extra dForward (prepared source' dest' hs xs) := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem hReverse_active (source dest : ℤ → Fin 4) (hs : Fin 5 → List Bool) (xs : Fin 4 → List Bool) :
    Placement.active hReverse (prepared source dest hs xs) =
      RowPaddingConstructed.bank dest source 0 0 (hs 0) (hs 1) (hs 4) (xs 3) none none := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem hReverse_extra (source dest source' dest' : ℤ → Fin 4) (hs : Fin 5 → List Bool) (xs : Fin 4 → List Bool) :
    Placement.extra hReverse (prepared source dest hs xs) =
      Placement.extra hReverse (prepared source' dest' hs xs) := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem hForward_active (source dest : ℤ → Fin 4) (hs : Fin 5 → List Bool) (xs : Fin 4 → List Bool) :
    Placement.active hForward (prepared source dest hs xs) =
      RowPaddingConstructed.bank source dest 0 0 (hs 0) (hs 1) (hs 4) (xs 3) none none := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem hForward_extra (source dest source' dest' : ℤ → Fin 4) (hs : Fin 5 → List Bool) (xs : Fin 4 → List Bool) :
    Placement.extra hForward (prepared source dest hs xs) =
      Placement.extra hForward (prepared source' dest' hs xs) := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem dReverse_active (source dest : ℤ → Fin 4) (hs : Fin 5 → List Bool) (xs : Fin 4 → List Bool) :
    Placement.active dReverse (prepared source dest hs xs) =
      RowPaddingConstructed.bank dest source 0 0 (xs 1) (hs 1) (hs 4) (hs 3) none none := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem dReverse_extra (source dest source' dest' : ℤ → Fin 4) (hs : Fin 5 → List Bool) (xs : Fin 4 → List Bool) :
    Placement.extra dReverse (prepared source dest hs xs) =
      Placement.extra dReverse (prepared source' dest' hs xs) := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

private theorem placed_exact {s u t r cost : ℕ} {M : Program s r 0}
    (e : Fin (s+u) ≃ Fin t) (v w : Tapes t 0) (small small' : Tapes s 0)
    (ha : Placement.active e v = small) (hf : Placement.active e w = small')
    (he : Placement.extra e v = Placement.extra e w)
    (hh : HoareTime M (fun x => x = small) (fun x => x = small') cost) :
    HoareTime (Placement.placed M e) (fun x => x = v) (fun x => x = w) cost := by
  apply (Placement.hoare_at hh e v ha).consequence (fun _ h => h) _ le_rfl
  rintro x ⟨y,rfl,rfl⟩
  rw [Placement.replace,he,← hf]
  exact Placement.view _ _

def empty : ℤ → Fin 4 := fun _ => blank
def word {n : ℕ} (x : Fin n → Fin 4) := putWord empty 0 (List.ofFn x)

theorem word_eq {n : ℕ} (x : Fin n → Fin 4) : word x = putWord empty 0 (List.ofFn x) := rfl

theorem erased {n : ℕ} (x : Fin n → Fin 4) : CountedRawFill.filled (word x) 0 n blank = empty := by
  have h := CountedRawFill.erased_word empty 0 (List.ofFn x) (by intro z _ _; rfl)
  simpa only [word,List.length_ofFn] using h

theorem ofFn_cast {α : Type*} {n m : ℕ} (h : n=m) (f : Fin m → α) :
    List.ofFn (fun z : Fin n => f (Fin.cast h z)) = List.ofFn f := by subst m; rfl

def padDProgram : Program 17 215 0 := Placement.placed RowPaddingConstructed.program dForward
def padHProgram : Program 17 215 0 := Placement.placed RowPaddingConstructed.program hReverse
def cropHProgram : Program 17 215 0 := Placement.placed RowPaddingConstructed.cropProgram hForward
def cropDProgram : Program 17 215 0 := Placement.placed RowPaddingConstructed.cropProgram dReverse

def padD (P N G B M : ℕ) (x : Fin (RadixRangePadding.volume P N G B) → Fin 4) :
    Fin (P*N*G*M*B) → Fin 4 := RecursiveRowPadding.pad M (bitSymbol false) x

def groupD (P N G B M : ℕ) (x : Fin (RadixRangePadding.volume P N G B) → Fin 4) :
    Fin (P*N*(G*M*B)) → Fin 4 := fun z => padD P N G B M x (Fin.cast (RadixRangePadding.regroup P N G M B) z)

def padH (P N G B M : ℕ) (x : Fin (RadixRangePadding.volume P N G B) → Fin 4) :
    Fin (P*M*(G*M*B)) → Fin 4 := RecursiveRowPadding.pad M (bitSymbol false) (groupD P N G B M x)

theorem groupD_word (P N G B M : ℕ) (x : Fin (RadixRangePadding.volume P N G B) → Fin 4) :
    word (groupD P N G B M x) = word (padD P N G B M x) := by
  unfold word groupD
  rw [ofFn_cast]

theorem padH_word (P N G B M : ℕ) (x : Fin (RadixRangePadding.volume P N G B) → Fin 4) :
    word (padH P N G B M x) = word (RadixRangePadding.pad M (bitSymbol false) x) := by
  unfold word
  change putWord empty 0 (List.ofFn (padH P N G B M x)) =
    putWord empty 0 (List.ofFn (fun z => padH P N G B M x (Fin.cast (RadixRangePadding.regroup P M G M B).symm z)))
  rw [ofFn_cast]

def groupCrop (P G B M : ℕ) (x : Fin (RadixRangePadding.volume P M G B) → Fin 4) :
    Fin (P*M*(G*M*B)) → Fin 4 := fun z => x (Fin.cast (RadixRangePadding.regroup P M G M B) z)

def cropH (P N G B M : ℕ) (hNM : N ≤ M) (x : Fin (RadixRangePadding.volume P M G B) → Fin 4) :
    Fin (P*N*G*M*B) → Fin 4 := fun z =>
  RecursiveRowPadding.crop hNM (groupCrop P G B M x) (Fin.cast (RadixRangePadding.regroup P N G M B).symm z)

theorem groupCrop_word (P G B M : ℕ) (x : Fin (RadixRangePadding.volume P M G B) → Fin 4) :
    word (groupCrop P G B M x) = word x := by
  exact congrArg (putWord empty 0) (ofFn_cast
    (show P*M*(G*M*B) = RadixRangePadding.volume P M G B from RadixRangePadding.regroup P M G M B) x)

theorem cropH_word (P N G B M : ℕ) (hNM : N ≤ M) (x : Fin (RadixRangePadding.volume P M G B) → Fin 4) :
    word (cropH P N G B M hNM x) = word (RecursiveRowPadding.crop hNM (groupCrop P G B M x)) := by
  unfold word cropH
  rw [ofFn_cast]

theorem cropStages_word (P N G B M : ℕ) (hNM : N ≤ M) (x : Fin (RadixRangePadding.volume P M G B) → Fin 4) :
    word (RecursiveRowPadding.crop (A := P*N*G) (L := B) hNM (cropH P N G B M hNM x)) =
      word (RadixRangePadding.cropStages hNM x) := rfl

theorem padD_hoare (hs : Fin 5 → List Bool) (P N G B M : ℕ)
    (hv : ∀ i, Counter.value (hs i) = values P N G B M i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i))
    (hP : 0 < P) (hN : 0 < N) (hG : 0 < G) (hB : 0 < B) (hNM : N ≤ M)
    (x : Fin (RadixRangePadding.volume P N G B) → Fin 4) :
    HoareTime padDProgram (fun v => v = ready (word x) empty hs P N G B M)
      (fun v => v = ready empty (word (padD P N G B M x)) hs P N G B M) (413*(P*N*G)*(M*B)) := by
  change Fin (P*N*G*N*B) → Fin 4 at x
  have vp := RangePaddingDimensions.words_value P N G B M
  have hrow := RowPaddingConstructed.pad_array_hoare empty empty 0 0
    (words P N G B M 1) (hs 1) (hs 4) (hs 3) (P*N*G) N M (B) (x)
    (vp.2.1) (hv 1) (hv 4) (hv 3) (RangePaddingDimensions.words_canonical P N G B M 1) (hc 1) (hc 4) (hc 3)
    (Nat.mul_pos (Nat.mul_pos hP hN) hG) hN hNM (hB)
  have he : CountedRawFill.filled (putWord empty 0 (List.ofFn x)) 0 (P*N*G*N*B) blank = empty := erased x
  rw [he] at hrow
  simp only [← word_eq] at hrow
  apply placed_exact dForward _ _ _ _ _ _ _ hrow
  · exact dForward_active _ _ _ _
  · exact dForward_active _ _ _ _
  · exact dForward_extra _ _ _ _ _ _

theorem padH_hoare (hs : Fin 5 → List Bool) (P N G B M : ℕ)
    (hv : ∀ i, Counter.value (hs i) = values P N G B M i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i))
    (hP : 0 < P) (hN : 0 < N) (hG : 0 < G) (hB : 0 < B) (hNM : N ≤ M)
    (x : Fin (RadixRangePadding.volume P N G B) → Fin 4) :
    HoareTime padHProgram (fun v => v = ready empty (word (padD P N G B M x)) hs P N G B M)
      (fun v => v = ready (word (RadixRangePadding.pad M (bitSymbol false) x)) empty hs P N G B M) (413*P*(M*(G*M*B))) := by
  have vp := RangePaddingDimensions.words_value P N G B M
  have hrow := RowPaddingConstructed.pad_array_hoare empty empty 0 0
    (hs 0) (hs 1) (hs 4) (words P N G B M 3) (P) N M (G*M*B) (groupD P N G B M x)
    (hv 0) (hv 1) (hv 4) (vp.2.2.2) (hc 0) (hc 1) (hc 4) (RangePaddingDimensions.words_canonical P N G B M 3)
    (hP) hN hNM (Nat.mul_pos (Nat.mul_pos hG (lt_of_lt_of_le hN hNM)) hB)
  simp only [← word_eq,erased] at hrow
  rw [groupD_word] at hrow
  have hw : word (RecursiveRowPadding.pad M (bitSymbol false) (groupD P N G B M x)) =
      word (RadixRangePadding.pad M (bitSymbol false) x) := padH_word P N G B M x
  rw [hw] at hrow
  apply placed_exact hReverse _ _ _ _ _ _ _ hrow
  · exact hReverse_active _ _ _ _
  · exact hReverse_active _ _ _ _
  · exact hReverse_extra _ _ _ _ _ _

theorem cropH_hoare (hs : Fin 5 → List Bool) (P N G B M : ℕ)
    (hv : ∀ i, Counter.value (hs i) = values P N G B M i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i))
    (hP : 0 < P) (hN : 0 < N) (hG : 0 < G) (hB : 0 < B) (hNM : N ≤ M)
    (x : Fin (RadixRangePadding.volume P M G B) → Fin 4) :
    HoareTime cropHProgram (fun v => v = ready (word x) empty hs P N G B M)
      (fun v => v = ready empty (word (cropH P N G B M hNM x)) hs P N G B M) (413*P*(M*(G*M*B))) := by
  have vp := RangePaddingDimensions.words_value P N G B M
  have hrow := RowCropAny.constructed_array_hoare empty empty 0 0
    (hs 0) (hs 1) (hs 4) (words P N G B M 3) (P) N M (G*M*B) (groupCrop P G B M x)
    (hv 0) (hv 1) (hv 4) (vp.2.2.2) (hc 0) (hc 1) (hc 4) (RangePaddingDimensions.words_canonical P N G B M 3)
    (hP) hN hNM (Nat.mul_pos (Nat.mul_pos hG (lt_of_lt_of_le hN hNM)) hB)
  simp only [← word_eq,erased] at hrow
  rw [groupCrop_word,← cropH_word] at hrow
  apply placed_exact hForward _ _ _ _ _ _ _ hrow
  · exact hForward_active _ _ _ _
  · exact hForward_active _ _ _ _
  · exact hForward_extra _ _ _ _ _ _

theorem cropD_hoare (hs : Fin 5 → List Bool) (P N G B M : ℕ)
    (hv : ∀ i, Counter.value (hs i) = values P N G B M i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i))
    (hP : 0 < P) (hN : 0 < N) (hG : 0 < G) (hB : 0 < B) (hNM : N ≤ M)
    (x : Fin (RadixRangePadding.volume P M G B) → Fin 4) :
    HoareTime cropDProgram (fun v => v = ready empty (word (cropH P N G B M hNM x)) hs P N G B M)
      (fun v => v = ready (word (RadixRangePadding.cropStages hNM x)) empty hs P N G B M) (413*(P*N*G)*(M*B)) := by
  have vp := RangePaddingDimensions.words_value P N G B M
  have hrow := RowCropAny.constructed_array_hoare empty empty 0 0
    (words P N G B M 1) (hs 1) (hs 4) (hs 3) (P*N*G) N M (B) (cropH P N G B M hNM x)
    (vp.2.1) (hv 1) (hv 4) (hv 3) (RangePaddingDimensions.words_canonical P N G B M 1) (hc 1) (hc 4) (hc 3)
    (Nat.mul_pos (Nat.mul_pos hP hN) hG) hN hNM (hB)
  simp only [← word_eq,erased] at hrow
  rw [cropStages_word] at hrow
  apply placed_exact dReverse _ _ _ _ _ _ _ hrow
  · exact dReverse_active _ _ _ _
  · exact dReverse_active _ _ _ _
  · exact dReverse_extra _ _ _ _ _ _


def padProgram : Program 17 (160+((215+215)+17)) 0 :=
  seq RangePaddingDimensions.program (seq (seq padDProgram padHProgram) RangePaddingDimensions.cleanupProgram)

def cropProgram : Program 17 (160+((215+215)+17)) 0 :=
  seq RangePaddingDimensions.program (seq (seq cropHProgram cropDProgram) RangePaddingDimensions.cleanupProgram)

theorem budget (P N G B M : ℕ) (hP : 0 < P) (hG : 0 < G) (hB : 0 < B)
    (hM : 0 < M) (hNM : N ≤ M) :
    330*RangePaddingDimensions.volume P G B M+1+
      (413*(P*N*G)*(M*B)+1+413*P*(M*(G*M*B))+1+
        40*RangePaddingDimensions.volume P G B M) ≤ 1200*RadixRangePadding.volume P M G B := by
  have hs := RangePaddingDimensions.volume_le_padded P G B M hM
  have hp := RangePaddingDimensions.volume_positive P G B M hP hG hB hM
  have hd : (P*N*G)*(M*B) ≤ P*M*G*M*B := by
    calc
      (P*N*G)*(M*B) = (P*G*M*B)*N := by ring
      _ ≤ (P*G*M*B)*M := Nat.mul_le_mul_left _ hNM
      _ = P*M*G*M*B := by ring
  have hh : 413*P*(M*(G*M*B)) = 413*(P*M*G*M*B) := by ring
  rw [hh]
  change _ ≤ 1200*(P*M*G*M*B)
  nlinarith

/-- Two actual grouped row extensions pad both numerical chunk ranges.
All four grouped dimensions are generated from immutable P,N,G,B,M and
then physically erased; all payload and workspace heads return to zero. -/
theorem pad_hoare (hs : Fin 5 → List Bool) (P N G B M : ℕ)
    (hv : ∀ i, Counter.value (hs i) = values P N G B M i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i))
    (hP : 0 < P) (hN : 0 < N) (hG : 0 < G) (hB : 0 < B) (hNM : N ≤ M)
    (x : Fin (RadixRangePadding.volume P N G B) → Fin 4) :
    HoareTime padProgram (fun v => v = RangePaddingDimensions.input (word x) empty hs)
      (fun v => v = RangePaddingDimensions.input (word (RadixRangePadding.pad M (bitSymbol false) x)) empty hs)
      (1200*RadixRangePadding.volume P M G B) := by
  have hM := lt_of_lt_of_le hN hNM
  have h := (RangePaddingDimensions.construct_hoare (word x) empty hs P N G B M hv hc hP hG hB hM hNM).seq
    (((padD_hoare hs P N G B M hv hc hP hN hG hB hNM x).seq
      (padH_hoare hs P N G B M hv hc hP hN hG hB hNM x)).seq
      (RangePaddingDimensions.cleanup_hoare _ _ hs P N G B M hP hG hB hM hNM))
  exact h.consequence (fun _ hh => hh) (fun _ hh => hh) (budget P N G B M hP hG hB hM hNM)

/-- Reverse physical scans crop H and then D, accepting arbitrary discarded
contents. Only the five original descriptors remain at the final boundary. -/
theorem crop_hoare (hs : Fin 5 → List Bool) (P N G B M : ℕ)
    (hv : ∀ i, Counter.value (hs i) = values P N G B M i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i))
    (hP : 0 < P) (hN : 0 < N) (hG : 0 < G) (hB : 0 < B) (hNM : N ≤ M)
    (x : Fin (RadixRangePadding.volume P M G B) → Fin 4) :
    HoareTime cropProgram (fun v => v = RangePaddingDimensions.input (word x) empty hs)
      (fun v => v = RangePaddingDimensions.input (word (RadixRangePadding.cropStages hNM x)) empty hs)
      (1200*RadixRangePadding.volume P M G B) := by
  have hM := lt_of_lt_of_le hN hNM
  have h := (RangePaddingDimensions.construct_hoare (word x) empty hs P N G B M hv hc hP hG hB hM hNM).seq
    (((cropH_hoare hs P N G B M hv hc hP hN hG hB hNM x).seq
      (cropD_hoare hs P N G B M hv hc hP hN hG hB hNM x)).seq
      (RangePaddingDimensions.cleanup_hoare _ _ hs P N G B M hP hG hB hM hNM))
  have hb := budget P N G B M hP hG hB hM hNM
  have he : 330*RangePaddingDimensions.volume P G B M+1+
      (413*P*(M*(G*M*B))+1+413*(P*N*G)*(M*B)+1+40*RangePaddingDimensions.volume P G B M) =
      330*RangePaddingDimensions.volume P G B M+1+
      (413*(P*N*G)*(M*B)+1+413*P*(M*(G*M*B))+1+40*RangePaddingDimensions.volume P G B M) := by omega
  exact h.consequence (fun _ hh => hh) (fun _ hh => hh) (he.le.trans hb)

/-- The paid crop after a padded numerical transpose returns the original
numerical transpose, using the complete manuscript range-padding semantics. -/
theorem crop_transpose_pad_hoare (hs : Fin 5 → List Bool) (P N G B M : ℕ)
    (hv : ∀ i, Counter.value (hs i) = values P N G B M i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i))
    (hP : 0 < P) (hN : 0 < N) (hG : 0 < G) (hB : 0 < B) (hNM : N ≤ M)
    (x : Fin (RadixRangePadding.volume P N G B) → Fin 4) :
    HoareTime cropProgram
      (fun v => v = RangePaddingDimensions.input (word (RadixRangePadding.transpose (RadixRangePadding.pad M (bitSymbol false) x))) empty hs)
      (fun v => v = RangePaddingDimensions.input (word (RadixRangePadding.transpose x)) empty hs)
      (1200*RadixRangePadding.volume P M G B) := by
  have h := crop_hoare hs P N G B M hv hc hP hN hG hB hNM
    (RadixRangePadding.transpose (RadixRangePadding.pad M (bitSymbol false) x))
  simpa only [RadixRangePadding.cropStages_transpose_pad] using h

end
end IntegerMultBounds.Machine.RadixRangePaddingExecution
