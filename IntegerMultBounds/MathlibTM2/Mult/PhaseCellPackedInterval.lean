module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellEncodedScatter
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCoreRead
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPairComponentsAccuracy

/-! # Packed storage with ambient coordinates

An interval is a slice of the ambient line, not a new periodic system. These
laws separate the physical offset used by readers from the matrix coordinate.
No padding to the ambient period is part of this representation.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

def packedInterval {s : ℕ} (a L : ℕ) (F : ZMod s → GaussianInt) : List GaussianInt :=
  ((chirpLine s F).drop a).take L

@[simp] theorem packedInterval_length {s a L : ℕ} (F : ZMod s → GaussianInt)
    (hfit : a+L ≤ s) : (packedInterval a L F).length = L := by
  simp only [packedInterval,List.length_take,List.length_drop,length_chirpLine]
  exact min_eq_left (by omega)

theorem packedInterval_get {s a L j : ℕ} (F : ZMod s → GaussianInt)
    (hfit : a+L ≤ s) (hj : j < L) :
    (packedInterval a L F)[j]'(by rw [packedInterval_length F hfit]; exact hj) =
      F ((a+j : ℕ) : ZMod s) := by
  simp only [packedInterval,List.getElem_take,List.getElem_drop,chirpLine,
    List.getElem_map,List.getElem_range]

theorem packedInterval_crop {s a L offset count : ℕ} (F : ZMod s → GaussianInt)
    (hfit : offset+count ≤ L) :
    ((packedInterval a L F).drop offset).take count = packedInterval (a+offset) count F := by
  simp only [packedInterval,List.drop_take,List.take_take,List.drop_drop,
    Nat.min_eq_left (show count ≤ L-offset by omega)]

theorem packedInterval_singleton {s a : ℕ} (F : ZMod s → GaussianInt) (ha : a < s) :
    packedInterval a 1 F = [F (a : ZMod s)] := by
  apply List.ext_getElem (by rw [packedInterval_length F (by omega)]; rfl)
  intro j hj hk
  have hj0 : j = 0 := by simp only [List.length_singleton] at hk; omega
  subst j
  simp only [packedInterval_get F (show a+1 ≤ s by omega) (by decide : 0 < 1),
    Nat.add_zero,List.getElem_cons_zero]

/-- Packed input and output contracts depend only on the active interval. -/
theorem packedInterval_congr {s a L : ℕ} (F G : ZMod s → GaussianInt)
    (hfit : a+L ≤ s)
    (heq : ∀ j < L, F ((a+j : ℕ) : ZMod s) = G ((a+j : ℕ) : ZMod s)) :
    packedInterval a L F = packedInterval a L G := by
  apply List.ext_getElem (by rw [packedInterval_length F hfit,packedInterval_length G hfit])
  intro j hj hk
  have hjL : j < L := by simpa only [packedInterval_length F hfit] using hj
  rw [packedInterval_get F hfit hjL,packedInterval_get G hfit hjL]
  exact heq j hjL

theorem packedInterval_symbols {s : ℕ} (A w a L : ℕ) (F : ZMod s → GaussianInt) :
    ((cstream A w (chirpLine s F)).drop (a*w)).take (L*w) =
      cstream A w (packedInterval a L F) := by
  rw [cstream_drop,cstream_take]
  rfl

/-- The reader takes an ambient coordinate but seeks only within the packed halo. -/
noncomputable def packedIntervalRead {A s : ℕ} (q w a : ℕ)
    (raw : List (Fin (A+4))) (i : ZMod s) : ℂ :=
  value q (decodeWord ((raw.drop ((i.val-a)*w)).take w))

/-- The existing real recovery reader accepts the packed halo's ambient origin. -/
theorem packedIntervalRead_re {A s : ℕ} [NeZero s] (q w a : ℕ) (ha : a < s)
    (raw : List (Fin (A+4))) (i : ZMod s) :
    (packedIntervalRead q w a raw i).re = publishedCellRead q w (a : ZMod s) raw i := by
  simp only [packedIntervalRead,publishedCellRead,ZMod.val_natCast,Nat.mod_eq_of_lt ha]

/-- Exact equality of physical reads needs no representability assumption:
both sides decode the same stored word, even in the presence of suffixes. -/
theorem packedIntervalRead_eq {A s : ℕ} [NeZero s] (q w a L : ℕ)
    (F : ZMod s → GaussianInt) (tail ambientTail : List (Fin (A+4)))
    (hfit : a+L ≤ s) (i : ZMod s) (ha : a ≤ i.val) (hi : i.val < a+L) :
    packedIntervalRead q w a (cstream A w (packedInterval a L F)++tail) i =
      pairedCellRead q w (cstream A w (chirpLine s F)++ambientTail) i := by
  have hj : i.val-a < L := by omega
  simp only [packedIntervalRead,pairedCellRead]
  rw [cstream_word w _ tail _ (by rw [packedInterval_length F hfit]; exact hj),
    cstream_word w _ ambientTail _ (by simpa using i.val_lt),packedInterval_get F hfit hj]
  simp only [chirpLine,List.getElem_map,List.getElem_range,Nat.add_sub_of_le ha]

/-- Cropping changes storage, not the arithmetic error bound. -/
theorem packedInterval_error {A s : ℕ} [NeZero s] (q w a L : ℕ)
    (F : ZMod s → GaussianInt) (tail ambientTail : List (Fin (A+4)))
    (hfit : a+L ≤ s) (core : Finset (ZMod s))
    (hcore : ∀ i ∈ core, a ≤ i.val ∧ i.val < a+L)
    (z : ZMod s → ℂ) (e : ℝ)
    (herror : PhaseCellInterface.ErrorOn core
      (pairedCellRead q w (cstream A w (chirpLine s F)++ambientTail)) z e) :
    PhaseCellInterface.ErrorOn core
      (packedIntervalRead q w a (cstream A w (packedInterval a L F)++tail)) z e := by
  intro i hi
  rw [packedIntervalRead_eq q w a L F tail ambientTail hfit i (hcore i hi).1 (hcore i hi).2]
  exact herror i hi

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
