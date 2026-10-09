import IntegerMultBounds.Machine.RadixRangePadding
import IntegerMultBounds.Machine.RadixDigitMoveBlockExecution

/-! Exact rectangular interchange when binary coordinate widths differ by one.
The long-H direction is an equal-width interchange followed by one fixed-radix
binary digit move. The long-D direction reverses that order and movement.
All casts preserve flat offsets; neither spectator coordinate is permuted. -/
namespace IntegerMultBounds.Machine.BinaryAdjacentWidthInterchange
open RecursiveInterchangeRows (pack pack_val)
variable {P H D N G B a : ℕ} {α : Type*}

def volume (P H G D B : ℕ) := P*H*G*D*B

def index (p : Fin P) (h : Fin H) (g : Fin G) (d : Fin D) (b : Fin B) :
    Fin (volume P H G D B) := pack (pack (pack (pack p h) g) d) b

def coordinates (z : Fin (volume P H G D B)) : Fin P × Fin H × Fin G × Fin D × Fin B :=
  let db := finProdFinEquiv.symm z
  let gd := finProdFinEquiv.symm db.1
  let hg := finProdFinEquiv.symm gd.1
  let ph := finProdFinEquiv.symm hg.1
  (ph.1,ph.2,hg.2,gd.2,db.2)

@[simp] theorem coordinates_index (p : Fin P) (h : Fin H) (g : Fin G) (d : Fin D) (b : Fin B) :
    coordinates (index p h g d b) = (p,h,g,d,b) := by simp [coordinates,index,pack]

theorem index_coordinates (z : Fin (volume P H G D B)) :
    index (coordinates z).1 (coordinates z).2.1 (coordinates z).2.2.1
      (coordinates z).2.2.2.1 (coordinates z).2.2.2.2 = z := by
  obtain ⟨⟨phgd,b⟩,rfl⟩ := finProdFinEquiv.surjective z
  obtain ⟨⟨phg,d⟩,rfl⟩ := finProdFinEquiv.surjective phgd
  obtain ⟨⟨ph,g⟩,rfl⟩ := finProdFinEquiv.surjective phg
  obtain ⟨⟨p,h⟩,rfl⟩ := finProdFinEquiv.surjective ph
  simp [coordinates,index,pack]
  rfl

def transpose (x : Fin (volume P H G D B) → α) : Fin (volume P D G H B) → α := fun z =>
  let c := coordinates z
  x (index c.1 c.2.2.2.1 c.2.2.1 c.2.1 c.2.2.2.2)

@[simp] theorem transpose_entry (x : Fin (volume P H G D B) → α)
    (p : Fin P) (h : Fin H) (g : Fin G) (d : Fin D) (b : Fin B) :
    transpose x (index p d g h b) = x (index p h g d b) := by simp [transpose]

@[simp] theorem transpose_transpose (x : Fin (volume P H G D B) → α) :
    transpose (transpose x) = x := by
  funext z
  rw [← index_coordinates z]
  simp only [transpose_entry]

theorem equal_volume (P N G B : ℕ) :
    RadixRangePadding.volume (P*2) N G B = volume P (2*N) G N B := by
  unfold RadixRangePadding.volume volume
  ring

theorem move_input_volume (P N G B : ℕ) :
    P*2*((N*G)*(N*B)) = RadixRangePadding.volume (P*2) N G B := by
  unfold RadixRangePadding.volume
  ring

theorem move_output_volume (P N G B : ℕ) :
    P*(N*G)*2*(N*B) = volume P N G (2*N) B := by
  unfold volume
  ring

/-- Regroup the leading bit of H into the prefix without moving any cell. -/
def equalInput (x : Fin (volume P (2*N) G N B) → α) :
    Fin (RadixRangePadding.volume (P*2) N G B) → α := fun z =>
  x (Fin.cast (equal_volume P N G B) z)

/-- Literal first physical stage: equal-width interchange on the longer prefix. -/
def afterEqual (x : Fin (volume P (2*N) G N B) → Fin (a+4)) :
    Fin (P*2*((N*G)*(N*B))) → Fin (a+4) := fun z =>
  RadixRangePadding.transpose (equalInput x) (Fin.cast (move_input_volume P N G B) z)

/-- Literal second physical stage: the fixed-radix-two block digit move. -/
def longH (x : Fin (volume P (2*N) G N B) → Fin (a+4)) :
    Fin (volume P N G (2*N) B) → Fin (a+4) := fun z =>
  RadixDigitMoveBlockRows.move (afterEqual x) (Fin.cast (move_output_volume P N G B).symm z)

private theorem equal_index (p : Fin P) (j : Fin 2) (h : Fin N) (g : Fin G)
    (d : Fin N) (b : Fin B) :
    Fin.cast (equal_volume P N G B) (RadixRangePadding.index (pack p j) h g d b) =
      index p (pack j h) g d b := by
  apply Fin.ext
  simp only [Fin.cast,RadixRangePadding.index,index,pack_val]
  ring

private theorem move_input_index (p : Fin P) (j : Fin 2) (h : Fin N) (g : Fin G)
    (d : Fin N) (b : Fin B) :
    Fin.cast (move_input_volume P N G B) (pack (pack p j) (pack (pack h g) (pack d b))) =
      RadixRangePadding.index (pack p j) h g d b := by
  apply Fin.ext
  simp only [Fin.val_cast,RadixRangePadding.index,pack_val]
  ring

private theorem move_output_index (p : Fin P) (j : Fin 2) (h : Fin N) (g : Fin G)
    (d : Fin N) (b : Fin B) :
    Fin.cast (move_output_volume P N G B).symm (index p h g (pack j d) b) =
      pack (pack (pack p (pack h g)) j) (pack d b) := by
  apply Fin.ext
  simp only [Fin.cast,index,pack_val]
  ring

theorem longH_entry (x : Fin (volume P (2*N) G N B) → Fin (a+4))
    (p : Fin P) (j : Fin 2) (h : Fin N) (g : Fin G) (d : Fin N) (b : Fin B) :
    longH x (index p d g (pack j h) b) = x (index p (pack j h) g d b) := by
  unfold longH
  rw [move_output_index,RadixDigitMoveBlockRows.move_entry]
  unfold afterEqual
  rw [move_input_index,RadixRangePadding.transpose_entry]
  unfold equalInput
  rw [equal_index]

theorem longH_eq_transpose (x : Fin (volume P (2*N) G N B) → Fin (a+4)) :
    longH x = transpose x := by
  funext z
  rw [← index_coordinates z]
  obtain ⟨⟨j,h⟩,hj⟩ := finProdFinEquiv.surjective (coordinates z).2.2.2.1
  rw [← hj]
  simpa only [transpose_entry,pack] using longH_entry x (coordinates z).1 j h (coordinates z).2.2.1 (coordinates z).2.1 (coordinates z).2.2.2.2

/-- Regroup the shorter-H input for the inverse binary digit move. -/
def moveInput (y : Fin (volume P N G (2*N) B) → Fin (a+4)) :
    Fin (P*(N*G)*2*(N*B)) → Fin (a+4) := fun z =>
  y (Fin.cast (move_output_volume P N G B) z)

/-- Literal first physical stage in the other orientation. -/
def afterUnmove (y : Fin (volume P N G (2*N) B) → Fin (a+4)) :
    Fin (RadixRangePadding.volume (P*2) N G B) → Fin (a+4) := fun z =>
  RadixDigitMoveBlockRows.unmove (moveInput y) (Fin.cast (move_input_volume P N G B).symm z)

/-- The inverse movement followed by equal-width interchange. -/
def longD (y : Fin (volume P N G (2*N) B) → Fin (a+4)) :
    Fin (volume P (2*N) G N B) → Fin (a+4) := fun z =>
  RadixRangePadding.transpose (afterUnmove y) (Fin.cast (equal_volume P N G B).symm z)

theorem longD_entry (y : Fin (volume P N G (2*N) B) → Fin (a+4))
    (p : Fin P) (j : Fin 2) (h : Fin N) (g : Fin G) (d : Fin N) (b : Fin B) :
    longD y (index p (pack j d) g h b) = y (index p h g (pack j d) b) := by
  have he := equal_index p j d g h b
  have hi := move_input_index p j h g d b
  have ho := move_output_index p j h g d b
  unfold longD
  rw [← he]
  simp only [Fin.cast_cast,Fin.cast_eq_self,RadixRangePadding.transpose_entry]
  unfold afterUnmove
  rw [← hi]
  simp only [Fin.cast_cast,Fin.cast_eq_self,RadixDigitMoveBlockRows.unmove_entry]
  unfold moveInput
  rw [← ho]
  simp only [Fin.cast_cast,Fin.cast_eq_self]

theorem longD_eq_transpose (y : Fin (volume P N G (2*N) B) → Fin (a+4)) :
    longD y = transpose y := by
  funext z
  rw [← index_coordinates z]
  obtain ⟨⟨j,d⟩,hj⟩ := finProdFinEquiv.surjective (coordinates z).2.1
  rw [← hj]
  simpa only [transpose_entry,pack] using longD_entry y (coordinates z).1 j (coordinates z).2.2.2.1 (coordinates z).2.2.1 d (coordinates z).2.2.2.2

/-- Cast-only regrouping preserves the actual serialized input word. -/
theorem equalInput_word (x : Fin (volume P (2*N) G N B) → α) :
    List.ofFn (equalInput x) = List.ofFn x :=
  (List.ofFn_congr (equal_volume P N G B).symm x).symm

theorem afterEqual_word (x : Fin (volume P (2*N) G N B) → Fin (a+4)) :
    List.ofFn (afterEqual x) = List.ofFn (RadixRangePadding.transpose (equalInput x)) :=
  (List.ofFn_congr (move_input_volume P N G B).symm
    (RadixRangePadding.transpose (equalInput x))).symm

theorem move_afterEqual_word (x : Fin (volume P (2*N) G N B) → Fin (a+4)) :
    List.ofFn (RadixDigitMoveBlockRows.move (afterEqual x)) = List.ofFn (transpose x) := by
  rw [← longH_eq_transpose]
  exact List.ofFn_congr (move_output_volume P N G B) _

theorem moveInput_word (y : Fin (volume P N G (2*N) B) → Fin (a+4)) :
    List.ofFn (moveInput y) = List.ofFn y :=
  (List.ofFn_congr (move_output_volume P N G B).symm y).symm

theorem unmove_word (y : Fin (volume P N G (2*N) B) → Fin (a+4)) :
    List.ofFn (RadixDigitMoveBlockRows.unmove (moveInput y)) = List.ofFn (afterUnmove y) :=
  List.ofFn_congr (move_input_volume P N G B) _

theorem equal_afterUnmove_word (y : Fin (volume P N G (2*N) B) → Fin (a+4)) :
    List.ofFn (RadixRangePadding.transpose (afterUnmove y)) = List.ofFn (transpose y) := by
  rw [← longD_eq_transpose]
  exact List.ofFn_congr (equal_volume P N G B) _

/-- The extra movement has linear cost in the original rectangular volume.
Its P, N*G, N*B headers must be supplied physically; producing those headers
from the original binary widths is separate caller work. -/
theorem longH_move_hoare (source : ℤ → Fin (a+4))
    (x : Fin (volume P (2*N) G N B) → Fin (a+4)) (ps ss es : List Bool)
    (hP : 0 < P) (hN : 0 < N) (hG : 0 < G) (hB : 0 < B)
    (hp : Counter.value ps = P) (hs : Counter.value ss = N*G) (he : Counter.value es = N*B)
    (cp : GrowingCounterData.Canonical ps) (cs : GrowingCounterData.Canonical ss)
    (ce : GrowingCounterData.Canonical es) :
    HoareTime (RadixDigitMoveBlockExecution.forwardProgram 2 a)
      (fun v => v = RadixDigitMoveBlockExecution.bank (Q := 2)
        (putWord source 0 (List.ofFn (RadixRangePadding.transpose (equalInput x)))) ps ss es)
      (fun v => v = RadixDigitMoveBlockExecution.bank (Q := 2)
        (putWord source 0 (List.ofFn (transpose x))) ps ss es)
      (RadixDigitMoveBlockExecution.bound 2 * volume P (2*N) G N B) := by
  have h := RadixDigitMoveBlockExecution.forward_hoare source (afterEqual x) ps ss es
    hP (by omega) (Nat.mul_pos hN hG) (Nat.mul_pos hN hB) hp hs he cp cs ce
  have hv : P*2*((N*G)*(N*B)) = volume P (2*N) G N B := by unfold volume; ring
  rw [afterEqual_word,move_afterEqual_word,hv] at h
  exact h

/-- Paid inverse move from every shorter-H input, without a forward preimage.
The following equal-width call consumes exactly the displayed output word. -/
theorem longD_unmove_hoare (source : ℤ → Fin (a+4))
    (y : Fin (volume P N G (2*N) B) → Fin (a+4)) (ps ss es : List Bool)
    (hP : 0 < P) (hN : 0 < N) (hG : 0 < G) (hB : 0 < B)
    (hp : Counter.value ps = P) (hs : Counter.value ss = N*G) (he : Counter.value es = N*B)
    (cp : GrowingCounterData.Canonical ps) (cs : GrowingCounterData.Canonical ss)
    (ce : GrowingCounterData.Canonical es) :
    HoareTime (RadixDigitMoveBlockExecution.backwardProgram 2 a)
      (fun v => v = RadixDigitMoveBlockExecution.bank (Q := 2)
        (putWord source 0 (List.ofFn y)) ps ss es)
      (fun v => v = RadixDigitMoveBlockExecution.bank (Q := 2)
        (putWord source 0 (List.ofFn (afterUnmove y))) ps ss es)
      (RadixDigitMoveBlockExecution.bound 2 * volume P N G (2*N) B) := by
  have h := RadixDigitMoveBlockExecution.backward_unmove_hoare source (moveInput y) ps ss es
    hP (by omega) (Nat.mul_pos hN hG) (Nat.mul_pos hN hB) hp hs he cp cs ce
  have hv : P*2*((N*G)*(N*B)) = volume P N G (2*N) B := by unfold volume; ring
  rw [moveInput_word,unmove_word,hv] at h
  exact h

/-- The decomposition includes the boundary case of a zero-bit shorter field. -/
theorem adjacent_binary_width (u : ℕ) : 2*2^u = 2^(u+1) := by
  rw [pow_succ,Nat.mul_comm]

end IntegerMultBounds.Machine.BinaryAdjacentWidthInterchange
