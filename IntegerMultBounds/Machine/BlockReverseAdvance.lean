import IntegerMultBounds.Machine.CountedSeek
import IntegerMultBounds.Machine.CountedReverse
import IntegerMultBounds.Machine.Placement

/-! Reverse one raw block while advancing both payload heads to the next block.
The program seeks to the block's end, moves back one cell, copies backwards to
forward output, moves forward one cell, and seeks over the source block again.
Every move and composition join is charged, including when the block is empty.
The immutable length descriptor and reusable work clock are restored. -/

namespace IntegerMultBounds.Machine.BlockReverseAdvance

/-- Four tape roles: raw source, raw destination, empty clock, binary descriptor. -/
def bank (source dest : ℤ → Fin 4) (bs : List Bool) (p q : ℤ) : Tapes 4 0 :=
  CountedCopyReuse.bank source dest CountedCopyReuse.empty (CountedCopyReuse.binary bs) p q 1 1

/-- Seek on source/clock/descriptor, retaining the entire destination tape. -/
def seekSlots : Fin (3+1) ≃ Fin 4 where
  toFun := fun i => if i = 0 then 0 else if i = 1 then 2 else if i = 2 then 3 else 1
  invFun := fun i => if i = 0 then 0 else if i = 1 then 3 else if i = 2 then 1 else 2
  left_inv := by intro i; fin_cases i <;> decide
  right_inv := by intro i; fin_cases i <;> decide

def seekProgram : Program 4 16 0 := Placement.placed (u := 1) CountedSeek.program seekSlots

private theorem active_seek (f g : ℤ → Fin 4) (bs : List Bool) (p q : ℤ) :
    Placement.active (s := 3) seekSlots (bank f g bs p q) = CountedSeek.bank f p bs := by
  unfold Placement.active bank CountedCopyReuse.bank CountedSeek.bank
  congr 1 <;> funext i <;> fin_cases i <;> rfl

private theorem replace_seek (f g f' : ℤ → Fin 4) (bs : List Bool) (p q p' : ℤ) :
    Placement.replace (s := 3) seekSlots (bank f g bs p q) (CountedSeek.bank f' p' bs) =
      bank f' g bs p' q := by
  unfold Placement.replace Placement.combine Placement.extra Tapes.reindex Tapes.append
    bank CountedCopyReuse.bank CountedSeek.bank
  congr 1 <;> funext i <;> fin_cases i <;> rfl

private theorem seek_hoare (f g : ℤ → Fin 4) (bs : List Bool) (p q : ℤ) :
    HoareTime seekProgram (fun v => v = bank f g bs p q)
      (fun v => v = bank f g bs (p+Counter.value bs) q)
      (5*Counter.value bs+7*bs.length+16) := by
  have h := Placement.hoare_at (CountedSeek.seek_hoare f p bs) seekSlots
    (bank f g bs p q) (active_seek f g bs p q)
  apply h.consequence (fun _ hv => hv) _ le_rfl
  rintro v ⟨w,rfl,rfl⟩
  exact replace_seek f g f bs p q _

/-- A single real displacement of the source head; all cells and other heads
are retained. This is required even for an empty block. -/
def moveProgram (direction : Move) : Program 4 2 0 where
  tapes_pos := by decide
  start := 0
  transition := fun state symbols => if state = 0 then
    some (1,fun i => (symbols i,if i = 0 then direction else .stay)) else none

private theorem move_hoare (direction : Move) (f g : ℤ → Fin 4) (bs : List Bool) (p q : ℤ) :
    HoareTime (moveProgram direction) (fun v => v = bank f g bs p q)
      (fun v => v = bank f g bs (p+direction.offset) q) 1 := by
  rintro v rfl
  let result : Config 4 2 0 :=
    ⟨1,(bank f g bs (p+direction.offset) q).head,(bank f g bs (p+direction.offset) q).tape⟩
  refine ⟨1,result,le_rfl,?_,?_,rfl⟩
  · simp only [run_one,step,moveProgram,Tapes.start,bank,CountedCopyReuse.bank,result,ite_true]
    congr 1
    congr 1
    · funext i
      fin_cases i <;> simp [Move.offset]
    · funext i j
      fin_cases i <;> simp <;> intro h <;> subst j <;> rfl
  · simp [step,moveProgram,result]

/-- The finite controller is fixed independently of the block width. -/
def program : Program 4 52 0 :=
  seq (seq (seq (seq seekProgram (moveProgram .left)) CountedReverse.Reusable.program)
    (moveProgram .right)) seekProgram

/-- Copy the reversed block, preserving every source cell and all destination
cells outside the output segment. Both raw heads advance the complete block,
and the empty clock and immutable descriptor are restored for the next block. -/
theorem reverse_hoare (source dest : ℤ → Fin 4) (p q : ℤ) (xs : List (Fin 4))
    (bs : List Bool) (hcount : Counter.value bs = xs.length) :
    HoareTime program
      (fun v => v = bank (putWord source p xs) dest bs p q)
      (fun v => v = bank (putWord source p xs) (putWord dest q xs.reverse) bs
        (p+xs.length) (q+xs.length))
      (15*xs.length+21*bs.length+54) := by
  let input := putWord source p xs
  let output := putWord dest q xs.reverse
  have h₀ := seek_hoare input dest bs p q
  rw [hcount] at h₀
  have h₁ := move_hoare .left input dest bs (p+xs.length) q
  have h₂ := CountedReverse.Reusable.reverse_hoare source dest p q xs bs hcount
  change HoareTime CountedReverse.Reusable.program
    (fun v => v = bank input dest bs (p+xs.length-1) q)
    (fun v => v = bank input output bs (p-1) (q+xs.length))
    (5*xs.length+7*bs.length+16) at h₂
  have h₃ := move_hoare .right input output bs (p-1) (q+xs.length)
  have h₄ := seek_hoare input output bs p (q+xs.length)
  rw [hcount] at h₄
  simp only [Move.offset] at h₁
  simp only [Move.offset,sub_add_cancel] at h₃
  have h := (((h₀.seq h₁).seq h₂).seq h₃).seq h₄
  apply h.consequence (fun _ hv => hv) (fun _ hv => hv)
  omega

end IntegerMultBounds.Machine.BlockReverseAdvance
