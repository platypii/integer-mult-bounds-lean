import IntegerMultBounds.Machine.BinaryMultiply
import IntegerMultBounds.Machine.Negate
import IntegerMultBounds.Machine.RulerCopy
import IntegerMultBounds.Machine.WordMoves
import IntegerMultBounds.Machine.Branch
import IntegerMultBounds.Machine.Gather

/-! Signed fixed-point multiplication on twelve tapes: two's complement
words `x`, `y` of width `w`, rulers of lengths `p`, `w` and `2w`. Copies of
the operands are replaced by their magnitudes with the signs recorded in two
flag cells; the unsigned product is padded to `2w` bits, its bits from
position `p` on are copied into a `w`-bit output word, which is negated when
the signs differ; every scratch tape is restored. The output word represents
the product truncated toward zero by `p` bits, the fixed-point rounding `ρ`
(proved in `FixedMulValue`). The unsigned product uses the quadratic
`BinaryMultiply`; its cost is the only superlinear term. -/

namespace IntegerMultBounds.Machine.FixedMul

open TwosComplement (negWord)
open CopyCells (cells)

variable {a : ℕ}

/-- The twelve-tape bank: operands, operand copies, product, padded product,
output, three rulers, two sign flags. -/
def bank (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 : ℤ → Fin (a + 4))
    (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 : ℤ) : Tapes 12 a :=
  ⟨fun i => if i = 0 then p0 else if i = 1 then p1 else if i = 2 then p2 else if i = 3 then p3
    else if i = 4 then p4 else if i = 5 then p5 else if i = 6 then p6 else if i = 7 then p7
    else if i = 8 then p8 else if i = 9 then p9 else if i = 10 then p10 else p11,
   fun i => if i = 0 then f0 else if i = 1 then f1 else if i = 2 then f2 else if i = 3 then f3
    else if i = 4 then f4 else if i = 5 then f5 else if i = 6 then f6 else if i = 7 then f7
    else if i = 8 then f8 else if i = 9 then f9 else if i = 10 then f10 else f11⟩

section Words

/-- A ruler of `n` cells. -/
def ruler (n : ℕ) : List (Fin (a + 4)) := List.replicate n (bitSymbol true)

theorem ruler_nonblank (n : ℕ) : ∀ x ∈ ruler (a := a) n, x ≠ blank := by
  intro x hx
  rw [ruler, List.mem_replicate] at hx
  rw [hx.2]; simp [bitSymbol, blank]

@[simp] theorem ruler_length (n : ℕ) : (ruler (a := a) n).length = n := List.length_replicate

/-- The magnitude word: negated when the top bit is set. -/
def mag (x : List Bool) : List Bool := if x.getLastD false then negWord x else x

theorem mag_length (x : List Bool) : (mag x).length = x.length := by
  unfold mag; split_ifs <;> simp [TwosComplement.negWord_length]

/-- The unsigned product padded with zeros to `2w` bits. -/
def padProd (x y : List Bool) (w : ℕ) : List Bool :=
  BinaryMultiply.horner (mag x) (mag y) ++
    List.replicate (2 * w - (BinaryMultiply.horner (mag x) (mag y)).length) false

/-- The result word: the padded product's bits `p` to `p + w`, negated when
the signs differ. -/
def result (x y : List Bool) (p w : ℕ) : List Bool :=
  if x.getLastD false = y.getLastD false then Gather.field (padProd x y w) p w
  else negWord (Gather.field (padProd x y w) p w)

theorem map_split (x : List Bool) (h : x ≠ []) :
    x.map bitSymbol = x.dropLast.map (bitSymbol (a := a)) ++ [bitSymbol (x.getLastD false)] := by
  conv_lhs => rw [← List.dropLast_append_getLast h]
  rw [List.map_append, List.map_singleton, TwosComplement.getLastD_eq x h]

/-- Reading the top bit of a placed word. -/
theorem putWord_last (f : ℤ → Fin (a + 4)) (q : ℤ) (x : List Bool) (h : x ≠ []) (w : ℕ)
    (hx : x.length = w) :
    putWord f q (x.map bitSymbol) (q + ↑w - 1) = bitSymbol (x.getLastD false) := by
  have hpos := List.length_pos_of_ne_nil h
  have heq : (q : ℤ) + ↑w - 1 = q + ↑(x.dropLast.map (bitSymbol (a := a))).length := by
    rw [List.length_map, List.length_dropLast, hx]; omega
  rw [map_split x h, ← putWord_append_forward, heq]
  exact putWord_head _ _ _ _

theorem field_cons (xs : List Bool) (s d : ℕ) :
    Gather.field xs s (d + 1) = xs.getD s false :: Gather.field xs (s + 1) d := by
  simp only [Gather.field, List.range_succ_eq_map, List.map_cons, List.map_map, add_zero]
  congr 1
  refine List.map_congr_left fun j _ => ?_
  simp only [Function.comp]
  congr 1
  omega

/-- Copying cells of a placed bit word from an offset. -/
theorem cells_field1 (f : ℤ → Fin (a + 4)) (q : ℤ) (bs : List Bool) (m d : ℕ) (h : m + d ≤ bs.length) :
    cells (putWord f q (bs.map bitSymbol)) (q + m) d = (Gather.field bs m d).map bitSymbol := by
  induction d generalizing m with
  | zero => rfl
  | succ d ih =>
    rw [cells, field_cons, List.map_cons, Gather.putWord_getD _ _ _ _ (by omega),
      show q + (m : ℤ) + 1 = q + ((m + 1 : ℕ) : ℤ) by push_cast; ring, ih (m + 1) (by omega)]
    cases bs.getD m false <;> simp [CopyCells.zeroFill, bitSymbol, blank]

theorem cells_add (f : ℤ → Fin (a + 4)) (q : ℤ) (m n : ℕ) :
    cells f q (m + n) = cells f q m ++ cells f (q + m) n := by
  induction m generalizing q with
  | zero => simp [cells]
  | succ m ih =>
    rw [Nat.succ_add, cells, cells, ih, List.cons_append]
    congr 3
    push_cast; ring

theorem cells_of_blank (g : ℤ → Fin (a + 4)) (r : ℤ) (n : ℕ) (hg : ∀ k : ℕ, g (r + k) = blank) :
    cells g r n = (List.replicate n false).map bitSymbol := by
  induction n generalizing r with
  | zero => rfl
  | succ n ih =>
    have h0 : g r = blank := by simpa using hg 0
    rw [cells, List.replicate_succ, List.map_cons, h0, ih (r + 1) (fun k => by
      rw [show r + 1 + (k : ℤ) = r + ((k + 1 : ℕ) : ℤ) by push_cast; ring]; exact hg (k + 1))]
    all_goals simp [CopyCells.zeroFill]

/-- Copying past a placed bit word on a blank background pads it with zeros. -/
theorem cells_pad (q : ℤ) (bs : List Bool) (c : ℕ) (h : bs.length ≤ c) :
    cells (putWord (fun _ => (blank : Fin (a + 4))) q (bs.map bitSymbol)) q c =
      (bs ++ List.replicate (c - bs.length) false).map bitSymbol := by
  obtain ⟨k, rfl⟩ : ∃ k, c = bs.length + k := ⟨c - bs.length, by omega⟩
  rw [cells_add, CopyCells.cells_putWord, List.map_append, Nat.add_sub_cancel_left]
  congr 1
  exact cells_of_blank _ _ _ (fun k => by
    rw [putWord_outside _ _ _ _ (Or.inr (by simp only [List.length_map]; omega))])

end Words

def E0_2 : Fin (2 + 10) ≃ Fin 12 where
  toFun := fun i => if i = 0 then 0 else if i = 1 then 2 else if i = 2 then 1 else if i = 3 then 3 else if i = 4 then 4 else if i = 5 then 5 else if i = 6 then 6 else if i = 7 then 7 else if i = 8 then 8 else if i = 9 then 9 else if i = 10 then 10 else 11
  invFun := fun i => if i = 0 then 0 else if i = 1 then 2 else if i = 2 then 1 else if i = 3 then 3 else if i = 4 then 4 else if i = 5 then 5 else if i = 6 then 6 else if i = 7 then 7 else if i = 8 then 8 else if i = 9 then 9 else if i = 10 then 10 else 11
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

theorem E0_2_bank (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 : ℤ → Fin (a + 4)) (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 : ℤ) :
    ((⟨fun i => if i = 0 then p0 else p2, fun i => if i = 0 then f0 else f2⟩ : Tapes 2 a).append (⟨fun i => if i = 0 then p1 else if i = 1 then p3 else if i = 2 then p4 else if i = 3 then p5 else if i = 4 then p6 else if i = 5 then p7 else if i = 6 then p8 else if i = 7 then p9 else if i = 8 then p10 else p11, fun i => if i = 0 then f1 else if i = 1 then f3 else if i = 2 then f4 else if i = 3 then f5 else if i = 4 then f6 else if i = 5 then f7 else if i = 6 then f8 else if i = 7 then f9 else if i = 8 then f10 else f11⟩ : Tapes 10 a)).reindex E0_2 = bank f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 := by
  unfold Tapes.reindex Tapes.append  bank E0_2
  congr 1 <;> funext i <;> fin_cases i <;> rfl

def E0 : Fin (1 + 11) ≃ Fin 12 where
  toFun := fun i => if i = 0 then 0 else if i = 1 then 1 else if i = 2 then 2 else if i = 3 then 3 else if i = 4 then 4 else if i = 5 then 5 else if i = 6 then 6 else if i = 7 then 7 else if i = 8 then 8 else if i = 9 then 9 else if i = 10 then 10 else 11
  invFun := fun i => if i = 0 then 0 else if i = 1 then 1 else if i = 2 then 2 else if i = 3 then 3 else if i = 4 then 4 else if i = 5 then 5 else if i = 6 then 6 else if i = 7 then 7 else if i = 8 then 8 else if i = 9 then 9 else if i = 10 then 10 else 11
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

theorem E0_bank (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 : ℤ → Fin (a + 4)) (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 : ℤ) :
    ((⟨fun _ => p0, fun _ => f0⟩ : Tapes 1 a).append (⟨fun i => if i = 0 then p1 else if i = 1 then p2 else if i = 2 then p3 else if i = 3 then p4 else if i = 4 then p5 else if i = 5 then p6 else if i = 6 then p7 else if i = 7 then p8 else if i = 8 then p9 else if i = 9 then p10 else p11, fun i => if i = 0 then f1 else if i = 1 then f2 else if i = 2 then f3 else if i = 3 then f4 else if i = 4 then f5 else if i = 5 then f6 else if i = 6 then f7 else if i = 7 then f8 else if i = 8 then f9 else if i = 9 then f10 else f11⟩ : Tapes 11 a)).reindex E0 = bank f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 := by
  unfold Tapes.reindex Tapes.append  bank E0
  congr 1 <;> funext i <;> fin_cases i <;> rfl

def E2 : Fin (1 + 11) ≃ Fin 12 where
  toFun := fun i => if i = 0 then 2 else if i = 1 then 0 else if i = 2 then 1 else if i = 3 then 3 else if i = 4 then 4 else if i = 5 then 5 else if i = 6 then 6 else if i = 7 then 7 else if i = 8 then 8 else if i = 9 then 9 else if i = 10 then 10 else 11
  invFun := fun i => if i = 0 then 1 else if i = 1 then 2 else if i = 2 then 0 else if i = 3 then 3 else if i = 4 then 4 else if i = 5 then 5 else if i = 6 then 6 else if i = 7 then 7 else if i = 8 then 8 else if i = 9 then 9 else if i = 10 then 10 else 11
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

theorem E2_bank (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 : ℤ → Fin (a + 4)) (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 : ℤ) :
    ((⟨fun _ => p2, fun _ => f2⟩ : Tapes 1 a).append (⟨fun i => if i = 0 then p0 else if i = 1 then p1 else if i = 2 then p3 else if i = 3 then p4 else if i = 4 then p5 else if i = 5 then p6 else if i = 6 then p7 else if i = 7 then p8 else if i = 8 then p9 else if i = 9 then p10 else p11, fun i => if i = 0 then f0 else if i = 1 then f1 else if i = 2 then f3 else if i = 3 then f4 else if i = 4 then f5 else if i = 5 then f6 else if i = 6 then f7 else if i = 7 then f8 else if i = 8 then f9 else if i = 9 then f10 else f11⟩ : Tapes 11 a)).reindex E2 = bank f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 := by
  unfold Tapes.reindex Tapes.append  bank E2
  congr 1 <;> funext i <;> fin_cases i <;> rfl

def E1_3 : Fin (2 + 10) ≃ Fin 12 where
  toFun := fun i => if i = 0 then 1 else if i = 1 then 3 else if i = 2 then 0 else if i = 3 then 2 else if i = 4 then 4 else if i = 5 then 5 else if i = 6 then 6 else if i = 7 then 7 else if i = 8 then 8 else if i = 9 then 9 else if i = 10 then 10 else 11
  invFun := fun i => if i = 0 then 2 else if i = 1 then 0 else if i = 2 then 3 else if i = 3 then 1 else if i = 4 then 4 else if i = 5 then 5 else if i = 6 then 6 else if i = 7 then 7 else if i = 8 then 8 else if i = 9 then 9 else if i = 10 then 10 else 11
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

theorem E1_3_bank (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 : ℤ → Fin (a + 4)) (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 : ℤ) :
    ((⟨fun i => if i = 0 then p1 else p3, fun i => if i = 0 then f1 else f3⟩ : Tapes 2 a).append (⟨fun i => if i = 0 then p0 else if i = 1 then p2 else if i = 2 then p4 else if i = 3 then p5 else if i = 4 then p6 else if i = 5 then p7 else if i = 6 then p8 else if i = 7 then p9 else if i = 8 then p10 else p11, fun i => if i = 0 then f0 else if i = 1 then f2 else if i = 2 then f4 else if i = 3 then f5 else if i = 4 then f6 else if i = 5 then f7 else if i = 6 then f8 else if i = 7 then f9 else if i = 8 then f10 else f11⟩ : Tapes 10 a)).reindex E1_3 = bank f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 := by
  unfold Tapes.reindex Tapes.append  bank E1_3
  congr 1 <;> funext i <;> fin_cases i <;> rfl

def E1 : Fin (1 + 11) ≃ Fin 12 where
  toFun := fun i => if i = 0 then 1 else if i = 1 then 0 else if i = 2 then 2 else if i = 3 then 3 else if i = 4 then 4 else if i = 5 then 5 else if i = 6 then 6 else if i = 7 then 7 else if i = 8 then 8 else if i = 9 then 9 else if i = 10 then 10 else 11
  invFun := fun i => if i = 0 then 1 else if i = 1 then 0 else if i = 2 then 2 else if i = 3 then 3 else if i = 4 then 4 else if i = 5 then 5 else if i = 6 then 6 else if i = 7 then 7 else if i = 8 then 8 else if i = 9 then 9 else if i = 10 then 10 else 11
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

theorem E1_bank (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 : ℤ → Fin (a + 4)) (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 : ℤ) :
    ((⟨fun _ => p1, fun _ => f1⟩ : Tapes 1 a).append (⟨fun i => if i = 0 then p0 else if i = 1 then p2 else if i = 2 then p3 else if i = 3 then p4 else if i = 4 then p5 else if i = 5 then p6 else if i = 6 then p7 else if i = 7 then p8 else if i = 8 then p9 else if i = 9 then p10 else p11, fun i => if i = 0 then f0 else if i = 1 then f2 else if i = 2 then f3 else if i = 3 then f4 else if i = 4 then f5 else if i = 5 then f6 else if i = 6 then f7 else if i = 7 then f8 else if i = 8 then f9 else if i = 9 then f10 else f11⟩ : Tapes 11 a)).reindex E1 = bank f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 := by
  unfold Tapes.reindex Tapes.append  bank E1
  congr 1 <;> funext i <;> fin_cases i <;> rfl

def E3 : Fin (1 + 11) ≃ Fin 12 where
  toFun := fun i => if i = 0 then 3 else if i = 1 then 0 else if i = 2 then 1 else if i = 3 then 2 else if i = 4 then 4 else if i = 5 then 5 else if i = 6 then 6 else if i = 7 then 7 else if i = 8 then 8 else if i = 9 then 9 else if i = 10 then 10 else 11
  invFun := fun i => if i = 0 then 1 else if i = 1 then 2 else if i = 2 then 3 else if i = 3 then 0 else if i = 4 then 4 else if i = 5 then 5 else if i = 6 then 6 else if i = 7 then 7 else if i = 8 then 8 else if i = 9 then 9 else if i = 10 then 10 else 11
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

theorem E3_bank (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 : ℤ → Fin (a + 4)) (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 : ℤ) :
    ((⟨fun _ => p3, fun _ => f3⟩ : Tapes 1 a).append (⟨fun i => if i = 0 then p0 else if i = 1 then p1 else if i = 2 then p2 else if i = 3 then p4 else if i = 4 then p5 else if i = 5 then p6 else if i = 6 then p7 else if i = 7 then p8 else if i = 8 then p9 else if i = 9 then p10 else p11, fun i => if i = 0 then f0 else if i = 1 then f1 else if i = 2 then f2 else if i = 3 then f4 else if i = 4 then f5 else if i = 5 then f6 else if i = 6 then f7 else if i = 7 then f8 else if i = 8 then f9 else if i = 9 then f10 else f11⟩ : Tapes 11 a)).reindex E3 = bank f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 := by
  unfold Tapes.reindex Tapes.append  bank E3
  congr 1 <;> funext i <;> fin_cases i <;> rfl

def E10 : Fin (1 + 11) ≃ Fin 12 where
  toFun := fun i => if i = 0 then 10 else if i = 1 then 0 else if i = 2 then 1 else if i = 3 then 2 else if i = 4 then 3 else if i = 5 then 4 else if i = 6 then 5 else if i = 7 then 6 else if i = 8 then 7 else if i = 9 then 8 else if i = 10 then 9 else 11
  invFun := fun i => if i = 0 then 1 else if i = 1 then 2 else if i = 2 then 3 else if i = 3 then 4 else if i = 4 then 5 else if i = 5 then 6 else if i = 6 then 7 else if i = 7 then 8 else if i = 8 then 9 else if i = 9 then 10 else if i = 10 then 0 else 11
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

theorem E10_bank (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 : ℤ → Fin (a + 4)) (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 : ℤ) :
    ((⟨fun _ => p10, fun _ => f10⟩ : Tapes 1 a).append (⟨fun i => if i = 0 then p0 else if i = 1 then p1 else if i = 2 then p2 else if i = 3 then p3 else if i = 4 then p4 else if i = 5 then p5 else if i = 6 then p6 else if i = 7 then p7 else if i = 8 then p8 else if i = 9 then p9 else p11, fun i => if i = 0 then f0 else if i = 1 then f1 else if i = 2 then f2 else if i = 3 then f3 else if i = 4 then f4 else if i = 5 then f5 else if i = 6 then f6 else if i = 7 then f7 else if i = 8 then f8 else if i = 9 then f9 else f11⟩ : Tapes 11 a)).reindex E10 = bank f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 := by
  unfold Tapes.reindex Tapes.append  bank E10
  congr 1 <;> funext i <;> fin_cases i <;> rfl

def E11 : Fin (1 + 11) ≃ Fin 12 where
  toFun := fun i => if i = 0 then 11 else if i = 1 then 0 else if i = 2 then 1 else if i = 3 then 2 else if i = 4 then 3 else if i = 5 then 4 else if i = 6 then 5 else if i = 7 then 6 else if i = 8 then 7 else if i = 9 then 8 else if i = 10 then 9 else 10
  invFun := fun i => if i = 0 then 1 else if i = 1 then 2 else if i = 2 then 3 else if i = 3 then 4 else if i = 4 then 5 else if i = 5 then 6 else if i = 6 then 7 else if i = 7 then 8 else if i = 8 then 9 else if i = 9 then 10 else if i = 10 then 11 else 0
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

theorem E11_bank (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 : ℤ → Fin (a + 4)) (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 : ℤ) :
    ((⟨fun _ => p11, fun _ => f11⟩ : Tapes 1 a).append (⟨fun i => if i = 0 then p0 else if i = 1 then p1 else if i = 2 then p2 else if i = 3 then p3 else if i = 4 then p4 else if i = 5 then p5 else if i = 6 then p6 else if i = 7 then p7 else if i = 8 then p8 else if i = 9 then p9 else p10, fun i => if i = 0 then f0 else if i = 1 then f1 else if i = 2 then f2 else if i = 3 then f3 else if i = 4 then f4 else if i = 5 then f5 else if i = 6 then f6 else if i = 7 then f7 else if i = 8 then f8 else if i = 9 then f9 else f10⟩ : Tapes 11 a)).reindex E11 = bank f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 := by
  unfold Tapes.reindex Tapes.append  bank E11
  congr 1 <;> funext i <;> fin_cases i <;> rfl

def E8_4 : Fin (2 + 10) ≃ Fin 12 where
  toFun := fun i => if i = 0 then 8 else if i = 1 then 4 else if i = 2 then 0 else if i = 3 then 1 else if i = 4 then 2 else if i = 5 then 3 else if i = 6 then 5 else if i = 7 then 6 else if i = 8 then 7 else if i = 9 then 9 else if i = 10 then 10 else 11
  invFun := fun i => if i = 0 then 2 else if i = 1 then 3 else if i = 2 then 4 else if i = 3 then 5 else if i = 4 then 1 else if i = 5 then 6 else if i = 6 then 7 else if i = 7 then 8 else if i = 8 then 0 else if i = 9 then 9 else if i = 10 then 10 else 11
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

theorem E8_4_bank (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 : ℤ → Fin (a + 4)) (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 : ℤ) :
    ((⟨fun i => if i = 0 then p8 else p4, fun i => if i = 0 then f8 else f4⟩ : Tapes 2 a).append (⟨fun i => if i = 0 then p0 else if i = 1 then p1 else if i = 2 then p2 else if i = 3 then p3 else if i = 4 then p5 else if i = 5 then p6 else if i = 6 then p7 else if i = 7 then p9 else if i = 8 then p10 else p11, fun i => if i = 0 then f0 else if i = 1 then f1 else if i = 2 then f2 else if i = 3 then f3 else if i = 4 then f5 else if i = 5 then f6 else if i = 6 then f7 else if i = 7 then f9 else if i = 8 then f10 else f11⟩ : Tapes 10 a)).reindex E8_4 = bank f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 := by
  unfold Tapes.reindex Tapes.append  bank E8_4
  congr 1 <;> funext i <;> fin_cases i <;> rfl

def E8 : Fin (1 + 11) ≃ Fin 12 where
  toFun := fun i => if i = 0 then 8 else if i = 1 then 0 else if i = 2 then 1 else if i = 3 then 2 else if i = 4 then 3 else if i = 5 then 4 else if i = 6 then 5 else if i = 7 then 6 else if i = 8 then 7 else if i = 9 then 9 else if i = 10 then 10 else 11
  invFun := fun i => if i = 0 then 1 else if i = 1 then 2 else if i = 2 then 3 else if i = 3 then 4 else if i = 4 then 5 else if i = 5 then 6 else if i = 6 then 7 else if i = 7 then 8 else if i = 8 then 0 else if i = 9 then 9 else if i = 10 then 10 else 11
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

theorem E8_bank (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 : ℤ → Fin (a + 4)) (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 : ℤ) :
    ((⟨fun _ => p8, fun _ => f8⟩ : Tapes 1 a).append (⟨fun i => if i = 0 then p0 else if i = 1 then p1 else if i = 2 then p2 else if i = 3 then p3 else if i = 4 then p4 else if i = 5 then p5 else if i = 6 then p6 else if i = 7 then p7 else if i = 8 then p9 else if i = 9 then p10 else p11, fun i => if i = 0 then f0 else if i = 1 then f1 else if i = 2 then f2 else if i = 3 then f3 else if i = 4 then f4 else if i = 5 then f5 else if i = 6 then f6 else if i = 7 then f7 else if i = 8 then f9 else if i = 9 then f10 else f11⟩ : Tapes 11 a)).reindex E8 = bank f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 := by
  unfold Tapes.reindex Tapes.append  bank E8
  congr 1 <;> funext i <;> fin_cases i <;> rfl

def E2_3_4 : Fin (3 + 9) ≃ Fin 12 where
  toFun := fun i => if i = 0 then 2 else if i = 1 then 3 else if i = 2 then 4 else if i = 3 then 0 else if i = 4 then 1 else if i = 5 then 5 else if i = 6 then 6 else if i = 7 then 7 else if i = 8 then 8 else if i = 9 then 9 else if i = 10 then 10 else 11
  invFun := fun i => if i = 0 then 3 else if i = 1 then 4 else if i = 2 then 0 else if i = 3 then 1 else if i = 4 then 2 else if i = 5 then 5 else if i = 6 then 6 else if i = 7 then 7 else if i = 8 then 8 else if i = 9 then 9 else if i = 10 then 10 else 11
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

theorem E2_3_4_bank (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 : ℤ → Fin (a + 4)) (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 : ℤ) :
    ((BinaryMultiply.bank f2 f3 f4 p2 p3 p4).append (⟨fun i => if i = 0 then p0 else if i = 1 then p1 else if i = 2 then p5 else if i = 3 then p6 else if i = 4 then p7 else if i = 5 then p8 else if i = 6 then p9 else if i = 7 then p10 else p11, fun i => if i = 0 then f0 else if i = 1 then f1 else if i = 2 then f5 else if i = 3 then f6 else if i = 4 then f7 else if i = 5 then f8 else if i = 6 then f9 else if i = 7 then f10 else f11⟩ : Tapes 9 a)).reindex E2_3_4 = bank f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 := by
  unfold Tapes.reindex Tapes.append BinaryMultiply.bank bank E2_3_4
  congr 1 <;> funext i <;> fin_cases i <;> rfl

def E9_4_5 : Fin (3 + 9) ≃ Fin 12 where
  toFun := fun i => if i = 0 then 9 else if i = 1 then 4 else if i = 2 then 5 else if i = 3 then 0 else if i = 4 then 1 else if i = 5 then 2 else if i = 6 then 3 else if i = 7 then 6 else if i = 8 then 7 else if i = 9 then 8 else if i = 10 then 10 else 11
  invFun := fun i => if i = 0 then 3 else if i = 1 then 4 else if i = 2 then 5 else if i = 3 then 6 else if i = 4 then 1 else if i = 5 then 2 else if i = 6 then 7 else if i = 7 then 8 else if i = 8 then 9 else if i = 9 then 0 else if i = 10 then 10 else 11
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

theorem E9_4_5_bank (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 : ℤ → Fin (a + 4)) (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 : ℤ) :
    ((⟨fun i => if i = 0 then p9 else if i = 1 then p4 else p5, fun i => if i = 0 then f9 else if i = 1 then f4 else f5⟩ : Tapes 3 a).append (⟨fun i => if i = 0 then p0 else if i = 1 then p1 else if i = 2 then p2 else if i = 3 then p3 else if i = 4 then p6 else if i = 5 then p7 else if i = 6 then p8 else if i = 7 then p10 else p11, fun i => if i = 0 then f0 else if i = 1 then f1 else if i = 2 then f2 else if i = 3 then f3 else if i = 4 then f6 else if i = 5 then f7 else if i = 6 then f8 else if i = 7 then f10 else f11⟩ : Tapes 9 a)).reindex E9_4_5 = bank f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 := by
  unfold Tapes.reindex Tapes.append  bank E9_4_5
  congr 1 <;> funext i <;> fin_cases i <;> rfl

def E9_4 : Fin (2 + 10) ≃ Fin 12 where
  toFun := fun i => if i = 0 then 9 else if i = 1 then 4 else if i = 2 then 0 else if i = 3 then 1 else if i = 4 then 2 else if i = 5 then 3 else if i = 6 then 5 else if i = 7 then 6 else if i = 8 then 7 else if i = 9 then 8 else if i = 10 then 10 else 11
  invFun := fun i => if i = 0 then 2 else if i = 1 then 3 else if i = 2 then 4 else if i = 3 then 5 else if i = 4 then 1 else if i = 5 then 6 else if i = 6 then 7 else if i = 7 then 8 else if i = 8 then 9 else if i = 9 then 0 else if i = 10 then 10 else 11
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

theorem E9_4_bank (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 : ℤ → Fin (a + 4)) (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 : ℤ) :
    ((⟨fun i => if i = 0 then p9 else p4, fun i => if i = 0 then f9 else f4⟩ : Tapes 2 a).append (⟨fun i => if i = 0 then p0 else if i = 1 then p1 else if i = 2 then p2 else if i = 3 then p3 else if i = 4 then p5 else if i = 5 then p6 else if i = 6 then p7 else if i = 7 then p8 else if i = 8 then p10 else p11, fun i => if i = 0 then f0 else if i = 1 then f1 else if i = 2 then f2 else if i = 3 then f3 else if i = 4 then f5 else if i = 5 then f6 else if i = 6 then f7 else if i = 7 then f8 else if i = 8 then f10 else f11⟩ : Tapes 10 a)).reindex E9_4 = bank f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 := by
  unfold Tapes.reindex Tapes.append  bank E9_4
  congr 1 <;> funext i <;> fin_cases i <;> rfl

def E5 : Fin (1 + 11) ≃ Fin 12 where
  toFun := fun i => if i = 0 then 5 else if i = 1 then 0 else if i = 2 then 1 else if i = 3 then 2 else if i = 4 then 3 else if i = 5 then 4 else if i = 6 then 6 else if i = 7 then 7 else if i = 8 then 8 else if i = 9 then 9 else if i = 10 then 10 else 11
  invFun := fun i => if i = 0 then 1 else if i = 1 then 2 else if i = 2 then 3 else if i = 3 then 4 else if i = 4 then 5 else if i = 5 then 0 else if i = 6 then 6 else if i = 7 then 7 else if i = 8 then 8 else if i = 9 then 9 else if i = 10 then 10 else 11
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

theorem E5_bank (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 : ℤ → Fin (a + 4)) (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 : ℤ) :
    ((⟨fun _ => p5, fun _ => f5⟩ : Tapes 1 a).append (⟨fun i => if i = 0 then p0 else if i = 1 then p1 else if i = 2 then p2 else if i = 3 then p3 else if i = 4 then p4 else if i = 5 then p6 else if i = 6 then p7 else if i = 7 then p8 else if i = 8 then p9 else if i = 9 then p10 else p11, fun i => if i = 0 then f0 else if i = 1 then f1 else if i = 2 then f2 else if i = 3 then f3 else if i = 4 then f4 else if i = 5 then f6 else if i = 6 then f7 else if i = 7 then f8 else if i = 8 then f9 else if i = 9 then f10 else f11⟩ : Tapes 11 a)).reindex E5 = bank f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 := by
  unfold Tapes.reindex Tapes.append  bank E5
  congr 1 <;> funext i <;> fin_cases i <;> rfl

def E4 : Fin (1 + 11) ≃ Fin 12 where
  toFun := fun i => if i = 0 then 4 else if i = 1 then 0 else if i = 2 then 1 else if i = 3 then 2 else if i = 4 then 3 else if i = 5 then 5 else if i = 6 then 6 else if i = 7 then 7 else if i = 8 then 8 else if i = 9 then 9 else if i = 10 then 10 else 11
  invFun := fun i => if i = 0 then 1 else if i = 1 then 2 else if i = 2 then 3 else if i = 3 then 4 else if i = 4 then 0 else if i = 5 then 5 else if i = 6 then 6 else if i = 7 then 7 else if i = 8 then 8 else if i = 9 then 9 else if i = 10 then 10 else 11
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

theorem E4_bank (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 : ℤ → Fin (a + 4)) (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 : ℤ) :
    ((⟨fun _ => p4, fun _ => f4⟩ : Tapes 1 a).append (⟨fun i => if i = 0 then p0 else if i = 1 then p1 else if i = 2 then p2 else if i = 3 then p3 else if i = 4 then p5 else if i = 5 then p6 else if i = 6 then p7 else if i = 7 then p8 else if i = 8 then p9 else if i = 9 then p10 else p11, fun i => if i = 0 then f0 else if i = 1 then f1 else if i = 2 then f2 else if i = 3 then f3 else if i = 4 then f5 else if i = 5 then f6 else if i = 6 then f7 else if i = 7 then f8 else if i = 8 then f9 else if i = 9 then f10 else f11⟩ : Tapes 11 a)).reindex E4 = bank f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 := by
  unfold Tapes.reindex Tapes.append  bank E4
  congr 1 <;> funext i <;> fin_cases i <;> rfl

def E7_5 : Fin (2 + 10) ≃ Fin 12 where
  toFun := fun i => if i = 0 then 7 else if i = 1 then 5 else if i = 2 then 0 else if i = 3 then 1 else if i = 4 then 2 else if i = 5 then 3 else if i = 6 then 4 else if i = 7 then 6 else if i = 8 then 8 else if i = 9 then 9 else if i = 10 then 10 else 11
  invFun := fun i => if i = 0 then 2 else if i = 1 then 3 else if i = 2 then 4 else if i = 3 then 5 else if i = 4 then 6 else if i = 5 then 1 else if i = 6 then 7 else if i = 7 then 0 else if i = 8 then 8 else if i = 9 then 9 else if i = 10 then 10 else 11
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

theorem E7_5_bank (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 : ℤ → Fin (a + 4)) (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 : ℤ) :
    ((⟨fun i => if i = 0 then p7 else p5, fun i => if i = 0 then f7 else f5⟩ : Tapes 2 a).append (⟨fun i => if i = 0 then p0 else if i = 1 then p1 else if i = 2 then p2 else if i = 3 then p3 else if i = 4 then p4 else if i = 5 then p6 else if i = 6 then p8 else if i = 7 then p9 else if i = 8 then p10 else p11, fun i => if i = 0 then f0 else if i = 1 then f1 else if i = 2 then f2 else if i = 3 then f3 else if i = 4 then f4 else if i = 5 then f6 else if i = 6 then f8 else if i = 7 then f9 else if i = 8 then f10 else f11⟩ : Tapes 10 a)).reindex E7_5 = bank f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 := by
  unfold Tapes.reindex Tapes.append  bank E7_5
  congr 1 <;> funext i <;> fin_cases i <;> rfl

def E7 : Fin (1 + 11) ≃ Fin 12 where
  toFun := fun i => if i = 0 then 7 else if i = 1 then 0 else if i = 2 then 1 else if i = 3 then 2 else if i = 4 then 3 else if i = 5 then 4 else if i = 6 then 5 else if i = 7 then 6 else if i = 8 then 8 else if i = 9 then 9 else if i = 10 then 10 else 11
  invFun := fun i => if i = 0 then 1 else if i = 1 then 2 else if i = 2 then 3 else if i = 3 then 4 else if i = 4 then 5 else if i = 5 then 6 else if i = 6 then 7 else if i = 7 then 0 else if i = 8 then 8 else if i = 9 then 9 else if i = 10 then 10 else 11
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

theorem E7_bank (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 : ℤ → Fin (a + 4)) (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 : ℤ) :
    ((⟨fun _ => p7, fun _ => f7⟩ : Tapes 1 a).append (⟨fun i => if i = 0 then p0 else if i = 1 then p1 else if i = 2 then p2 else if i = 3 then p3 else if i = 4 then p4 else if i = 5 then p5 else if i = 6 then p6 else if i = 7 then p8 else if i = 8 then p9 else if i = 9 then p10 else p11, fun i => if i = 0 then f0 else if i = 1 then f1 else if i = 2 then f2 else if i = 3 then f3 else if i = 4 then f4 else if i = 5 then f5 else if i = 6 then f6 else if i = 7 then f8 else if i = 8 then f9 else if i = 9 then f10 else f11⟩ : Tapes 11 a)).reindex E7 = bank f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 := by
  unfold Tapes.reindex Tapes.append  bank E7
  congr 1 <;> funext i <;> fin_cases i <;> rfl

def E8_5_6 : Fin (3 + 9) ≃ Fin 12 where
  toFun := fun i => if i = 0 then 8 else if i = 1 then 5 else if i = 2 then 6 else if i = 3 then 0 else if i = 4 then 1 else if i = 5 then 2 else if i = 6 then 3 else if i = 7 then 4 else if i = 8 then 7 else if i = 9 then 9 else if i = 10 then 10 else 11
  invFun := fun i => if i = 0 then 3 else if i = 1 then 4 else if i = 2 then 5 else if i = 3 then 6 else if i = 4 then 7 else if i = 5 then 1 else if i = 6 then 2 else if i = 7 then 8 else if i = 8 then 0 else if i = 9 then 9 else if i = 10 then 10 else 11
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

theorem E8_5_6_bank (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 : ℤ → Fin (a + 4)) (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 : ℤ) :
    ((⟨fun i => if i = 0 then p8 else if i = 1 then p5 else p6, fun i => if i = 0 then f8 else if i = 1 then f5 else f6⟩ : Tapes 3 a).append (⟨fun i => if i = 0 then p0 else if i = 1 then p1 else if i = 2 then p2 else if i = 3 then p3 else if i = 4 then p4 else if i = 5 then p7 else if i = 6 then p9 else if i = 7 then p10 else p11, fun i => if i = 0 then f0 else if i = 1 then f1 else if i = 2 then f2 else if i = 3 then f3 else if i = 4 then f4 else if i = 5 then f7 else if i = 6 then f9 else if i = 7 then f10 else f11⟩ : Tapes 9 a)).reindex E8_5_6 = bank f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 := by
  unfold Tapes.reindex Tapes.append  bank E8_5_6
  congr 1 <;> funext i <;> fin_cases i <;> rfl

def E6 : Fin (1 + 11) ≃ Fin 12 where
  toFun := fun i => if i = 0 then 6 else if i = 1 then 0 else if i = 2 then 1 else if i = 3 then 2 else if i = 4 then 3 else if i = 5 then 4 else if i = 6 then 5 else if i = 7 then 7 else if i = 8 then 8 else if i = 9 then 9 else if i = 10 then 10 else 11
  invFun := fun i => if i = 0 then 1 else if i = 1 then 2 else if i = 2 then 3 else if i = 3 then 4 else if i = 4 then 5 else if i = 5 then 6 else if i = 6 then 0 else if i = 7 then 7 else if i = 8 then 8 else if i = 9 then 9 else if i = 10 then 10 else 11
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

theorem E6_bank (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 : ℤ → Fin (a + 4)) (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 : ℤ) :
    ((⟨fun _ => p6, fun _ => f6⟩ : Tapes 1 a).append (⟨fun i => if i = 0 then p0 else if i = 1 then p1 else if i = 2 then p2 else if i = 3 then p3 else if i = 4 then p4 else if i = 5 then p5 else if i = 6 then p7 else if i = 7 then p8 else if i = 8 then p9 else if i = 9 then p10 else p11, fun i => if i = 0 then f0 else if i = 1 then f1 else if i = 2 then f2 else if i = 3 then f3 else if i = 4 then f4 else if i = 5 then f5 else if i = 6 then f7 else if i = 7 then f8 else if i = 8 then f9 else if i = 9 then f10 else f11⟩ : Tapes 11 a)).reindex E6 = bank f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 := by
  unfold Tapes.reindex Tapes.append  bank E6
  congr 1 <;> funext i <;> fin_cases i <;> rfl

section Parts

def copyX := reindex (extend (CopyWord.program (a := a)) 10) E0_2
def retX := reindex (extend (ReturnOrigin.program (a := a)) 11) E0
def retXs := reindex (extend (ReturnOrigin.program (a := a)) 11) E2
def copyY := reindex (extend (CopyWord.program (a := a)) 10) E1_3
def retY := reindex (extend (ReturnOrigin.program (a := a)) 11) E1
def retYs := reindex (extend (ReturnOrigin.program (a := a)) 11) E3
def scanXs := reindex (extend (ScanEnd.program (a := a)) 11) E2
def leftXs := reindex (extend (StepLeft.program (a := a)) 11) E2
def negXs := reindex (extend (Negate.program a) 11) E2
def flag1T := reindex (extend (WriteSymbol.program (bitSymbol (a := a) true)) 11) E10
def flag1F := reindex (extend (WriteSymbol.program (bitSymbol (a := a) false)) 11) E10
def scanYs := reindex (extend (ScanEnd.program (a := a)) 11) E3
def leftYs := reindex (extend (StepLeft.program (a := a)) 11) E3
def negYs := reindex (extend (Negate.program a) 11) E3
def flag2T := reindex (extend (WriteSymbol.program (bitSymbol (a := a) true)) 11) E11
def flag2F := reindex (extend (WriteSymbol.program (bitSymbol (a := a) false)) 11) E11
def advP := reindex (extend (RulerAdvance.program (a := a)) 10) E8_4
def retRw := reindex (extend (ReturnOrigin.program (a := a)) 11) E8
def mulPart := reindex (extend (BinaryMultiply.program a) 9) E2_3_4
def rightYs := reindex (extend (StepRight.program (a := a)) 11) E3
def padP := reindex (extend (RulerCopy.program (a := a)) 9) E9_4_5
def backP := reindex (extend (RulerRetreat.program (a := a)) 10) E9_4
def retP2 := reindex (extend (ReturnOrigin.program (a := a)) 11) E5
def scanP := reindex (extend (ScanEnd.program (a := a)) 11) E4
def eraseP := reindex (extend (EraseBack.program (a := a)) 11) E4
def shiftP2 := reindex (extend (RulerAdvance.program (a := a)) 10) E7_5
def retRp := reindex (extend (ReturnOrigin.program (a := a)) 11) E7
def copyO := reindex (extend (RulerCopy.program (a := a)) 9) E8_5_6
def retO := reindex (extend (ReturnOrigin.program (a := a)) 11) E6
def scanP2 := reindex (extend (ScanEnd.program (a := a)) 11) E5
def eraseP2 := reindex (extend (EraseBack.program (a := a)) 11) E5
def eraseXs := reindex (extend (EraseBack.program (a := a)) 11) E2
def eraseYs := reindex (extend (EraseBack.program (a := a)) 11) E3
def negO := reindex (extend (Negate.program a) 11) E6
def eraseF1 := reindex (extend (EraseCell.program (a := a)) 11) E10
def eraseF2 := reindex (extend (EraseCell.program (a := a)) 11) E11

def prefix1 := (seq (seq (seq (seq (seq (seq (seq (copyX (a := a)) retX) retXs) copyY) retY) retYs) scanXs) leftXs)
def sxTrue := (seq (seq (seq (retXs (a := a)) negXs) retXs) flag1T)
def sxFalse := (seq (retXs (a := a)) flag1F)
def prefix2 := (seq (scanYs (a := a)) leftYs)
def syTrue := (seq (seq (seq (retYs (a := a)) negYs) retYs) flag2T)
def syFalse := (seq (retYs (a := a)) flag2F)
def core := (seq (seq (seq (seq (seq (seq (seq (seq (seq (seq (seq (seq (seq (seq (seq (seq (seq (seq (seq (seq (seq (seq (advP (a := a)) retRw) scanYs) leftYs) mulPart) rightYs) padP) backP) retP2) scanP) eraseP) shiftP2) retRp) copyO) retRw) retO) retP2) scanP2) eraseP2) scanXs) eraseXs) scanYs) eraseYs)
def negChain := (seq (negO (a := a)) retO)
def cleanup := (seq (eraseF1 (a := a)) eraseF2)
def cond1 := branch (fun sy => decide (sy 2 = bitSymbol true)) (sxTrue (a := a)) sxFalse
def cond2 := branch (fun sy => decide (sy 3 = bitSymbol true)) (syTrue (a := a)) syFalse
def skipO : Program 12 1 a := skip 12 a (by norm_num)
def final := branch (fun sy => decide (sy 10 = bitSymbol true))
  (branch (fun sy => decide (sy 11 = bitSymbol true)) (skipO (a := a)) negChain)
  (branch (fun sy => decide (sy 11 = bitSymbol true)) (negChain (a := a)) skipO)
/-- The signed fixed-point multiply: magnitudes and sign flags, the unsigned
product, the shift by the ruler, the sign, and cleanup. -/
def program := seq (seq (seq (seq (seq (seq (prefix1 (a := a)) cond1) prefix2) cond2) core) final) cleanup

end Parts

section Bounds

def prefix1_hoareBound (p w : ℕ) : ℕ := 7 * w + 20
def sxTrue_hoareBound (p w : ℕ) : ℕ := 3 * w + 10
def sxFalse_hoareBound (p w : ℕ) : ℕ := w + 10
def prefix2_hoareBound (p w : ℕ) : ℕ := w + 5
def syTrue_hoareBound (p w : ℕ) : ℕ := 3 * w + 10
def syFalse_hoareBound (p w : ℕ) : ℕ := w + 10
def core_hoareBound (p w : ℕ) : ℕ := w * (5 * w + 2 * w + 18) + 30 * w + 4 * p + 60
def negChain_hoareBound (p w : ℕ) : ℕ := 2 * w + 5
def cleanup_hoareBound (p w : ℕ) : ℕ := 4

end Bounds

theorem prefix1_hoare (x y : List Bool) (p w : ℕ) (f g : ℤ → Fin (a + 4))
    (pX pY pXs pYs pP pP2 pO pRp pRw pR2 pF1 pF2 : ℤ) (hx : x.length = w) (hy : y.length = w)
    (hw : 1 ≤ w) (hpw : p ≤ w) (hfl : f (pX - 1) = blank) (hfr : f (pX + w) = blank)
    (hgl : g (pY - 1) = blank) (hgr : g (pY + w) = blank) :
    ∃ c, HoareTime (prefix1) (fun v => v = bank (putWord f pX (x.map bitSymbol)) (putWord g pY (y.map bitSymbol)) ((fun _ => blank)) ((fun _ => blank)) ((fun _ => blank)) ((fun _ => blank)) ((fun _ => blank)) (putWord (fun _ => blank) pRp (ruler p)) (putWord (fun _ => blank) pRw (ruler w)) (putWord (fun _ => blank) pR2 (ruler (2 * w))) ((fun _ => blank)) ((fun _ => blank)) (pX) (pY) (pXs) (pYs) (pP) (pP2) (pO) (pRp) (pRw) (pR2) (pF1) (pF2))
      (fun v => v = bank (putWord f pX (x.map bitSymbol)) (putWord g pY (y.map bitSymbol)) (putWord (fun _ => blank) pXs ((x).map bitSymbol)) (putWord (fun _ => blank) pYs ((y).map bitSymbol)) ((fun _ => blank)) ((fun _ => blank)) ((fun _ => blank)) (putWord (fun _ => blank) pRp (ruler p)) (putWord (fun _ => blank) pRw (ruler w)) (putWord (fun _ => blank) pR2 (ruler (2 * w))) ((fun _ => blank)) ((fun _ => blank)) (pX) (pY) (pXs + ↑w - 1) (pYs) (pP) (pP2) (pO) (pRp) (pRw) (pR2) (pF1) (pF2)) c ∧ c ≤ prefix1_hoareBound p w := by
  have hx0 : x ≠ [] := by intro h0; rw [h0] at hx; simp at hx; omega
  have hy0 : y ≠ [] := by intro h0; rw [h0] at hy; simp at hy; omega
  have hfr' : f (pX + ↑(x.map (bitSymbol (a := a))).length) = blank := by rw [List.length_map, hx]; exact hfr
  have hgr' : g (pY + ↑(y.map (bitSymbol (a := a))).length) = blank := by rw [List.length_map, hy]; exact hgr
  have hxsplit := map_split (a := a) x hx0
  have hysplit := map_split (a := a) y hy0
  have hx1 : (pXs : ℤ) + ↑w - 1 = pXs + ↑(x.dropLast.map (bitSymbol (a := a))).length := by
    simp [List.length_dropLast, hx]; omega
  have hy1 : (pYs : ℤ) + ↑w - 1 = pYs + ↑(y.dropLast.map (bitSymbol (a := a))).length := by
    simp [List.length_dropLast, hy]; omega
  have hmx : (mag x).length = w := by rw [mag_length, hx]
  have hmy : (mag y).length = w := by rw [mag_length, hy]
  have hhw : (BinaryMultiply.horner (mag x) (mag y)).length ≤ 2 * w := by
    have := BinaryMultiply.horner_length (mag x) (mag y); omega
  have hpadlen : (padProd x y w).length = 2 * w := by simp [padProd]; omega
  have hpad := cells_pad (a := a) pP (BinaryMultiply.horner (mag x) (mag y)) (2 * w) hhw
  have hfield : CopyCells.cells (putWord (fun _ => (blank : Fin (a + 4))) pP2 ((padProd x y w).map bitSymbol)) (pP2 + ↑p) w =
      (Gather.field (padProd x y w) p w).map bitSymbol :=
    cells_field1 _ _ _ _ _ (by omega)
  have hP2split : ((padProd x y w).take (p + w)).map (bitSymbol (a := a)) ++ ((padProd x y w).drop (p + w)).map bitSymbol =
      (padProd x y w).map bitSymbol := by
    rw [← List.map_append, List.take_append_drop]
  have hP2head : (pP2 : ℤ) + ↑p + ↑w = pP2 + ↑(((padProd x y w).take (p + w)).map (bitSymbol (a := a))).length := by
    simp [List.length_take, hpadlen]; omega
  have s1 := hoare_place (CopyWord.copy_hoare f (fun _ => blank) pX pXs (x.map bitSymbol) (ReturnOrigin.bits_nonblank _) hfr') E0_2
    (⟨fun j => if j = 0 then pY else if j = 1 then pYs else if j = 2 then pP else if j = 3 then pP2 else if j = 4 then pO else if j = 5 then pRp else if j = 6 then pRw else if j = 7 then pR2 else if j = 8 then pF1 else pF2, fun j => if j = 0 then putWord g pY (y.map bitSymbol) else if j = 1 then (fun _ => blank) else if j = 2 then (fun _ => blank) else if j = 3 then (fun _ => blank) else if j = 4 then (fun _ => blank) else if j = 5 then putWord (fun _ => blank) pRp (ruler p) else if j = 6 then putWord (fun _ => blank) pRw (ruler w) else if j = 7 then putWord (fun _ => blank) pR2 (ruler (2 * w)) else if j = 8 then (fun _ => blank) else (fun _ => blank)⟩ : Tapes 10 a)
  simp only [CopyWord.cfg, Config.tapes] at s1
  rw [E0_2_bank, E0_2_bank, List.length_map, hx] at s1
  have s2 := hoare_place (ReturnOrigin.return_hoare_at f pX (x.map bitSymbol) (ReturnOrigin.bits_nonblank _) hfl) E0
    (⟨fun j => if j = 0 then pY else if j = 1 then pXs + ↑w else if j = 2 then pYs else if j = 3 then pP else if j = 4 then pP2 else if j = 5 then pO else if j = 6 then pRp else if j = 7 then pRw else if j = 8 then pR2 else if j = 9 then pF1 else pF2, fun j => if j = 0 then putWord g pY (y.map bitSymbol) else if j = 1 then putWord (fun _ => blank) pXs ((x).map bitSymbol) else if j = 2 then (fun _ => blank) else if j = 3 then (fun _ => blank) else if j = 4 then (fun _ => blank) else if j = 5 then (fun _ => blank) else if j = 6 then putWord (fun _ => blank) pRp (ruler p) else if j = 7 then putWord (fun _ => blank) pRw (ruler w) else if j = 8 then putWord (fun _ => blank) pR2 (ruler (2 * w)) else if j = 9 then (fun _ => blank) else (fun _ => blank)⟩ : Tapes 11 a)
  simp only [ReturnOrigin.cfg, Config.tapes] at s2
  rw [E0_bank, E0_bank, List.length_map, hx] at s2
  have s3 := hoare_place (ReturnOrigin.return_hoare_at (fun _ => blank) pXs ((x).map bitSymbol) (ReturnOrigin.bits_nonblank _) rfl) E2
    (⟨fun j => if j = 0 then pX else if j = 1 then pY else if j = 2 then pYs else if j = 3 then pP else if j = 4 then pP2 else if j = 5 then pO else if j = 6 then pRp else if j = 7 then pRw else if j = 8 then pR2 else if j = 9 then pF1 else pF2, fun j => if j = 0 then putWord f pX (x.map bitSymbol) else if j = 1 then putWord g pY (y.map bitSymbol) else if j = 2 then (fun _ => blank) else if j = 3 then (fun _ => blank) else if j = 4 then (fun _ => blank) else if j = 5 then (fun _ => blank) else if j = 6 then putWord (fun _ => blank) pRp (ruler p) else if j = 7 then putWord (fun _ => blank) pRw (ruler w) else if j = 8 then putWord (fun _ => blank) pR2 (ruler (2 * w)) else if j = 9 then (fun _ => blank) else (fun _ => blank)⟩ : Tapes 11 a)
  simp only [ReturnOrigin.cfg, Config.tapes] at s3
  rw [E2_bank, E2_bank, List.length_map, hx] at s3
  have s4 := hoare_place (CopyWord.copy_hoare g (fun _ => blank) pY pYs (y.map bitSymbol) (ReturnOrigin.bits_nonblank _) hgr') E1_3
    (⟨fun j => if j = 0 then pX else if j = 1 then pXs else if j = 2 then pP else if j = 3 then pP2 else if j = 4 then pO else if j = 5 then pRp else if j = 6 then pRw else if j = 7 then pR2 else if j = 8 then pF1 else pF2, fun j => if j = 0 then putWord f pX (x.map bitSymbol) else if j = 1 then putWord (fun _ => blank) pXs ((x).map bitSymbol) else if j = 2 then (fun _ => blank) else if j = 3 then (fun _ => blank) else if j = 4 then (fun _ => blank) else if j = 5 then putWord (fun _ => blank) pRp (ruler p) else if j = 6 then putWord (fun _ => blank) pRw (ruler w) else if j = 7 then putWord (fun _ => blank) pR2 (ruler (2 * w)) else if j = 8 then (fun _ => blank) else (fun _ => blank)⟩ : Tapes 10 a)
  simp only [CopyWord.cfg, Config.tapes] at s4
  rw [E1_3_bank, E1_3_bank, List.length_map, hy] at s4
  have s5 := hoare_place (ReturnOrigin.return_hoare_at g pY (y.map bitSymbol) (ReturnOrigin.bits_nonblank _) hgl) E1
    (⟨fun j => if j = 0 then pX else if j = 1 then pXs else if j = 2 then pYs + ↑w else if j = 3 then pP else if j = 4 then pP2 else if j = 5 then pO else if j = 6 then pRp else if j = 7 then pRw else if j = 8 then pR2 else if j = 9 then pF1 else pF2, fun j => if j = 0 then putWord f pX (x.map bitSymbol) else if j = 1 then putWord (fun _ => blank) pXs ((x).map bitSymbol) else if j = 2 then putWord (fun _ => blank) pYs ((y).map bitSymbol) else if j = 3 then (fun _ => blank) else if j = 4 then (fun _ => blank) else if j = 5 then (fun _ => blank) else if j = 6 then putWord (fun _ => blank) pRp (ruler p) else if j = 7 then putWord (fun _ => blank) pRw (ruler w) else if j = 8 then putWord (fun _ => blank) pR2 (ruler (2 * w)) else if j = 9 then (fun _ => blank) else (fun _ => blank)⟩ : Tapes 11 a)
  simp only [ReturnOrigin.cfg, Config.tapes] at s5
  rw [E1_bank, E1_bank, List.length_map, hy] at s5
  have s6 := hoare_place (ReturnOrigin.return_hoare_at (fun _ => blank) pYs ((y).map bitSymbol) (ReturnOrigin.bits_nonblank _) rfl) E3
    (⟨fun j => if j = 0 then pX else if j = 1 then pY else if j = 2 then pXs else if j = 3 then pP else if j = 4 then pP2 else if j = 5 then pO else if j = 6 then pRp else if j = 7 then pRw else if j = 8 then pR2 else if j = 9 then pF1 else pF2, fun j => if j = 0 then putWord f pX (x.map bitSymbol) else if j = 1 then putWord g pY (y.map bitSymbol) else if j = 2 then putWord (fun _ => blank) pXs ((x).map bitSymbol) else if j = 3 then (fun _ => blank) else if j = 4 then (fun _ => blank) else if j = 5 then (fun _ => blank) else if j = 6 then putWord (fun _ => blank) pRp (ruler p) else if j = 7 then putWord (fun _ => blank) pRw (ruler w) else if j = 8 then putWord (fun _ => blank) pR2 (ruler (2 * w)) else if j = 9 then (fun _ => blank) else (fun _ => blank)⟩ : Tapes 11 a)
  simp only [ReturnOrigin.cfg, Config.tapes] at s6
  rw [E3_bank, E3_bank, List.length_map, hy] at s6
  have s7 := hoare_place (ScanEnd.scan_hoare (fun _ => blank) pXs ((x).map bitSymbol) (ReturnOrigin.bits_nonblank _) rfl) E2
    (⟨fun j => if j = 0 then pX else if j = 1 then pY else if j = 2 then pYs else if j = 3 then pP else if j = 4 then pP2 else if j = 5 then pO else if j = 6 then pRp else if j = 7 then pRw else if j = 8 then pR2 else if j = 9 then pF1 else pF2, fun j => if j = 0 then putWord f pX (x.map bitSymbol) else if j = 1 then putWord g pY (y.map bitSymbol) else if j = 2 then putWord (fun _ => blank) pYs ((y).map bitSymbol) else if j = 3 then (fun _ => blank) else if j = 4 then (fun _ => blank) else if j = 5 then (fun _ => blank) else if j = 6 then putWord (fun _ => blank) pRp (ruler p) else if j = 7 then putWord (fun _ => blank) pRw (ruler w) else if j = 8 then putWord (fun _ => blank) pR2 (ruler (2 * w)) else if j = 9 then (fun _ => blank) else (fun _ => blank)⟩ : Tapes 11 a)
  simp only [ScanEnd.cfg, Config.tapes] at s7
  rw [E2_bank, E2_bank, List.length_map, hx] at s7
  have s8 := hoare_place (StepLeft.step_hoare (putWord (fun _ => blank) pXs (x.map bitSymbol)) (pXs + ↑w)) E2
    (⟨fun j => if j = 0 then pX else if j = 1 then pY else if j = 2 then pYs else if j = 3 then pP else if j = 4 then pP2 else if j = 5 then pO else if j = 6 then pRp else if j = 7 then pRw else if j = 8 then pR2 else if j = 9 then pF1 else pF2, fun j => if j = 0 then putWord f pX (x.map bitSymbol) else if j = 1 then putWord g pY (y.map bitSymbol) else if j = 2 then putWord (fun _ => blank) pYs ((y).map bitSymbol) else if j = 3 then (fun _ => blank) else if j = 4 then (fun _ => blank) else if j = 5 then (fun _ => blank) else if j = 6 then putWord (fun _ => blank) pRp (ruler p) else if j = 7 then putWord (fun _ => blank) pRw (ruler w) else if j = 8 then putWord (fun _ => blank) pR2 (ruler (2 * w)) else if j = 9 then (fun _ => blank) else (fun _ => blank)⟩ : Tapes 11 a)
  simp only [StepLeft.cfg, Config.tapes] at s8
  rw [E2_bank, E2_bank] at s8
  refine ⟨_, (((((((s1.seq s2).seq s3).seq s4).seq s5).seq s6).seq s7).seq s8), ?_⟩
  unfold prefix1_hoareBound
  omega

theorem sxTrue_hoare (x y : List Bool) (p w : ℕ) (f g : ℤ → Fin (a + 4))
    (pX pY pXs pYs pP pP2 pO pRp pRw pR2 pF1 pF2 : ℤ) (hx : x.length = w) (hy : y.length = w)
    (hw : 1 ≤ w) (hpw : p ≤ w) (hfl : f (pX - 1) = blank) (hfr : f (pX + w) = blank)
    (hgl : g (pY - 1) = blank) (hgr : g (pY + w) = blank) :
    ∃ c, HoareTime (sxTrue) (fun v => v = bank (putWord f pX (x.map bitSymbol)) (putWord g pY (y.map bitSymbol)) (putWord (fun _ => blank) pXs ((x).map bitSymbol)) (putWord (fun _ => blank) pYs ((y).map bitSymbol)) ((fun _ => blank)) ((fun _ => blank)) ((fun _ => blank)) (putWord (fun _ => blank) pRp (ruler p)) (putWord (fun _ => blank) pRw (ruler w)) (putWord (fun _ => blank) pR2 (ruler (2 * w))) ((fun _ => blank)) ((fun _ => blank)) (pX) (pY) (pXs + ↑w - 1) (pYs) (pP) (pP2) (pO) (pRp) (pRw) (pR2) (pF1) (pF2))
      (fun v => v = bank (putWord f pX (x.map bitSymbol)) (putWord g pY (y.map bitSymbol)) (putWord (fun _ => blank) pXs ((negWord x).map bitSymbol)) (putWord (fun _ => blank) pYs ((y).map bitSymbol)) ((fun _ => blank)) ((fun _ => blank)) ((fun _ => blank)) (putWord (fun _ => blank) pRp (ruler p)) (putWord (fun _ => blank) pRw (ruler w)) (putWord (fun _ => blank) pR2 (ruler (2 * w))) (putWord (fun _ => blank) pF1 [bitSymbol true]) ((fun _ => blank)) (pX) (pY) (pXs) (pYs) (pP) (pP2) (pO) (pRp) (pRw) (pR2) (pF1) (pF2)) c ∧ c ≤ sxTrue_hoareBound p w := by
  have hx0 : x ≠ [] := by intro h0; rw [h0] at hx; simp at hx; omega
  have hy0 : y ≠ [] := by intro h0; rw [h0] at hy; simp at hy; omega
  have hfr' : f (pX + ↑(x.map (bitSymbol (a := a))).length) = blank := by rw [List.length_map, hx]; exact hfr
  have hgr' : g (pY + ↑(y.map (bitSymbol (a := a))).length) = blank := by rw [List.length_map, hy]; exact hgr
  have hxsplit := map_split (a := a) x hx0
  have hysplit := map_split (a := a) y hy0
  have hx1 : (pXs : ℤ) + ↑w - 1 = pXs + ↑(x.dropLast.map (bitSymbol (a := a))).length := by
    simp [List.length_dropLast, hx]; omega
  have hy1 : (pYs : ℤ) + ↑w - 1 = pYs + ↑(y.dropLast.map (bitSymbol (a := a))).length := by
    simp [List.length_dropLast, hy]; omega
  have hmx : (mag x).length = w := by rw [mag_length, hx]
  have hmy : (mag y).length = w := by rw [mag_length, hy]
  have hhw : (BinaryMultiply.horner (mag x) (mag y)).length ≤ 2 * w := by
    have := BinaryMultiply.horner_length (mag x) (mag y); omega
  have hpadlen : (padProd x y w).length = 2 * w := by simp [padProd]; omega
  have hpad := cells_pad (a := a) pP (BinaryMultiply.horner (mag x) (mag y)) (2 * w) hhw
  have hfield : CopyCells.cells (putWord (fun _ => (blank : Fin (a + 4))) pP2 ((padProd x y w).map bitSymbol)) (pP2 + ↑p) w =
      (Gather.field (padProd x y w) p w).map bitSymbol :=
    cells_field1 _ _ _ _ _ (by omega)
  have hP2split : ((padProd x y w).take (p + w)).map (bitSymbol (a := a)) ++ ((padProd x y w).drop (p + w)).map bitSymbol =
      (padProd x y w).map bitSymbol := by
    rw [← List.map_append, List.take_append_drop]
  have hP2head : (pP2 : ℤ) + ↑p + ↑w = pP2 + ↑(((padProd x y w).take (p + w)).map (bitSymbol (a := a))).length := by
    simp [List.length_take, hpadlen]; omega
  have t1 := hoare_place (ReturnOrigin.return_hoare_prefix (fun _ => blank) pXs (x.dropLast.map bitSymbol) [bitSymbol (x.getLastD false)] (ReturnOrigin.bits_nonblank _) rfl) E2
    (⟨fun j => if j = 0 then pX else if j = 1 then pY else if j = 2 then pYs else if j = 3 then pP else if j = 4 then pP2 else if j = 5 then pO else if j = 6 then pRp else if j = 7 then pRw else if j = 8 then pR2 else if j = 9 then pF1 else pF2, fun j => if j = 0 then putWord f pX (x.map bitSymbol) else if j = 1 then putWord g pY (y.map bitSymbol) else if j = 2 then putWord (fun _ => blank) pYs ((y).map bitSymbol) else if j = 3 then (fun _ => blank) else if j = 4 then (fun _ => blank) else if j = 5 then (fun _ => blank) else if j = 6 then putWord (fun _ => blank) pRp (ruler p) else if j = 7 then putWord (fun _ => blank) pRw (ruler w) else if j = 8 then putWord (fun _ => blank) pR2 (ruler (2 * w)) else if j = 9 then (fun _ => blank) else (fun _ => blank)⟩ : Tapes 11 a)
  simp only [ReturnOrigin.cfg, Config.tapes] at t1
  rw [E2_bank, E2_bank, ← hxsplit, ← hx1] at t1
  have t2 := hoare_place (Negate.neg_hoare (fun _ => blank) pXs x rfl) E2
    (⟨fun j => if j = 0 then pX else if j = 1 then pY else if j = 2 then pYs else if j = 3 then pP else if j = 4 then pP2 else if j = 5 then pO else if j = 6 then pRp else if j = 7 then pRw else if j = 8 then pR2 else if j = 9 then pF1 else pF2, fun j => if j = 0 then putWord f pX (x.map bitSymbol) else if j = 1 then putWord g pY (y.map bitSymbol) else if j = 2 then putWord (fun _ => blank) pYs ((y).map bitSymbol) else if j = 3 then (fun _ => blank) else if j = 4 then (fun _ => blank) else if j = 5 then (fun _ => blank) else if j = 6 then putWord (fun _ => blank) pRp (ruler p) else if j = 7 then putWord (fun _ => blank) pRw (ruler w) else if j = 8 then putWord (fun _ => blank) pR2 (ruler (2 * w)) else if j = 9 then (fun _ => blank) else (fun _ => blank)⟩ : Tapes 11 a)
  simp only [Negate.cfg, Config.tapes] at t2
  rw [E2_bank, E2_bank, hx] at t2
  have t3 := hoare_place (ReturnOrigin.return_hoare_at (fun _ => blank) pXs ((negWord x).map bitSymbol) (ReturnOrigin.bits_nonblank _) rfl) E2
    (⟨fun j => if j = 0 then pX else if j = 1 then pY else if j = 2 then pYs else if j = 3 then pP else if j = 4 then pP2 else if j = 5 then pO else if j = 6 then pRp else if j = 7 then pRw else if j = 8 then pR2 else if j = 9 then pF1 else pF2, fun j => if j = 0 then putWord f pX (x.map bitSymbol) else if j = 1 then putWord g pY (y.map bitSymbol) else if j = 2 then putWord (fun _ => blank) pYs ((y).map bitSymbol) else if j = 3 then (fun _ => blank) else if j = 4 then (fun _ => blank) else if j = 5 then (fun _ => blank) else if j = 6 then putWord (fun _ => blank) pRp (ruler p) else if j = 7 then putWord (fun _ => blank) pRw (ruler w) else if j = 8 then putWord (fun _ => blank) pR2 (ruler (2 * w)) else if j = 9 then (fun _ => blank) else (fun _ => blank)⟩ : Tapes 11 a)
  simp only [ReturnOrigin.cfg, Config.tapes] at t3
  rw [E2_bank, E2_bank, List.length_map, TwosComplement.negWord_length, hx] at t3
  have t4 := hoare_place (WriteSymbol.write_hoare (bitSymbol true) (fun _ => blank) pF1) E10
    (⟨fun j => if j = 0 then pX else if j = 1 then pY else if j = 2 then pXs else if j = 3 then pYs else if j = 4 then pP else if j = 5 then pP2 else if j = 6 then pO else if j = 7 then pRp else if j = 8 then pRw else if j = 9 then pR2 else pF2, fun j => if j = 0 then putWord f pX (x.map bitSymbol) else if j = 1 then putWord g pY (y.map bitSymbol) else if j = 2 then putWord (fun _ => blank) pXs ((negWord x).map bitSymbol) else if j = 3 then putWord (fun _ => blank) pYs ((y).map bitSymbol) else if j = 4 then (fun _ => blank) else if j = 5 then (fun _ => blank) else if j = 6 then (fun _ => blank) else if j = 7 then putWord (fun _ => blank) pRp (ruler p) else if j = 8 then putWord (fun _ => blank) pRw (ruler w) else if j = 9 then putWord (fun _ => blank) pR2 (ruler (2 * w)) else (fun _ => blank)⟩ : Tapes 11 a)
  simp only [WriteSymbol.cfg, Config.tapes] at t4
  rw [E10_bank, E10_bank, WriteSymbol.update_blank] at t4
  refine ⟨_, (((t1.seq t2).seq t3).seq t4), ?_⟩
  unfold sxTrue_hoareBound
  omega

theorem sxFalse_hoare (x y : List Bool) (p w : ℕ) (f g : ℤ → Fin (a + 4))
    (pX pY pXs pYs pP pP2 pO pRp pRw pR2 pF1 pF2 : ℤ) (hx : x.length = w) (hy : y.length = w)
    (hw : 1 ≤ w) (hpw : p ≤ w) (hfl : f (pX - 1) = blank) (hfr : f (pX + w) = blank)
    (hgl : g (pY - 1) = blank) (hgr : g (pY + w) = blank) :
    ∃ c, HoareTime (sxFalse) (fun v => v = bank (putWord f pX (x.map bitSymbol)) (putWord g pY (y.map bitSymbol)) (putWord (fun _ => blank) pXs ((x).map bitSymbol)) (putWord (fun _ => blank) pYs ((y).map bitSymbol)) ((fun _ => blank)) ((fun _ => blank)) ((fun _ => blank)) (putWord (fun _ => blank) pRp (ruler p)) (putWord (fun _ => blank) pRw (ruler w)) (putWord (fun _ => blank) pR2 (ruler (2 * w))) ((fun _ => blank)) ((fun _ => blank)) (pX) (pY) (pXs + ↑w - 1) (pYs) (pP) (pP2) (pO) (pRp) (pRw) (pR2) (pF1) (pF2))
      (fun v => v = bank (putWord f pX (x.map bitSymbol)) (putWord g pY (y.map bitSymbol)) (putWord (fun _ => blank) pXs ((x).map bitSymbol)) (putWord (fun _ => blank) pYs ((y).map bitSymbol)) ((fun _ => blank)) ((fun _ => blank)) ((fun _ => blank)) (putWord (fun _ => blank) pRp (ruler p)) (putWord (fun _ => blank) pRw (ruler w)) (putWord (fun _ => blank) pR2 (ruler (2 * w))) (putWord (fun _ => blank) pF1 [bitSymbol false]) ((fun _ => blank)) (pX) (pY) (pXs) (pYs) (pP) (pP2) (pO) (pRp) (pRw) (pR2) (pF1) (pF2)) c ∧ c ≤ sxFalse_hoareBound p w := by
  have hx0 : x ≠ [] := by intro h0; rw [h0] at hx; simp at hx; omega
  have hy0 : y ≠ [] := by intro h0; rw [h0] at hy; simp at hy; omega
  have hfr' : f (pX + ↑(x.map (bitSymbol (a := a))).length) = blank := by rw [List.length_map, hx]; exact hfr
  have hgr' : g (pY + ↑(y.map (bitSymbol (a := a))).length) = blank := by rw [List.length_map, hy]; exact hgr
  have hxsplit := map_split (a := a) x hx0
  have hysplit := map_split (a := a) y hy0
  have hx1 : (pXs : ℤ) + ↑w - 1 = pXs + ↑(x.dropLast.map (bitSymbol (a := a))).length := by
    simp [List.length_dropLast, hx]; omega
  have hy1 : (pYs : ℤ) + ↑w - 1 = pYs + ↑(y.dropLast.map (bitSymbol (a := a))).length := by
    simp [List.length_dropLast, hy]; omega
  have hmx : (mag x).length = w := by rw [mag_length, hx]
  have hmy : (mag y).length = w := by rw [mag_length, hy]
  have hhw : (BinaryMultiply.horner (mag x) (mag y)).length ≤ 2 * w := by
    have := BinaryMultiply.horner_length (mag x) (mag y); omega
  have hpadlen : (padProd x y w).length = 2 * w := by simp [padProd]; omega
  have hpad := cells_pad (a := a) pP (BinaryMultiply.horner (mag x) (mag y)) (2 * w) hhw
  have hfield : CopyCells.cells (putWord (fun _ => (blank : Fin (a + 4))) pP2 ((padProd x y w).map bitSymbol)) (pP2 + ↑p) w =
      (Gather.field (padProd x y w) p w).map bitSymbol :=
    cells_field1 _ _ _ _ _ (by omega)
  have hP2split : ((padProd x y w).take (p + w)).map (bitSymbol (a := a)) ++ ((padProd x y w).drop (p + w)).map bitSymbol =
      (padProd x y w).map bitSymbol := by
    rw [← List.map_append, List.take_append_drop]
  have hP2head : (pP2 : ℤ) + ↑p + ↑w = pP2 + ↑(((padProd x y w).take (p + w)).map (bitSymbol (a := a))).length := by
    simp [List.length_take, hpadlen]; omega
  have u1 := hoare_place (ReturnOrigin.return_hoare_prefix (fun _ => blank) pXs (x.dropLast.map bitSymbol) [bitSymbol (x.getLastD false)] (ReturnOrigin.bits_nonblank _) rfl) E2
    (⟨fun j => if j = 0 then pX else if j = 1 then pY else if j = 2 then pYs else if j = 3 then pP else if j = 4 then pP2 else if j = 5 then pO else if j = 6 then pRp else if j = 7 then pRw else if j = 8 then pR2 else if j = 9 then pF1 else pF2, fun j => if j = 0 then putWord f pX (x.map bitSymbol) else if j = 1 then putWord g pY (y.map bitSymbol) else if j = 2 then putWord (fun _ => blank) pYs ((y).map bitSymbol) else if j = 3 then (fun _ => blank) else if j = 4 then (fun _ => blank) else if j = 5 then (fun _ => blank) else if j = 6 then putWord (fun _ => blank) pRp (ruler p) else if j = 7 then putWord (fun _ => blank) pRw (ruler w) else if j = 8 then putWord (fun _ => blank) pR2 (ruler (2 * w)) else if j = 9 then (fun _ => blank) else (fun _ => blank)⟩ : Tapes 11 a)
  simp only [ReturnOrigin.cfg, Config.tapes] at u1
  rw [E2_bank, E2_bank, ← hxsplit, ← hx1] at u1
  have u2 := hoare_place (WriteSymbol.write_hoare (bitSymbol false) (fun _ => blank) pF1) E10
    (⟨fun j => if j = 0 then pX else if j = 1 then pY else if j = 2 then pXs else if j = 3 then pYs else if j = 4 then pP else if j = 5 then pP2 else if j = 6 then pO else if j = 7 then pRp else if j = 8 then pRw else if j = 9 then pR2 else pF2, fun j => if j = 0 then putWord f pX (x.map bitSymbol) else if j = 1 then putWord g pY (y.map bitSymbol) else if j = 2 then putWord (fun _ => blank) pXs ((x).map bitSymbol) else if j = 3 then putWord (fun _ => blank) pYs ((y).map bitSymbol) else if j = 4 then (fun _ => blank) else if j = 5 then (fun _ => blank) else if j = 6 then (fun _ => blank) else if j = 7 then putWord (fun _ => blank) pRp (ruler p) else if j = 8 then putWord (fun _ => blank) pRw (ruler w) else if j = 9 then putWord (fun _ => blank) pR2 (ruler (2 * w)) else (fun _ => blank)⟩ : Tapes 11 a)
  simp only [WriteSymbol.cfg, Config.tapes] at u2
  rw [E10_bank, E10_bank, WriteSymbol.update_blank] at u2
  refine ⟨_, (u1.seq u2), ?_⟩
  unfold sxFalse_hoareBound
  omega

theorem prefix2_hoare (x y : List Bool) (p w : ℕ) (f g : ℤ → Fin (a + 4))
    (pX pY pXs pYs pP pP2 pO pRp pRw pR2 pF1 pF2 : ℤ) (hx : x.length = w) (hy : y.length = w)
    (hw : 1 ≤ w) (hpw : p ≤ w) (hfl : f (pX - 1) = blank) (hfr : f (pX + w) = blank)
    (hgl : g (pY - 1) = blank) (hgr : g (pY + w) = blank) :
    ∃ c, HoareTime (prefix2) (fun v => v = bank (putWord f pX (x.map bitSymbol)) (putWord g pY (y.map bitSymbol)) (putWord (fun _ => blank) pXs ((mag x).map bitSymbol)) (putWord (fun _ => blank) pYs ((y).map bitSymbol)) ((fun _ => blank)) ((fun _ => blank)) ((fun _ => blank)) (putWord (fun _ => blank) pRp (ruler p)) (putWord (fun _ => blank) pRw (ruler w)) (putWord (fun _ => blank) pR2 (ruler (2 * w))) (putWord (fun _ => blank) pF1 [bitSymbol (x.getLastD false)]) ((fun _ => blank)) (pX) (pY) (pXs) (pYs) (pP) (pP2) (pO) (pRp) (pRw) (pR2) (pF1) (pF2))
      (fun v => v = bank (putWord f pX (x.map bitSymbol)) (putWord g pY (y.map bitSymbol)) (putWord (fun _ => blank) pXs ((mag x).map bitSymbol)) (putWord (fun _ => blank) pYs ((y).map bitSymbol)) ((fun _ => blank)) ((fun _ => blank)) ((fun _ => blank)) (putWord (fun _ => blank) pRp (ruler p)) (putWord (fun _ => blank) pRw (ruler w)) (putWord (fun _ => blank) pR2 (ruler (2 * w))) (putWord (fun _ => blank) pF1 [bitSymbol (x.getLastD false)]) ((fun _ => blank)) (pX) (pY) (pXs) (pYs + ↑w - 1) (pP) (pP2) (pO) (pRp) (pRw) (pR2) (pF1) (pF2)) c ∧ c ≤ prefix2_hoareBound p w := by
  have hx0 : x ≠ [] := by intro h0; rw [h0] at hx; simp at hx; omega
  have hy0 : y ≠ [] := by intro h0; rw [h0] at hy; simp at hy; omega
  have hfr' : f (pX + ↑(x.map (bitSymbol (a := a))).length) = blank := by rw [List.length_map, hx]; exact hfr
  have hgr' : g (pY + ↑(y.map (bitSymbol (a := a))).length) = blank := by rw [List.length_map, hy]; exact hgr
  have hxsplit := map_split (a := a) x hx0
  have hysplit := map_split (a := a) y hy0
  have hx1 : (pXs : ℤ) + ↑w - 1 = pXs + ↑(x.dropLast.map (bitSymbol (a := a))).length := by
    simp [List.length_dropLast, hx]; omega
  have hy1 : (pYs : ℤ) + ↑w - 1 = pYs + ↑(y.dropLast.map (bitSymbol (a := a))).length := by
    simp [List.length_dropLast, hy]; omega
  have hmx : (mag x).length = w := by rw [mag_length, hx]
  have hmy : (mag y).length = w := by rw [mag_length, hy]
  have hhw : (BinaryMultiply.horner (mag x) (mag y)).length ≤ 2 * w := by
    have := BinaryMultiply.horner_length (mag x) (mag y); omega
  have hpadlen : (padProd x y w).length = 2 * w := by simp [padProd]; omega
  have hpad := cells_pad (a := a) pP (BinaryMultiply.horner (mag x) (mag y)) (2 * w) hhw
  have hfield : CopyCells.cells (putWord (fun _ => (blank : Fin (a + 4))) pP2 ((padProd x y w).map bitSymbol)) (pP2 + ↑p) w =
      (Gather.field (padProd x y w) p w).map bitSymbol :=
    cells_field1 _ _ _ _ _ (by omega)
  have hP2split : ((padProd x y w).take (p + w)).map (bitSymbol (a := a)) ++ ((padProd x y w).drop (p + w)).map bitSymbol =
      (padProd x y w).map bitSymbol := by
    rw [← List.map_append, List.take_append_drop]
  have hP2head : (pP2 : ℤ) + ↑p + ↑w = pP2 + ↑(((padProd x y w).take (p + w)).map (bitSymbol (a := a))).length := by
    simp [List.length_take, hpadlen]; omega
  have s9 := hoare_place (ScanEnd.scan_hoare (fun _ => blank) pYs ((y).map bitSymbol) (ReturnOrigin.bits_nonblank _) rfl) E3
    (⟨fun j => if j = 0 then pX else if j = 1 then pY else if j = 2 then pXs else if j = 3 then pP else if j = 4 then pP2 else if j = 5 then pO else if j = 6 then pRp else if j = 7 then pRw else if j = 8 then pR2 else if j = 9 then pF1 else pF2, fun j => if j = 0 then putWord f pX (x.map bitSymbol) else if j = 1 then putWord g pY (y.map bitSymbol) else if j = 2 then putWord (fun _ => blank) pXs ((mag x).map bitSymbol) else if j = 3 then (fun _ => blank) else if j = 4 then (fun _ => blank) else if j = 5 then (fun _ => blank) else if j = 6 then putWord (fun _ => blank) pRp (ruler p) else if j = 7 then putWord (fun _ => blank) pRw (ruler w) else if j = 8 then putWord (fun _ => blank) pR2 (ruler (2 * w)) else if j = 9 then putWord (fun _ => blank) pF1 [bitSymbol (x.getLastD false)] else (fun _ => blank)⟩ : Tapes 11 a)
  simp only [ScanEnd.cfg, Config.tapes] at s9
  rw [E3_bank, E3_bank, List.length_map, hy] at s9
  have s10 := hoare_place (StepLeft.step_hoare (putWord (fun _ => blank) pYs (y.map bitSymbol)) (pYs + ↑w)) E3
    (⟨fun j => if j = 0 then pX else if j = 1 then pY else if j = 2 then pXs else if j = 3 then pP else if j = 4 then pP2 else if j = 5 then pO else if j = 6 then pRp else if j = 7 then pRw else if j = 8 then pR2 else if j = 9 then pF1 else pF2, fun j => if j = 0 then putWord f pX (x.map bitSymbol) else if j = 1 then putWord g pY (y.map bitSymbol) else if j = 2 then putWord (fun _ => blank) pXs ((mag x).map bitSymbol) else if j = 3 then (fun _ => blank) else if j = 4 then (fun _ => blank) else if j = 5 then (fun _ => blank) else if j = 6 then putWord (fun _ => blank) pRp (ruler p) else if j = 7 then putWord (fun _ => blank) pRw (ruler w) else if j = 8 then putWord (fun _ => blank) pR2 (ruler (2 * w)) else if j = 9 then putWord (fun _ => blank) pF1 [bitSymbol (x.getLastD false)] else (fun _ => blank)⟩ : Tapes 11 a)
  simp only [StepLeft.cfg, Config.tapes] at s10
  rw [E3_bank, E3_bank] at s10
  refine ⟨_, (s9.seq s10), ?_⟩
  unfold prefix2_hoareBound
  omega

theorem syTrue_hoare (x y : List Bool) (p w : ℕ) (f g : ℤ → Fin (a + 4))
    (pX pY pXs pYs pP pP2 pO pRp pRw pR2 pF1 pF2 : ℤ) (hx : x.length = w) (hy : y.length = w)
    (hw : 1 ≤ w) (hpw : p ≤ w) (hfl : f (pX - 1) = blank) (hfr : f (pX + w) = blank)
    (hgl : g (pY - 1) = blank) (hgr : g (pY + w) = blank) :
    ∃ c, HoareTime (syTrue) (fun v => v = bank (putWord f pX (x.map bitSymbol)) (putWord g pY (y.map bitSymbol)) (putWord (fun _ => blank) pXs ((mag x).map bitSymbol)) (putWord (fun _ => blank) pYs ((y).map bitSymbol)) ((fun _ => blank)) ((fun _ => blank)) ((fun _ => blank)) (putWord (fun _ => blank) pRp (ruler p)) (putWord (fun _ => blank) pRw (ruler w)) (putWord (fun _ => blank) pR2 (ruler (2 * w))) (putWord (fun _ => blank) pF1 [bitSymbol (x.getLastD false)]) ((fun _ => blank)) (pX) (pY) (pXs) (pYs + ↑w - 1) (pP) (pP2) (pO) (pRp) (pRw) (pR2) (pF1) (pF2))
      (fun v => v = bank (putWord f pX (x.map bitSymbol)) (putWord g pY (y.map bitSymbol)) (putWord (fun _ => blank) pXs ((mag x).map bitSymbol)) (putWord (fun _ => blank) pYs ((negWord y).map bitSymbol)) ((fun _ => blank)) ((fun _ => blank)) ((fun _ => blank)) (putWord (fun _ => blank) pRp (ruler p)) (putWord (fun _ => blank) pRw (ruler w)) (putWord (fun _ => blank) pR2 (ruler (2 * w))) (putWord (fun _ => blank) pF1 [bitSymbol (x.getLastD false)]) (putWord (fun _ => blank) pF2 [bitSymbol true]) (pX) (pY) (pXs) (pYs) (pP) (pP2) (pO) (pRp) (pRw) (pR2) (pF1) (pF2)) c ∧ c ≤ syTrue_hoareBound p w := by
  have hx0 : x ≠ [] := by intro h0; rw [h0] at hx; simp at hx; omega
  have hy0 : y ≠ [] := by intro h0; rw [h0] at hy; simp at hy; omega
  have hfr' : f (pX + ↑(x.map (bitSymbol (a := a))).length) = blank := by rw [List.length_map, hx]; exact hfr
  have hgr' : g (pY + ↑(y.map (bitSymbol (a := a))).length) = blank := by rw [List.length_map, hy]; exact hgr
  have hxsplit := map_split (a := a) x hx0
  have hysplit := map_split (a := a) y hy0
  have hx1 : (pXs : ℤ) + ↑w - 1 = pXs + ↑(x.dropLast.map (bitSymbol (a := a))).length := by
    simp [List.length_dropLast, hx]; omega
  have hy1 : (pYs : ℤ) + ↑w - 1 = pYs + ↑(y.dropLast.map (bitSymbol (a := a))).length := by
    simp [List.length_dropLast, hy]; omega
  have hmx : (mag x).length = w := by rw [mag_length, hx]
  have hmy : (mag y).length = w := by rw [mag_length, hy]
  have hhw : (BinaryMultiply.horner (mag x) (mag y)).length ≤ 2 * w := by
    have := BinaryMultiply.horner_length (mag x) (mag y); omega
  have hpadlen : (padProd x y w).length = 2 * w := by simp [padProd]; omega
  have hpad := cells_pad (a := a) pP (BinaryMultiply.horner (mag x) (mag y)) (2 * w) hhw
  have hfield : CopyCells.cells (putWord (fun _ => (blank : Fin (a + 4))) pP2 ((padProd x y w).map bitSymbol)) (pP2 + ↑p) w =
      (Gather.field (padProd x y w) p w).map bitSymbol :=
    cells_field1 _ _ _ _ _ (by omega)
  have hP2split : ((padProd x y w).take (p + w)).map (bitSymbol (a := a)) ++ ((padProd x y w).drop (p + w)).map bitSymbol =
      (padProd x y w).map bitSymbol := by
    rw [← List.map_append, List.take_append_drop]
  have hP2head : (pP2 : ℤ) + ↑p + ↑w = pP2 + ↑(((padProd x y w).take (p + w)).map (bitSymbol (a := a))).length := by
    simp [List.length_take, hpadlen]; omega
  have v1 := hoare_place (ReturnOrigin.return_hoare_prefix (fun _ => blank) pYs (y.dropLast.map bitSymbol) [bitSymbol (y.getLastD false)] (ReturnOrigin.bits_nonblank _) rfl) E3
    (⟨fun j => if j = 0 then pX else if j = 1 then pY else if j = 2 then pXs else if j = 3 then pP else if j = 4 then pP2 else if j = 5 then pO else if j = 6 then pRp else if j = 7 then pRw else if j = 8 then pR2 else if j = 9 then pF1 else pF2, fun j => if j = 0 then putWord f pX (x.map bitSymbol) else if j = 1 then putWord g pY (y.map bitSymbol) else if j = 2 then putWord (fun _ => blank) pXs ((mag x).map bitSymbol) else if j = 3 then (fun _ => blank) else if j = 4 then (fun _ => blank) else if j = 5 then (fun _ => blank) else if j = 6 then putWord (fun _ => blank) pRp (ruler p) else if j = 7 then putWord (fun _ => blank) pRw (ruler w) else if j = 8 then putWord (fun _ => blank) pR2 (ruler (2 * w)) else if j = 9 then putWord (fun _ => blank) pF1 [bitSymbol (x.getLastD false)] else (fun _ => blank)⟩ : Tapes 11 a)
  simp only [ReturnOrigin.cfg, Config.tapes] at v1
  rw [E3_bank, E3_bank, ← hysplit, ← hy1] at v1
  have v2 := hoare_place (Negate.neg_hoare (fun _ => blank) pYs y rfl) E3
    (⟨fun j => if j = 0 then pX else if j = 1 then pY else if j = 2 then pXs else if j = 3 then pP else if j = 4 then pP2 else if j = 5 then pO else if j = 6 then pRp else if j = 7 then pRw else if j = 8 then pR2 else if j = 9 then pF1 else pF2, fun j => if j = 0 then putWord f pX (x.map bitSymbol) else if j = 1 then putWord g pY (y.map bitSymbol) else if j = 2 then putWord (fun _ => blank) pXs ((mag x).map bitSymbol) else if j = 3 then (fun _ => blank) else if j = 4 then (fun _ => blank) else if j = 5 then (fun _ => blank) else if j = 6 then putWord (fun _ => blank) pRp (ruler p) else if j = 7 then putWord (fun _ => blank) pRw (ruler w) else if j = 8 then putWord (fun _ => blank) pR2 (ruler (2 * w)) else if j = 9 then putWord (fun _ => blank) pF1 [bitSymbol (x.getLastD false)] else (fun _ => blank)⟩ : Tapes 11 a)
  simp only [Negate.cfg, Config.tapes] at v2
  rw [E3_bank, E3_bank, hy] at v2
  have v3 := hoare_place (ReturnOrigin.return_hoare_at (fun _ => blank) pYs ((negWord y).map bitSymbol) (ReturnOrigin.bits_nonblank _) rfl) E3
    (⟨fun j => if j = 0 then pX else if j = 1 then pY else if j = 2 then pXs else if j = 3 then pP else if j = 4 then pP2 else if j = 5 then pO else if j = 6 then pRp else if j = 7 then pRw else if j = 8 then pR2 else if j = 9 then pF1 else pF2, fun j => if j = 0 then putWord f pX (x.map bitSymbol) else if j = 1 then putWord g pY (y.map bitSymbol) else if j = 2 then putWord (fun _ => blank) pXs ((mag x).map bitSymbol) else if j = 3 then (fun _ => blank) else if j = 4 then (fun _ => blank) else if j = 5 then (fun _ => blank) else if j = 6 then putWord (fun _ => blank) pRp (ruler p) else if j = 7 then putWord (fun _ => blank) pRw (ruler w) else if j = 8 then putWord (fun _ => blank) pR2 (ruler (2 * w)) else if j = 9 then putWord (fun _ => blank) pF1 [bitSymbol (x.getLastD false)] else (fun _ => blank)⟩ : Tapes 11 a)
  simp only [ReturnOrigin.cfg, Config.tapes] at v3
  rw [E3_bank, E3_bank, List.length_map, TwosComplement.negWord_length, hy] at v3
  have v4 := hoare_place (WriteSymbol.write_hoare (bitSymbol true) (fun _ => blank) pF2) E11
    (⟨fun j => if j = 0 then pX else if j = 1 then pY else if j = 2 then pXs else if j = 3 then pYs else if j = 4 then pP else if j = 5 then pP2 else if j = 6 then pO else if j = 7 then pRp else if j = 8 then pRw else if j = 9 then pR2 else pF1, fun j => if j = 0 then putWord f pX (x.map bitSymbol) else if j = 1 then putWord g pY (y.map bitSymbol) else if j = 2 then putWord (fun _ => blank) pXs ((mag x).map bitSymbol) else if j = 3 then putWord (fun _ => blank) pYs ((negWord y).map bitSymbol) else if j = 4 then (fun _ => blank) else if j = 5 then (fun _ => blank) else if j = 6 then (fun _ => blank) else if j = 7 then putWord (fun _ => blank) pRp (ruler p) else if j = 8 then putWord (fun _ => blank) pRw (ruler w) else if j = 9 then putWord (fun _ => blank) pR2 (ruler (2 * w)) else putWord (fun _ => blank) pF1 [bitSymbol (x.getLastD false)]⟩ : Tapes 11 a)
  simp only [WriteSymbol.cfg, Config.tapes] at v4
  rw [E11_bank, E11_bank, WriteSymbol.update_blank] at v4
  refine ⟨_, (((v1.seq v2).seq v3).seq v4), ?_⟩
  unfold syTrue_hoareBound
  omega

theorem syFalse_hoare (x y : List Bool) (p w : ℕ) (f g : ℤ → Fin (a + 4))
    (pX pY pXs pYs pP pP2 pO pRp pRw pR2 pF1 pF2 : ℤ) (hx : x.length = w) (hy : y.length = w)
    (hw : 1 ≤ w) (hpw : p ≤ w) (hfl : f (pX - 1) = blank) (hfr : f (pX + w) = blank)
    (hgl : g (pY - 1) = blank) (hgr : g (pY + w) = blank) :
    ∃ c, HoareTime (syFalse) (fun v => v = bank (putWord f pX (x.map bitSymbol)) (putWord g pY (y.map bitSymbol)) (putWord (fun _ => blank) pXs ((mag x).map bitSymbol)) (putWord (fun _ => blank) pYs ((y).map bitSymbol)) ((fun _ => blank)) ((fun _ => blank)) ((fun _ => blank)) (putWord (fun _ => blank) pRp (ruler p)) (putWord (fun _ => blank) pRw (ruler w)) (putWord (fun _ => blank) pR2 (ruler (2 * w))) (putWord (fun _ => blank) pF1 [bitSymbol (x.getLastD false)]) ((fun _ => blank)) (pX) (pY) (pXs) (pYs + ↑w - 1) (pP) (pP2) (pO) (pRp) (pRw) (pR2) (pF1) (pF2))
      (fun v => v = bank (putWord f pX (x.map bitSymbol)) (putWord g pY (y.map bitSymbol)) (putWord (fun _ => blank) pXs ((mag x).map bitSymbol)) (putWord (fun _ => blank) pYs ((y).map bitSymbol)) ((fun _ => blank)) ((fun _ => blank)) ((fun _ => blank)) (putWord (fun _ => blank) pRp (ruler p)) (putWord (fun _ => blank) pRw (ruler w)) (putWord (fun _ => blank) pR2 (ruler (2 * w))) (putWord (fun _ => blank) pF1 [bitSymbol (x.getLastD false)]) (putWord (fun _ => blank) pF2 [bitSymbol false]) (pX) (pY) (pXs) (pYs) (pP) (pP2) (pO) (pRp) (pRw) (pR2) (pF1) (pF2)) c ∧ c ≤ syFalse_hoareBound p w := by
  have hx0 : x ≠ [] := by intro h0; rw [h0] at hx; simp at hx; omega
  have hy0 : y ≠ [] := by intro h0; rw [h0] at hy; simp at hy; omega
  have hfr' : f (pX + ↑(x.map (bitSymbol (a := a))).length) = blank := by rw [List.length_map, hx]; exact hfr
  have hgr' : g (pY + ↑(y.map (bitSymbol (a := a))).length) = blank := by rw [List.length_map, hy]; exact hgr
  have hxsplit := map_split (a := a) x hx0
  have hysplit := map_split (a := a) y hy0
  have hx1 : (pXs : ℤ) + ↑w - 1 = pXs + ↑(x.dropLast.map (bitSymbol (a := a))).length := by
    simp [List.length_dropLast, hx]; omega
  have hy1 : (pYs : ℤ) + ↑w - 1 = pYs + ↑(y.dropLast.map (bitSymbol (a := a))).length := by
    simp [List.length_dropLast, hy]; omega
  have hmx : (mag x).length = w := by rw [mag_length, hx]
  have hmy : (mag y).length = w := by rw [mag_length, hy]
  have hhw : (BinaryMultiply.horner (mag x) (mag y)).length ≤ 2 * w := by
    have := BinaryMultiply.horner_length (mag x) (mag y); omega
  have hpadlen : (padProd x y w).length = 2 * w := by simp [padProd]; omega
  have hpad := cells_pad (a := a) pP (BinaryMultiply.horner (mag x) (mag y)) (2 * w) hhw
  have hfield : CopyCells.cells (putWord (fun _ => (blank : Fin (a + 4))) pP2 ((padProd x y w).map bitSymbol)) (pP2 + ↑p) w =
      (Gather.field (padProd x y w) p w).map bitSymbol :=
    cells_field1 _ _ _ _ _ (by omega)
  have hP2split : ((padProd x y w).take (p + w)).map (bitSymbol (a := a)) ++ ((padProd x y w).drop (p + w)).map bitSymbol =
      (padProd x y w).map bitSymbol := by
    rw [← List.map_append, List.take_append_drop]
  have hP2head : (pP2 : ℤ) + ↑p + ↑w = pP2 + ↑(((padProd x y w).take (p + w)).map (bitSymbol (a := a))).length := by
    simp [List.length_take, hpadlen]; omega
  have w1 := hoare_place (ReturnOrigin.return_hoare_prefix (fun _ => blank) pYs (y.dropLast.map bitSymbol) [bitSymbol (y.getLastD false)] (ReturnOrigin.bits_nonblank _) rfl) E3
    (⟨fun j => if j = 0 then pX else if j = 1 then pY else if j = 2 then pXs else if j = 3 then pP else if j = 4 then pP2 else if j = 5 then pO else if j = 6 then pRp else if j = 7 then pRw else if j = 8 then pR2 else if j = 9 then pF1 else pF2, fun j => if j = 0 then putWord f pX (x.map bitSymbol) else if j = 1 then putWord g pY (y.map bitSymbol) else if j = 2 then putWord (fun _ => blank) pXs ((mag x).map bitSymbol) else if j = 3 then (fun _ => blank) else if j = 4 then (fun _ => blank) else if j = 5 then (fun _ => blank) else if j = 6 then putWord (fun _ => blank) pRp (ruler p) else if j = 7 then putWord (fun _ => blank) pRw (ruler w) else if j = 8 then putWord (fun _ => blank) pR2 (ruler (2 * w)) else if j = 9 then putWord (fun _ => blank) pF1 [bitSymbol (x.getLastD false)] else (fun _ => blank)⟩ : Tapes 11 a)
  simp only [ReturnOrigin.cfg, Config.tapes] at w1
  rw [E3_bank, E3_bank, ← hysplit, ← hy1] at w1
  have w2 := hoare_place (WriteSymbol.write_hoare (bitSymbol false) (fun _ => blank) pF2) E11
    (⟨fun j => if j = 0 then pX else if j = 1 then pY else if j = 2 then pXs else if j = 3 then pYs else if j = 4 then pP else if j = 5 then pP2 else if j = 6 then pO else if j = 7 then pRp else if j = 8 then pRw else if j = 9 then pR2 else pF1, fun j => if j = 0 then putWord f pX (x.map bitSymbol) else if j = 1 then putWord g pY (y.map bitSymbol) else if j = 2 then putWord (fun _ => blank) pXs ((mag x).map bitSymbol) else if j = 3 then putWord (fun _ => blank) pYs ((y).map bitSymbol) else if j = 4 then (fun _ => blank) else if j = 5 then (fun _ => blank) else if j = 6 then (fun _ => blank) else if j = 7 then putWord (fun _ => blank) pRp (ruler p) else if j = 8 then putWord (fun _ => blank) pRw (ruler w) else if j = 9 then putWord (fun _ => blank) pR2 (ruler (2 * w)) else putWord (fun _ => blank) pF1 [bitSymbol (x.getLastD false)]⟩ : Tapes 11 a)
  simp only [WriteSymbol.cfg, Config.tapes] at w2
  rw [E11_bank, E11_bank, WriteSymbol.update_blank] at w2
  refine ⟨_, (w1.seq w2), ?_⟩
  unfold syFalse_hoareBound
  omega

theorem core_hoare (x y : List Bool) (p w : ℕ) (f g : ℤ → Fin (a + 4))
    (pX pY pXs pYs pP pP2 pO pRp pRw pR2 pF1 pF2 : ℤ) (hx : x.length = w) (hy : y.length = w)
    (hw : 1 ≤ w) (hpw : p ≤ w) (hfl : f (pX - 1) = blank) (hfr : f (pX + w) = blank)
    (hgl : g (pY - 1) = blank) (hgr : g (pY + w) = blank) :
    ∃ c, HoareTime (core) (fun v => v = bank (putWord f pX (x.map bitSymbol)) (putWord g pY (y.map bitSymbol)) (putWord (fun _ => blank) pXs ((mag x).map bitSymbol)) (putWord (fun _ => blank) pYs ((mag y).map bitSymbol)) ((fun _ => blank)) ((fun _ => blank)) ((fun _ => blank)) (putWord (fun _ => blank) pRp (ruler p)) (putWord (fun _ => blank) pRw (ruler w)) (putWord (fun _ => blank) pR2 (ruler (2 * w))) (putWord (fun _ => blank) pF1 [bitSymbol (x.getLastD false)]) (putWord (fun _ => blank) pF2 [bitSymbol (y.getLastD false)]) (pX) (pY) (pXs) (pYs) (pP) (pP2) (pO) (pRp) (pRw) (pR2) (pF1) (pF2))
      (fun v => v = bank (putWord f pX (x.map bitSymbol)) (putWord g pY (y.map bitSymbol)) ((fun _ => blank)) ((fun _ => blank)) ((fun _ => blank)) ((fun _ => blank)) (putWord (fun _ => blank) pO ((Gather.field (padProd x y w) p w).map bitSymbol)) (putWord (fun _ => blank) pRp (ruler p)) (putWord (fun _ => blank) pRw (ruler w)) (putWord (fun _ => blank) pR2 (ruler (2 * w))) (putWord (fun _ => blank) pF1 [bitSymbol (x.getLastD false)]) (putWord (fun _ => blank) pF2 [bitSymbol (y.getLastD false)]) (pX) (pY) (pXs) (pYs) (pP) (pP2) (pO) (pRp) (pRw) (pR2) (pF1) (pF2)) c ∧ c ≤ core_hoareBound p w := by
  have hx0 : x ≠ [] := by intro h0; rw [h0] at hx; simp at hx; omega
  have hy0 : y ≠ [] := by intro h0; rw [h0] at hy; simp at hy; omega
  have hfr' : f (pX + ↑(x.map (bitSymbol (a := a))).length) = blank := by rw [List.length_map, hx]; exact hfr
  have hgr' : g (pY + ↑(y.map (bitSymbol (a := a))).length) = blank := by rw [List.length_map, hy]; exact hgr
  have hxsplit := map_split (a := a) x hx0
  have hysplit := map_split (a := a) y hy0
  have hx1 : (pXs : ℤ) + ↑w - 1 = pXs + ↑(x.dropLast.map (bitSymbol (a := a))).length := by
    simp [List.length_dropLast, hx]; omega
  have hy1 : (pYs : ℤ) + ↑w - 1 = pYs + ↑(y.dropLast.map (bitSymbol (a := a))).length := by
    simp [List.length_dropLast, hy]; omega
  have hmx : (mag x).length = w := by rw [mag_length, hx]
  have hmy : (mag y).length = w := by rw [mag_length, hy]
  have hhw : (BinaryMultiply.horner (mag x) (mag y)).length ≤ 2 * w := by
    have := BinaryMultiply.horner_length (mag x) (mag y); omega
  have hpadlen : (padProd x y w).length = 2 * w := by simp [padProd]; omega
  have hpad := cells_pad (a := a) pP (BinaryMultiply.horner (mag x) (mag y)) (2 * w) hhw
  have hfield : CopyCells.cells (putWord (fun _ => (blank : Fin (a + 4))) pP2 ((padProd x y w).map bitSymbol)) (pP2 + ↑p) w =
      (Gather.field (padProd x y w) p w).map bitSymbol :=
    cells_field1 _ _ _ _ _ (by omega)
  have hP2split : ((padProd x y w).take (p + w)).map (bitSymbol (a := a)) ++ ((padProd x y w).drop (p + w)).map bitSymbol =
      (padProd x y w).map bitSymbol := by
    rw [← List.map_append, List.take_append_drop]
  have hP2head : (pP2 : ℤ) + ↑p + ↑w = pP2 + ↑(((padProd x y w).take (p + w)).map (bitSymbol (a := a))).length := by
    simp [List.length_take, hpadlen]; omega
  have hmul := BinaryMultiply.cost_le (mag x) (mag y)
  rw [hmx, hmy] at hmul
  have hhw' := BinaryMultiply.horner_length (mag x) (mag y)
  rw [hmx, hmy] at hhw'
  have c1 := hoare_place (RulerAdvance.advance_hoare (fun _ => blank) (fun _ => blank) pRw pP (ruler w) (ruler_nonblank _) rfl) E8_4
    (⟨fun j => if j = 0 then pX else if j = 1 then pY else if j = 2 then pXs else if j = 3 then pYs else if j = 4 then pP2 else if j = 5 then pO else if j = 6 then pRp else if j = 7 then pR2 else if j = 8 then pF1 else pF2, fun j => if j = 0 then putWord f pX (x.map bitSymbol) else if j = 1 then putWord g pY (y.map bitSymbol) else if j = 2 then putWord (fun _ => blank) pXs ((mag x).map bitSymbol) else if j = 3 then putWord (fun _ => blank) pYs ((mag y).map bitSymbol) else if j = 4 then (fun _ => blank) else if j = 5 then (fun _ => blank) else if j = 6 then putWord (fun _ => blank) pRp (ruler p) else if j = 7 then putWord (fun _ => blank) pR2 (ruler (2 * w)) else if j = 8 then putWord (fun _ => blank) pF1 [bitSymbol (x.getLastD false)] else putWord (fun _ => blank) pF2 [bitSymbol (y.getLastD false)]⟩ : Tapes 10 a)
  simp only [RulerAdvance.cfg, Config.tapes] at c1
  rw [E8_4_bank, E8_4_bank, ruler_length] at c1
  have c2 := hoare_place (ReturnOrigin.return_hoare_at (fun _ => blank) pRw (ruler w) (ruler_nonblank _) rfl) E8
    (⟨fun j => if j = 0 then pX else if j = 1 then pY else if j = 2 then pXs else if j = 3 then pYs else if j = 4 then pP + ↑w else if j = 5 then pP2 else if j = 6 then pO else if j = 7 then pRp else if j = 8 then pR2 else if j = 9 then pF1 else pF2, fun j => if j = 0 then putWord f pX (x.map bitSymbol) else if j = 1 then putWord g pY (y.map bitSymbol) else if j = 2 then putWord (fun _ => blank) pXs ((mag x).map bitSymbol) else if j = 3 then putWord (fun _ => blank) pYs ((mag y).map bitSymbol) else if j = 4 then (fun _ => blank) else if j = 5 then (fun _ => blank) else if j = 6 then (fun _ => blank) else if j = 7 then putWord (fun _ => blank) pRp (ruler p) else if j = 8 then putWord (fun _ => blank) pR2 (ruler (2 * w)) else if j = 9 then putWord (fun _ => blank) pF1 [bitSymbol (x.getLastD false)] else putWord (fun _ => blank) pF2 [bitSymbol (y.getLastD false)]⟩ : Tapes 11 a)
  simp only [ReturnOrigin.cfg, Config.tapes] at c2
  rw [E8_bank, E8_bank, ruler_length] at c2
  have c3 := hoare_place (ScanEnd.scan_hoare (fun _ => blank) pYs ((mag y).map bitSymbol) (ReturnOrigin.bits_nonblank _) rfl) E3
    (⟨fun j => if j = 0 then pX else if j = 1 then pY else if j = 2 then pXs else if j = 3 then pP + ↑w else if j = 4 then pP2 else if j = 5 then pO else if j = 6 then pRp else if j = 7 then pRw else if j = 8 then pR2 else if j = 9 then pF1 else pF2, fun j => if j = 0 then putWord f pX (x.map bitSymbol) else if j = 1 then putWord g pY (y.map bitSymbol) else if j = 2 then putWord (fun _ => blank) pXs ((mag x).map bitSymbol) else if j = 3 then (fun _ => blank) else if j = 4 then (fun _ => blank) else if j = 5 then (fun _ => blank) else if j = 6 then putWord (fun _ => blank) pRp (ruler p) else if j = 7 then putWord (fun _ => blank) pRw (ruler w) else if j = 8 then putWord (fun _ => blank) pR2 (ruler (2 * w)) else if j = 9 then putWord (fun _ => blank) pF1 [bitSymbol (x.getLastD false)] else putWord (fun _ => blank) pF2 [bitSymbol (y.getLastD false)]⟩ : Tapes 11 a)
  simp only [ScanEnd.cfg, Config.tapes] at c3
  rw [E3_bank, E3_bank, List.length_map, hmy] at c3
  have c4 := hoare_place (StepLeft.step_hoare (putWord (fun _ => blank) pYs ((mag y).map bitSymbol)) (pYs + ↑w)) E3
    (⟨fun j => if j = 0 then pX else if j = 1 then pY else if j = 2 then pXs else if j = 3 then pP + ↑w else if j = 4 then pP2 else if j = 5 then pO else if j = 6 then pRp else if j = 7 then pRw else if j = 8 then pR2 else if j = 9 then pF1 else pF2, fun j => if j = 0 then putWord f pX (x.map bitSymbol) else if j = 1 then putWord g pY (y.map bitSymbol) else if j = 2 then putWord (fun _ => blank) pXs ((mag x).map bitSymbol) else if j = 3 then (fun _ => blank) else if j = 4 then (fun _ => blank) else if j = 5 then (fun _ => blank) else if j = 6 then putWord (fun _ => blank) pRp (ruler p) else if j = 7 then putWord (fun _ => blank) pRw (ruler w) else if j = 8 then putWord (fun _ => blank) pR2 (ruler (2 * w)) else if j = 9 then putWord (fun _ => blank) pF1 [bitSymbol (x.getLastD false)] else putWord (fun _ => blank) pF2 [bitSymbol (y.getLastD false)]⟩ : Tapes 11 a)
  simp only [StepLeft.cfg, Config.tapes] at c4
  rw [E3_bank, E3_bank] at c4
  have c5 := hoare_place (BinaryMultiply.multiply_hoare (mag x) (mag y) (fun _ => blank) (fun _ => blank) pXs pYs (pP + ↑w) rfl rfl rfl) E2_3_4
    (⟨fun j => if j = 0 then pX else if j = 1 then pY else if j = 2 then pP2 else if j = 3 then pO else if j = 4 then pRp else if j = 5 then pRw else if j = 6 then pR2 else if j = 7 then pF1 else pF2, fun j => if j = 0 then putWord f pX (x.map bitSymbol) else if j = 1 then putWord g pY (y.map bitSymbol) else if j = 2 then (fun _ => blank) else if j = 3 then (fun _ => blank) else if j = 4 then putWord (fun _ => blank) pRp (ruler p) else if j = 5 then putWord (fun _ => blank) pRw (ruler w) else if j = 6 then putWord (fun _ => blank) pR2 (ruler (2 * w)) else if j = 7 then putWord (fun _ => blank) pF1 [bitSymbol (x.getLastD false)] else putWord (fun _ => blank) pF2 [bitSymbol (y.getLastD false)]⟩ : Tapes 9 a)
  rw [hmy, E2_3_4_bank, E2_3_4_bank] at c5
  rw [add_sub_cancel_right] at c5
  have c6 := hoare_place (StepRight.step_hoare (putWord (fun _ => blank) pYs ((mag y).map bitSymbol)) (pYs - 1)) E3
    (⟨fun j => if j = 0 then pX else if j = 1 then pY else if j = 2 then pXs else if j = 3 then pP else if j = 4 then pP2 else if j = 5 then pO else if j = 6 then pRp else if j = 7 then pRw else if j = 8 then pR2 else if j = 9 then pF1 else pF2, fun j => if j = 0 then putWord f pX (x.map bitSymbol) else if j = 1 then putWord g pY (y.map bitSymbol) else if j = 2 then putWord (fun _ => blank) pXs ((mag x).map bitSymbol) else if j = 3 then putWord (fun _ => blank) pP ((BinaryMultiply.horner (mag x) (mag y)).map bitSymbol) else if j = 4 then (fun _ => blank) else if j = 5 then (fun _ => blank) else if j = 6 then putWord (fun _ => blank) pRp (ruler p) else if j = 7 then putWord (fun _ => blank) pRw (ruler w) else if j = 8 then putWord (fun _ => blank) pR2 (ruler (2 * w)) else if j = 9 then putWord (fun _ => blank) pF1 [bitSymbol (x.getLastD false)] else putWord (fun _ => blank) pF2 [bitSymbol (y.getLastD false)]⟩ : Tapes 11 a)
  simp only [StepRight.cfg, Config.tapes] at c6
  rw [E3_bank, E3_bank, sub_add_cancel] at c6
  have c7 := hoare_place (RulerCopy.copy_hoare (fun _ => blank) (putWord (fun _ => blank) pP ((BinaryMultiply.horner (mag x) (mag y)).map bitSymbol)) (fun _ => blank) pR2 pP pP2 (ruler (2 * w)) (ruler_nonblank _) rfl) E9_4_5
    (⟨fun j => if j = 0 then pX else if j = 1 then pY else if j = 2 then pXs else if j = 3 then pYs else if j = 4 then pO else if j = 5 then pRp else if j = 6 then pRw else if j = 7 then pF1 else pF2, fun j => if j = 0 then putWord f pX (x.map bitSymbol) else if j = 1 then putWord g pY (y.map bitSymbol) else if j = 2 then putWord (fun _ => blank) pXs ((mag x).map bitSymbol) else if j = 3 then putWord (fun _ => blank) pYs ((mag y).map bitSymbol) else if j = 4 then (fun _ => blank) else if j = 5 then putWord (fun _ => blank) pRp (ruler p) else if j = 6 then putWord (fun _ => blank) pRw (ruler w) else if j = 7 then putWord (fun _ => blank) pF1 [bitSymbol (x.getLastD false)] else putWord (fun _ => blank) pF2 [bitSymbol (y.getLastD false)]⟩ : Tapes 9 a)
  simp only [RulerCopy.cfg, Config.tapes] at c7
  rw [E9_4_5_bank, E9_4_5_bank, ruler_length, hpad] at c7
  have c8 := hoare_place (RulerRetreat.retreat_hoare (fun _ => blank) (putWord (fun _ => blank) pP ((BinaryMultiply.horner (mag x) (mag y)).map bitSymbol)) pR2 pP (ruler (2 * w)) (ruler_nonblank _) rfl) E9_4
    (⟨fun j => if j = 0 then pX else if j = 1 then pY else if j = 2 then pXs else if j = 3 then pYs else if j = 4 then pP2 + ↑(2 * w) else if j = 5 then pO else if j = 6 then pRp else if j = 7 then pRw else if j = 8 then pF1 else pF2, fun j => if j = 0 then putWord f pX (x.map bitSymbol) else if j = 1 then putWord g pY (y.map bitSymbol) else if j = 2 then putWord (fun _ => blank) pXs ((mag x).map bitSymbol) else if j = 3 then putWord (fun _ => blank) pYs ((mag y).map bitSymbol) else if j = 4 then putWord (fun _ => blank) pP2 ((padProd x y w).map bitSymbol) else if j = 5 then (fun _ => blank) else if j = 6 then putWord (fun _ => blank) pRp (ruler p) else if j = 7 then putWord (fun _ => blank) pRw (ruler w) else if j = 8 then putWord (fun _ => blank) pF1 [bitSymbol (x.getLastD false)] else putWord (fun _ => blank) pF2 [bitSymbol (y.getLastD false)]⟩ : Tapes 10 a)
  simp only [RulerRetreat.cfg, Config.tapes] at c8
  rw [E9_4_bank, E9_4_bank, ruler_length] at c8
  have c9 := hoare_place (ReturnOrigin.return_hoare_at (fun _ => blank) pP2 ((padProd x y w).map bitSymbol) (ReturnOrigin.bits_nonblank _) rfl) E5
    (⟨fun j => if j = 0 then pX else if j = 1 then pY else if j = 2 then pXs else if j = 3 then pYs else if j = 4 then pP else if j = 5 then pO else if j = 6 then pRp else if j = 7 then pRw else if j = 8 then pR2 else if j = 9 then pF1 else pF2, fun j => if j = 0 then putWord f pX (x.map bitSymbol) else if j = 1 then putWord g pY (y.map bitSymbol) else if j = 2 then putWord (fun _ => blank) pXs ((mag x).map bitSymbol) else if j = 3 then putWord (fun _ => blank) pYs ((mag y).map bitSymbol) else if j = 4 then putWord (fun _ => blank) pP ((BinaryMultiply.horner (mag x) (mag y)).map bitSymbol) else if j = 5 then (fun _ => blank) else if j = 6 then putWord (fun _ => blank) pRp (ruler p) else if j = 7 then putWord (fun _ => blank) pRw (ruler w) else if j = 8 then putWord (fun _ => blank) pR2 (ruler (2 * w)) else if j = 9 then putWord (fun _ => blank) pF1 [bitSymbol (x.getLastD false)] else putWord (fun _ => blank) pF2 [bitSymbol (y.getLastD false)]⟩ : Tapes 11 a)
  simp only [ReturnOrigin.cfg, Config.tapes] at c9
  rw [E5_bank, E5_bank, List.length_map, hpadlen] at c9
  have c10 := hoare_place (ScanEnd.scan_hoare (fun _ => blank) pP ((BinaryMultiply.horner (mag x) (mag y)).map bitSymbol) (ReturnOrigin.bits_nonblank _) rfl) E4
    (⟨fun j => if j = 0 then pX else if j = 1 then pY else if j = 2 then pXs else if j = 3 then pYs else if j = 4 then pP2 else if j = 5 then pO else if j = 6 then pRp else if j = 7 then pRw else if j = 8 then pR2 else if j = 9 then pF1 else pF2, fun j => if j = 0 then putWord f pX (x.map bitSymbol) else if j = 1 then putWord g pY (y.map bitSymbol) else if j = 2 then putWord (fun _ => blank) pXs ((mag x).map bitSymbol) else if j = 3 then putWord (fun _ => blank) pYs ((mag y).map bitSymbol) else if j = 4 then putWord (fun _ => blank) pP2 ((padProd x y w).map bitSymbol) else if j = 5 then (fun _ => blank) else if j = 6 then putWord (fun _ => blank) pRp (ruler p) else if j = 7 then putWord (fun _ => blank) pRw (ruler w) else if j = 8 then putWord (fun _ => blank) pR2 (ruler (2 * w)) else if j = 9 then putWord (fun _ => blank) pF1 [bitSymbol (x.getLastD false)] else putWord (fun _ => blank) pF2 [bitSymbol (y.getLastD false)]⟩ : Tapes 11 a)
  simp only [ScanEnd.cfg, Config.tapes] at c10
  rw [E4_bank, E4_bank, List.length_map] at c10
  have c11 := hoare_place (EraseBack.erase_hoare (fun _ => blank) pP ((BinaryMultiply.horner (mag x) (mag y)).map bitSymbol) (ReturnOrigin.bits_nonblank _) rfl (fun _ _ => rfl)) E4
    (⟨fun j => if j = 0 then pX else if j = 1 then pY else if j = 2 then pXs else if j = 3 then pYs else if j = 4 then pP2 else if j = 5 then pO else if j = 6 then pRp else if j = 7 then pRw else if j = 8 then pR2 else if j = 9 then pF1 else pF2, fun j => if j = 0 then putWord f pX (x.map bitSymbol) else if j = 1 then putWord g pY (y.map bitSymbol) else if j = 2 then putWord (fun _ => blank) pXs ((mag x).map bitSymbol) else if j = 3 then putWord (fun _ => blank) pYs ((mag y).map bitSymbol) else if j = 4 then putWord (fun _ => blank) pP2 ((padProd x y w).map bitSymbol) else if j = 5 then (fun _ => blank) else if j = 6 then putWord (fun _ => blank) pRp (ruler p) else if j = 7 then putWord (fun _ => blank) pRw (ruler w) else if j = 8 then putWord (fun _ => blank) pR2 (ruler (2 * w)) else if j = 9 then putWord (fun _ => blank) pF1 [bitSymbol (x.getLastD false)] else putWord (fun _ => blank) pF2 [bitSymbol (y.getLastD false)]⟩ : Tapes 11 a)
  simp only [EraseBack.cfg, Config.tapes] at c11
  rw [E4_bank, E4_bank, List.length_map] at c11
  have c12 := hoare_place (RulerAdvance.advance_hoare (fun _ => blank) (putWord (fun _ => blank) pP2 ((padProd x y w).map bitSymbol)) pRp pP2 (ruler p) (ruler_nonblank _) rfl) E7_5
    (⟨fun j => if j = 0 then pX else if j = 1 then pY else if j = 2 then pXs else if j = 3 then pYs else if j = 4 then pP else if j = 5 then pO else if j = 6 then pRw else if j = 7 then pR2 else if j = 8 then pF1 else pF2, fun j => if j = 0 then putWord f pX (x.map bitSymbol) else if j = 1 then putWord g pY (y.map bitSymbol) else if j = 2 then putWord (fun _ => blank) pXs ((mag x).map bitSymbol) else if j = 3 then putWord (fun _ => blank) pYs ((mag y).map bitSymbol) else if j = 4 then (fun _ => blank) else if j = 5 then (fun _ => blank) else if j = 6 then putWord (fun _ => blank) pRw (ruler w) else if j = 7 then putWord (fun _ => blank) pR2 (ruler (2 * w)) else if j = 8 then putWord (fun _ => blank) pF1 [bitSymbol (x.getLastD false)] else putWord (fun _ => blank) pF2 [bitSymbol (y.getLastD false)]⟩ : Tapes 10 a)
  simp only [RulerAdvance.cfg, Config.tapes] at c12
  rw [E7_5_bank, E7_5_bank, ruler_length] at c12
  have c13 := hoare_place (ReturnOrigin.return_hoare_at (fun _ => blank) pRp (ruler p) (ruler_nonblank _) rfl) E7
    (⟨fun j => if j = 0 then pX else if j = 1 then pY else if j = 2 then pXs else if j = 3 then pYs else if j = 4 then pP else if j = 5 then pP2 + ↑p else if j = 6 then pO else if j = 7 then pRw else if j = 8 then pR2 else if j = 9 then pF1 else pF2, fun j => if j = 0 then putWord f pX (x.map bitSymbol) else if j = 1 then putWord g pY (y.map bitSymbol) else if j = 2 then putWord (fun _ => blank) pXs ((mag x).map bitSymbol) else if j = 3 then putWord (fun _ => blank) pYs ((mag y).map bitSymbol) else if j = 4 then (fun _ => blank) else if j = 5 then putWord (fun _ => blank) pP2 ((padProd x y w).map bitSymbol) else if j = 6 then (fun _ => blank) else if j = 7 then putWord (fun _ => blank) pRw (ruler w) else if j = 8 then putWord (fun _ => blank) pR2 (ruler (2 * w)) else if j = 9 then putWord (fun _ => blank) pF1 [bitSymbol (x.getLastD false)] else putWord (fun _ => blank) pF2 [bitSymbol (y.getLastD false)]⟩ : Tapes 11 a)
  simp only [ReturnOrigin.cfg, Config.tapes] at c13
  rw [E7_bank, E7_bank, ruler_length] at c13
  have c14 := hoare_place (RulerCopy.copy_hoare (fun _ => blank) (putWord (fun _ => blank) pP2 ((padProd x y w).map bitSymbol)) (fun _ => blank) pRw (pP2 + ↑p) pO (ruler w) (ruler_nonblank _) rfl) E8_5_6
    (⟨fun j => if j = 0 then pX else if j = 1 then pY else if j = 2 then pXs else if j = 3 then pYs else if j = 4 then pP else if j = 5 then pRp else if j = 6 then pR2 else if j = 7 then pF1 else pF2, fun j => if j = 0 then putWord f pX (x.map bitSymbol) else if j = 1 then putWord g pY (y.map bitSymbol) else if j = 2 then putWord (fun _ => blank) pXs ((mag x).map bitSymbol) else if j = 3 then putWord (fun _ => blank) pYs ((mag y).map bitSymbol) else if j = 4 then (fun _ => blank) else if j = 5 then putWord (fun _ => blank) pRp (ruler p) else if j = 6 then putWord (fun _ => blank) pR2 (ruler (2 * w)) else if j = 7 then putWord (fun _ => blank) pF1 [bitSymbol (x.getLastD false)] else putWord (fun _ => blank) pF2 [bitSymbol (y.getLastD false)]⟩ : Tapes 9 a)
  simp only [RulerCopy.cfg, Config.tapes] at c14
  rw [E8_5_6_bank, E8_5_6_bank, ruler_length, hfield] at c14
  have c15 := hoare_place (ReturnOrigin.return_hoare_at (fun _ => blank) pRw (ruler w) (ruler_nonblank _) rfl) E8
    (⟨fun j => if j = 0 then pX else if j = 1 then pY else if j = 2 then pXs else if j = 3 then pYs else if j = 4 then pP else if j = 5 then pP2 + ↑p + ↑w else if j = 6 then pO + ↑w else if j = 7 then pRp else if j = 8 then pR2 else if j = 9 then pF1 else pF2, fun j => if j = 0 then putWord f pX (x.map bitSymbol) else if j = 1 then putWord g pY (y.map bitSymbol) else if j = 2 then putWord (fun _ => blank) pXs ((mag x).map bitSymbol) else if j = 3 then putWord (fun _ => blank) pYs ((mag y).map bitSymbol) else if j = 4 then (fun _ => blank) else if j = 5 then putWord (fun _ => blank) pP2 ((padProd x y w).map bitSymbol) else if j = 6 then putWord (fun _ => blank) pO ((Gather.field (padProd x y w) p w).map bitSymbol) else if j = 7 then putWord (fun _ => blank) pRp (ruler p) else if j = 8 then putWord (fun _ => blank) pR2 (ruler (2 * w)) else if j = 9 then putWord (fun _ => blank) pF1 [bitSymbol (x.getLastD false)] else putWord (fun _ => blank) pF2 [bitSymbol (y.getLastD false)]⟩ : Tapes 11 a)
  simp only [ReturnOrigin.cfg, Config.tapes] at c15
  rw [E8_bank, E8_bank, ruler_length] at c15
  have c16 := hoare_place (ReturnOrigin.return_hoare_at (fun _ => blank) pO ((Gather.field (padProd x y w) p w).map bitSymbol) (ReturnOrigin.bits_nonblank _) rfl) E6
    (⟨fun j => if j = 0 then pX else if j = 1 then pY else if j = 2 then pXs else if j = 3 then pYs else if j = 4 then pP else if j = 5 then pP2 + ↑p + ↑w else if j = 6 then pRp else if j = 7 then pRw else if j = 8 then pR2 else if j = 9 then pF1 else pF2, fun j => if j = 0 then putWord f pX (x.map bitSymbol) else if j = 1 then putWord g pY (y.map bitSymbol) else if j = 2 then putWord (fun _ => blank) pXs ((mag x).map bitSymbol) else if j = 3 then putWord (fun _ => blank) pYs ((mag y).map bitSymbol) else if j = 4 then (fun _ => blank) else if j = 5 then putWord (fun _ => blank) pP2 ((padProd x y w).map bitSymbol) else if j = 6 then putWord (fun _ => blank) pRp (ruler p) else if j = 7 then putWord (fun _ => blank) pRw (ruler w) else if j = 8 then putWord (fun _ => blank) pR2 (ruler (2 * w)) else if j = 9 then putWord (fun _ => blank) pF1 [bitSymbol (x.getLastD false)] else putWord (fun _ => blank) pF2 [bitSymbol (y.getLastD false)]⟩ : Tapes 11 a)
  simp only [ReturnOrigin.cfg, Config.tapes] at c16
  rw [E6_bank, E6_bank, List.length_map, Gather.field_length] at c16
  have c17 := hoare_place (ReturnOrigin.return_hoare_prefix (fun _ => blank) pP2 (((padProd x y w).take (p + w)).map bitSymbol) (((padProd x y w).drop (p + w)).map bitSymbol) (ReturnOrigin.bits_nonblank _) rfl) E5
    (⟨fun j => if j = 0 then pX else if j = 1 then pY else if j = 2 then pXs else if j = 3 then pYs else if j = 4 then pP else if j = 5 then pO else if j = 6 then pRp else if j = 7 then pRw else if j = 8 then pR2 else if j = 9 then pF1 else pF2, fun j => if j = 0 then putWord f pX (x.map bitSymbol) else if j = 1 then putWord g pY (y.map bitSymbol) else if j = 2 then putWord (fun _ => blank) pXs ((mag x).map bitSymbol) else if j = 3 then putWord (fun _ => blank) pYs ((mag y).map bitSymbol) else if j = 4 then (fun _ => blank) else if j = 5 then putWord (fun _ => blank) pO ((Gather.field (padProd x y w) p w).map bitSymbol) else if j = 6 then putWord (fun _ => blank) pRp (ruler p) else if j = 7 then putWord (fun _ => blank) pRw (ruler w) else if j = 8 then putWord (fun _ => blank) pR2 (ruler (2 * w)) else if j = 9 then putWord (fun _ => blank) pF1 [bitSymbol (x.getLastD false)] else putWord (fun _ => blank) pF2 [bitSymbol (y.getLastD false)]⟩ : Tapes 11 a)
  simp only [ReturnOrigin.cfg, Config.tapes] at c17
  rw [E5_bank, E5_bank, hP2split, ← hP2head] at c17
  have c18 := hoare_place (ScanEnd.scan_hoare (fun _ => blank) pP2 ((padProd x y w).map bitSymbol) (ReturnOrigin.bits_nonblank _) rfl) E5
    (⟨fun j => if j = 0 then pX else if j = 1 then pY else if j = 2 then pXs else if j = 3 then pYs else if j = 4 then pP else if j = 5 then pO else if j = 6 then pRp else if j = 7 then pRw else if j = 8 then pR2 else if j = 9 then pF1 else pF2, fun j => if j = 0 then putWord f pX (x.map bitSymbol) else if j = 1 then putWord g pY (y.map bitSymbol) else if j = 2 then putWord (fun _ => blank) pXs ((mag x).map bitSymbol) else if j = 3 then putWord (fun _ => blank) pYs ((mag y).map bitSymbol) else if j = 4 then (fun _ => blank) else if j = 5 then putWord (fun _ => blank) pO ((Gather.field (padProd x y w) p w).map bitSymbol) else if j = 6 then putWord (fun _ => blank) pRp (ruler p) else if j = 7 then putWord (fun _ => blank) pRw (ruler w) else if j = 8 then putWord (fun _ => blank) pR2 (ruler (2 * w)) else if j = 9 then putWord (fun _ => blank) pF1 [bitSymbol (x.getLastD false)] else putWord (fun _ => blank) pF2 [bitSymbol (y.getLastD false)]⟩ : Tapes 11 a)
  simp only [ScanEnd.cfg, Config.tapes] at c18
  rw [E5_bank, E5_bank, List.length_map, hpadlen] at c18
  have c19 := hoare_place (EraseBack.erase_hoare (fun _ => blank) pP2 ((padProd x y w).map bitSymbol) (ReturnOrigin.bits_nonblank _) rfl (fun _ _ => rfl)) E5
    (⟨fun j => if j = 0 then pX else if j = 1 then pY else if j = 2 then pXs else if j = 3 then pYs else if j = 4 then pP else if j = 5 then pO else if j = 6 then pRp else if j = 7 then pRw else if j = 8 then pR2 else if j = 9 then pF1 else pF2, fun j => if j = 0 then putWord f pX (x.map bitSymbol) else if j = 1 then putWord g pY (y.map bitSymbol) else if j = 2 then putWord (fun _ => blank) pXs ((mag x).map bitSymbol) else if j = 3 then putWord (fun _ => blank) pYs ((mag y).map bitSymbol) else if j = 4 then (fun _ => blank) else if j = 5 then putWord (fun _ => blank) pO ((Gather.field (padProd x y w) p w).map bitSymbol) else if j = 6 then putWord (fun _ => blank) pRp (ruler p) else if j = 7 then putWord (fun _ => blank) pRw (ruler w) else if j = 8 then putWord (fun _ => blank) pR2 (ruler (2 * w)) else if j = 9 then putWord (fun _ => blank) pF1 [bitSymbol (x.getLastD false)] else putWord (fun _ => blank) pF2 [bitSymbol (y.getLastD false)]⟩ : Tapes 11 a)
  simp only [EraseBack.cfg, Config.tapes] at c19
  rw [E5_bank, E5_bank, List.length_map, hpadlen] at c19
  have c20 := hoare_place (ScanEnd.scan_hoare (fun _ => blank) pXs ((mag x).map bitSymbol) (ReturnOrigin.bits_nonblank _) rfl) E2
    (⟨fun j => if j = 0 then pX else if j = 1 then pY else if j = 2 then pYs else if j = 3 then pP else if j = 4 then pP2 else if j = 5 then pO else if j = 6 then pRp else if j = 7 then pRw else if j = 8 then pR2 else if j = 9 then pF1 else pF2, fun j => if j = 0 then putWord f pX (x.map bitSymbol) else if j = 1 then putWord g pY (y.map bitSymbol) else if j = 2 then putWord (fun _ => blank) pYs ((mag y).map bitSymbol) else if j = 3 then (fun _ => blank) else if j = 4 then (fun _ => blank) else if j = 5 then putWord (fun _ => blank) pO ((Gather.field (padProd x y w) p w).map bitSymbol) else if j = 6 then putWord (fun _ => blank) pRp (ruler p) else if j = 7 then putWord (fun _ => blank) pRw (ruler w) else if j = 8 then putWord (fun _ => blank) pR2 (ruler (2 * w)) else if j = 9 then putWord (fun _ => blank) pF1 [bitSymbol (x.getLastD false)] else putWord (fun _ => blank) pF2 [bitSymbol (y.getLastD false)]⟩ : Tapes 11 a)
  simp only [ScanEnd.cfg, Config.tapes] at c20
  rw [E2_bank, E2_bank, List.length_map, hmx] at c20
  have c21 := hoare_place (EraseBack.erase_hoare (fun _ => blank) pXs ((mag x).map bitSymbol) (ReturnOrigin.bits_nonblank _) rfl (fun _ _ => rfl)) E2
    (⟨fun j => if j = 0 then pX else if j = 1 then pY else if j = 2 then pYs else if j = 3 then pP else if j = 4 then pP2 else if j = 5 then pO else if j = 6 then pRp else if j = 7 then pRw else if j = 8 then pR2 else if j = 9 then pF1 else pF2, fun j => if j = 0 then putWord f pX (x.map bitSymbol) else if j = 1 then putWord g pY (y.map bitSymbol) else if j = 2 then putWord (fun _ => blank) pYs ((mag y).map bitSymbol) else if j = 3 then (fun _ => blank) else if j = 4 then (fun _ => blank) else if j = 5 then putWord (fun _ => blank) pO ((Gather.field (padProd x y w) p w).map bitSymbol) else if j = 6 then putWord (fun _ => blank) pRp (ruler p) else if j = 7 then putWord (fun _ => blank) pRw (ruler w) else if j = 8 then putWord (fun _ => blank) pR2 (ruler (2 * w)) else if j = 9 then putWord (fun _ => blank) pF1 [bitSymbol (x.getLastD false)] else putWord (fun _ => blank) pF2 [bitSymbol (y.getLastD false)]⟩ : Tapes 11 a)
  simp only [EraseBack.cfg, Config.tapes] at c21
  rw [E2_bank, E2_bank, List.length_map, hmx] at c21
  have c22 := hoare_place (ScanEnd.scan_hoare (fun _ => blank) pYs ((mag y).map bitSymbol) (ReturnOrigin.bits_nonblank _) rfl) E3
    (⟨fun j => if j = 0 then pX else if j = 1 then pY else if j = 2 then pXs else if j = 3 then pP else if j = 4 then pP2 else if j = 5 then pO else if j = 6 then pRp else if j = 7 then pRw else if j = 8 then pR2 else if j = 9 then pF1 else pF2, fun j => if j = 0 then putWord f pX (x.map bitSymbol) else if j = 1 then putWord g pY (y.map bitSymbol) else if j = 2 then (fun _ => blank) else if j = 3 then (fun _ => blank) else if j = 4 then (fun _ => blank) else if j = 5 then putWord (fun _ => blank) pO ((Gather.field (padProd x y w) p w).map bitSymbol) else if j = 6 then putWord (fun _ => blank) pRp (ruler p) else if j = 7 then putWord (fun _ => blank) pRw (ruler w) else if j = 8 then putWord (fun _ => blank) pR2 (ruler (2 * w)) else if j = 9 then putWord (fun _ => blank) pF1 [bitSymbol (x.getLastD false)] else putWord (fun _ => blank) pF2 [bitSymbol (y.getLastD false)]⟩ : Tapes 11 a)
  simp only [ScanEnd.cfg, Config.tapes] at c22
  rw [E3_bank, E3_bank, List.length_map, hmy] at c22
  have c23 := hoare_place (EraseBack.erase_hoare (fun _ => blank) pYs ((mag y).map bitSymbol) (ReturnOrigin.bits_nonblank _) rfl (fun _ _ => rfl)) E3
    (⟨fun j => if j = 0 then pX else if j = 1 then pY else if j = 2 then pXs else if j = 3 then pP else if j = 4 then pP2 else if j = 5 then pO else if j = 6 then pRp else if j = 7 then pRw else if j = 8 then pR2 else if j = 9 then pF1 else pF2, fun j => if j = 0 then putWord f pX (x.map bitSymbol) else if j = 1 then putWord g pY (y.map bitSymbol) else if j = 2 then (fun _ => blank) else if j = 3 then (fun _ => blank) else if j = 4 then (fun _ => blank) else if j = 5 then putWord (fun _ => blank) pO ((Gather.field (padProd x y w) p w).map bitSymbol) else if j = 6 then putWord (fun _ => blank) pRp (ruler p) else if j = 7 then putWord (fun _ => blank) pRw (ruler w) else if j = 8 then putWord (fun _ => blank) pR2 (ruler (2 * w)) else if j = 9 then putWord (fun _ => blank) pF1 [bitSymbol (x.getLastD false)] else putWord (fun _ => blank) pF2 [bitSymbol (y.getLastD false)]⟩ : Tapes 11 a)
  simp only [EraseBack.cfg, Config.tapes] at c23
  rw [E3_bank, E3_bank, List.length_map, hmy] at c23
  refine ⟨_, ((((((((((((((((((((((c1.seq c2).seq c3).seq c4).seq c5).seq c6).seq c7).seq c8).seq c9).seq c10).seq c11).seq c12).seq c13).seq c14).seq c15).seq c16).seq c17).seq c18).seq c19).seq c20).seq c21).seq c22).seq c23), ?_⟩
  unfold core_hoareBound
  omega

theorem negChain_hoare (x y : List Bool) (p w : ℕ) (f g : ℤ → Fin (a + 4))
    (pX pY pXs pYs pP pP2 pO pRp pRw pR2 pF1 pF2 : ℤ) (hx : x.length = w) (hy : y.length = w)
    (hw : 1 ≤ w) (hpw : p ≤ w) (hfl : f (pX - 1) = blank) (hfr : f (pX + w) = blank)
    (hgl : g (pY - 1) = blank) (hgr : g (pY + w) = blank) :
    ∃ c, HoareTime (negChain) (fun v => v = bank (putWord f pX (x.map bitSymbol)) (putWord g pY (y.map bitSymbol)) ((fun _ => blank)) ((fun _ => blank)) ((fun _ => blank)) ((fun _ => blank)) (putWord (fun _ => blank) pO ((Gather.field (padProd x y w) p w).map bitSymbol)) (putWord (fun _ => blank) pRp (ruler p)) (putWord (fun _ => blank) pRw (ruler w)) (putWord (fun _ => blank) pR2 (ruler (2 * w))) (putWord (fun _ => blank) pF1 [bitSymbol (x.getLastD false)]) (putWord (fun _ => blank) pF2 [bitSymbol (y.getLastD false)]) (pX) (pY) (pXs) (pYs) (pP) (pP2) (pO) (pRp) (pRw) (pR2) (pF1) (pF2))
      (fun v => v = bank (putWord f pX (x.map bitSymbol)) (putWord g pY (y.map bitSymbol)) ((fun _ => blank)) ((fun _ => blank)) ((fun _ => blank)) ((fun _ => blank)) (putWord (fun _ => blank) pO ((negWord (Gather.field (padProd x y w) p w)).map bitSymbol)) (putWord (fun _ => blank) pRp (ruler p)) (putWord (fun _ => blank) pRw (ruler w)) (putWord (fun _ => blank) pR2 (ruler (2 * w))) (putWord (fun _ => blank) pF1 [bitSymbol (x.getLastD false)]) (putWord (fun _ => blank) pF2 [bitSymbol (y.getLastD false)]) (pX) (pY) (pXs) (pYs) (pP) (pP2) (pO) (pRp) (pRw) (pR2) (pF1) (pF2)) c ∧ c ≤ negChain_hoareBound p w := by
  have hx0 : x ≠ [] := by intro h0; rw [h0] at hx; simp at hx; omega
  have hy0 : y ≠ [] := by intro h0; rw [h0] at hy; simp at hy; omega
  have hfr' : f (pX + ↑(x.map (bitSymbol (a := a))).length) = blank := by rw [List.length_map, hx]; exact hfr
  have hgr' : g (pY + ↑(y.map (bitSymbol (a := a))).length) = blank := by rw [List.length_map, hy]; exact hgr
  have hxsplit := map_split (a := a) x hx0
  have hysplit := map_split (a := a) y hy0
  have hx1 : (pXs : ℤ) + ↑w - 1 = pXs + ↑(x.dropLast.map (bitSymbol (a := a))).length := by
    simp [List.length_dropLast, hx]; omega
  have hy1 : (pYs : ℤ) + ↑w - 1 = pYs + ↑(y.dropLast.map (bitSymbol (a := a))).length := by
    simp [List.length_dropLast, hy]; omega
  have hmx : (mag x).length = w := by rw [mag_length, hx]
  have hmy : (mag y).length = w := by rw [mag_length, hy]
  have hhw : (BinaryMultiply.horner (mag x) (mag y)).length ≤ 2 * w := by
    have := BinaryMultiply.horner_length (mag x) (mag y); omega
  have hpadlen : (padProd x y w).length = 2 * w := by simp [padProd]; omega
  have hpad := cells_pad (a := a) pP (BinaryMultiply.horner (mag x) (mag y)) (2 * w) hhw
  have hfield : CopyCells.cells (putWord (fun _ => (blank : Fin (a + 4))) pP2 ((padProd x y w).map bitSymbol)) (pP2 + ↑p) w =
      (Gather.field (padProd x y w) p w).map bitSymbol :=
    cells_field1 _ _ _ _ _ (by omega)
  have hP2split : ((padProd x y w).take (p + w)).map (bitSymbol (a := a)) ++ ((padProd x y w).drop (p + w)).map bitSymbol =
      (padProd x y w).map bitSymbol := by
    rw [← List.map_append, List.take_append_drop]
  have hP2head : (pP2 : ℤ) + ↑p + ↑w = pP2 + ↑(((padProd x y w).take (p + w)).map (bitSymbol (a := a))).length := by
    simp [List.length_take, hpadlen]; omega
  have n1 := hoare_place (Negate.neg_hoare (fun _ => blank) pO (Gather.field (padProd x y w) p w) rfl) E6
    (⟨fun j => if j = 0 then pX else if j = 1 then pY else if j = 2 then pXs else if j = 3 then pYs else if j = 4 then pP else if j = 5 then pP2 else if j = 6 then pRp else if j = 7 then pRw else if j = 8 then pR2 else if j = 9 then pF1 else pF2, fun j => if j = 0 then putWord f pX (x.map bitSymbol) else if j = 1 then putWord g pY (y.map bitSymbol) else if j = 2 then (fun _ => blank) else if j = 3 then (fun _ => blank) else if j = 4 then (fun _ => blank) else if j = 5 then (fun _ => blank) else if j = 6 then putWord (fun _ => blank) pRp (ruler p) else if j = 7 then putWord (fun _ => blank) pRw (ruler w) else if j = 8 then putWord (fun _ => blank) pR2 (ruler (2 * w)) else if j = 9 then putWord (fun _ => blank) pF1 [bitSymbol (x.getLastD false)] else putWord (fun _ => blank) pF2 [bitSymbol (y.getLastD false)]⟩ : Tapes 11 a)
  simp only [Negate.cfg, Config.tapes] at n1
  rw [E6_bank, E6_bank, Gather.field_length] at n1
  have n2 := hoare_place (ReturnOrigin.return_hoare_at (fun _ => blank) pO ((negWord (Gather.field (padProd x y w) p w)).map bitSymbol) (ReturnOrigin.bits_nonblank _) rfl) E6
    (⟨fun j => if j = 0 then pX else if j = 1 then pY else if j = 2 then pXs else if j = 3 then pYs else if j = 4 then pP else if j = 5 then pP2 else if j = 6 then pRp else if j = 7 then pRw else if j = 8 then pR2 else if j = 9 then pF1 else pF2, fun j => if j = 0 then putWord f pX (x.map bitSymbol) else if j = 1 then putWord g pY (y.map bitSymbol) else if j = 2 then (fun _ => blank) else if j = 3 then (fun _ => blank) else if j = 4 then (fun _ => blank) else if j = 5 then (fun _ => blank) else if j = 6 then putWord (fun _ => blank) pRp (ruler p) else if j = 7 then putWord (fun _ => blank) pRw (ruler w) else if j = 8 then putWord (fun _ => blank) pR2 (ruler (2 * w)) else if j = 9 then putWord (fun _ => blank) pF1 [bitSymbol (x.getLastD false)] else putWord (fun _ => blank) pF2 [bitSymbol (y.getLastD false)]⟩ : Tapes 11 a)
  simp only [ReturnOrigin.cfg, Config.tapes] at n2
  rw [E6_bank, E6_bank, List.length_map, TwosComplement.negWord_length, Gather.field_length] at n2
  refine ⟨_, (n1.seq n2), ?_⟩
  unfold negChain_hoareBound
  omega

theorem cleanup_hoare (x y : List Bool) (p w : ℕ) (f g : ℤ → Fin (a + 4))
    (pX pY pXs pYs pP pP2 pO pRp pRw pR2 pF1 pF2 : ℤ) (hx : x.length = w) (hy : y.length = w)
    (hw : 1 ≤ w) (hpw : p ≤ w) (hfl : f (pX - 1) = blank) (hfr : f (pX + w) = blank)
    (hgl : g (pY - 1) = blank) (hgr : g (pY + w) = blank) :
    ∃ c, HoareTime (cleanup) (fun v => v = bank (putWord f pX (x.map bitSymbol)) (putWord g pY (y.map bitSymbol)) ((fun _ => blank)) ((fun _ => blank)) ((fun _ => blank)) ((fun _ => blank)) (putWord (fun _ => blank) pO ((result x y p w).map bitSymbol)) (putWord (fun _ => blank) pRp (ruler p)) (putWord (fun _ => blank) pRw (ruler w)) (putWord (fun _ => blank) pR2 (ruler (2 * w))) (putWord (fun _ => blank) pF1 [bitSymbol (x.getLastD false)]) (putWord (fun _ => blank) pF2 [bitSymbol (y.getLastD false)]) (pX) (pY) (pXs) (pYs) (pP) (pP2) (pO) (pRp) (pRw) (pR2) (pF1) (pF2))
      (fun v => v = bank (putWord f pX (x.map bitSymbol)) (putWord g pY (y.map bitSymbol)) ((fun _ => blank)) ((fun _ => blank)) ((fun _ => blank)) ((fun _ => blank)) (putWord (fun _ => blank) pO ((result x y p w).map bitSymbol)) (putWord (fun _ => blank) pRp (ruler p)) (putWord (fun _ => blank) pRw (ruler w)) (putWord (fun _ => blank) pR2 (ruler (2 * w))) ((fun _ => blank)) ((fun _ => blank)) (pX) (pY) (pXs) (pYs) (pP) (pP2) (pO) (pRp) (pRw) (pR2) (pF1) (pF2)) c ∧ c ≤ cleanup_hoareBound p w := by
  have hx0 : x ≠ [] := by intro h0; rw [h0] at hx; simp at hx; omega
  have hy0 : y ≠ [] := by intro h0; rw [h0] at hy; simp at hy; omega
  have hfr' : f (pX + ↑(x.map (bitSymbol (a := a))).length) = blank := by rw [List.length_map, hx]; exact hfr
  have hgr' : g (pY + ↑(y.map (bitSymbol (a := a))).length) = blank := by rw [List.length_map, hy]; exact hgr
  have hxsplit := map_split (a := a) x hx0
  have hysplit := map_split (a := a) y hy0
  have hx1 : (pXs : ℤ) + ↑w - 1 = pXs + ↑(x.dropLast.map (bitSymbol (a := a))).length := by
    simp [List.length_dropLast, hx]; omega
  have hy1 : (pYs : ℤ) + ↑w - 1 = pYs + ↑(y.dropLast.map (bitSymbol (a := a))).length := by
    simp [List.length_dropLast, hy]; omega
  have hmx : (mag x).length = w := by rw [mag_length, hx]
  have hmy : (mag y).length = w := by rw [mag_length, hy]
  have hhw : (BinaryMultiply.horner (mag x) (mag y)).length ≤ 2 * w := by
    have := BinaryMultiply.horner_length (mag x) (mag y); omega
  have hpadlen : (padProd x y w).length = 2 * w := by simp [padProd]; omega
  have hpad := cells_pad (a := a) pP (BinaryMultiply.horner (mag x) (mag y)) (2 * w) hhw
  have hfield : CopyCells.cells (putWord (fun _ => (blank : Fin (a + 4))) pP2 ((padProd x y w).map bitSymbol)) (pP2 + ↑p) w =
      (Gather.field (padProd x y w) p w).map bitSymbol :=
    cells_field1 _ _ _ _ _ (by omega)
  have hP2split : ((padProd x y w).take (p + w)).map (bitSymbol (a := a)) ++ ((padProd x y w).drop (p + w)).map bitSymbol =
      (padProd x y w).map bitSymbol := by
    rw [← List.map_append, List.take_append_drop]
  have hP2head : (pP2 : ℤ) + ↑p + ↑w = pP2 + ↑(((padProd x y w).take (p + w)).map (bitSymbol (a := a))).length := by
    simp [List.length_take, hpadlen]; omega
  have e1 := hoare_place (EraseCell.erase_hoare (putWord (fun _ => blank) pF1 [bitSymbol (x.getLastD false)]) pF1) E10
    (⟨fun j => if j = 0 then pX else if j = 1 then pY else if j = 2 then pXs else if j = 3 then pYs else if j = 4 then pP else if j = 5 then pP2 else if j = 6 then pO else if j = 7 then pRp else if j = 8 then pRw else if j = 9 then pR2 else pF2, fun j => if j = 0 then putWord f pX (x.map bitSymbol) else if j = 1 then putWord g pY (y.map bitSymbol) else if j = 2 then (fun _ => blank) else if j = 3 then (fun _ => blank) else if j = 4 then (fun _ => blank) else if j = 5 then (fun _ => blank) else if j = 6 then putWord (fun _ => blank) pO ((result x y p w).map bitSymbol) else if j = 7 then putWord (fun _ => blank) pRp (ruler p) else if j = 8 then putWord (fun _ => blank) pRw (ruler w) else if j = 9 then putWord (fun _ => blank) pR2 (ruler (2 * w)) else putWord (fun _ => blank) pF2 [bitSymbol (y.getLastD false)]⟩ : Tapes 11 a)
  simp only [EraseCell.cfg, Config.tapes] at e1
  rw [E10_bank, E10_bank, EraseCell.erase_single] at e1
  have e2 := hoare_place (EraseCell.erase_hoare (putWord (fun _ => blank) pF2 [bitSymbol (y.getLastD false)]) pF2) E11
    (⟨fun j => if j = 0 then pX else if j = 1 then pY else if j = 2 then pXs else if j = 3 then pYs else if j = 4 then pP else if j = 5 then pP2 else if j = 6 then pO else if j = 7 then pRp else if j = 8 then pRw else if j = 9 then pR2 else pF1, fun j => if j = 0 then putWord f pX (x.map bitSymbol) else if j = 1 then putWord g pY (y.map bitSymbol) else if j = 2 then (fun _ => blank) else if j = 3 then (fun _ => blank) else if j = 4 then (fun _ => blank) else if j = 5 then (fun _ => blank) else if j = 6 then putWord (fun _ => blank) pO ((result x y p w).map bitSymbol) else if j = 7 then putWord (fun _ => blank) pRp (ruler p) else if j = 8 then putWord (fun _ => blank) pRw (ruler w) else if j = 9 then putWord (fun _ => blank) pR2 (ruler (2 * w)) else (fun _ => blank)⟩ : Tapes 11 a)
  simp only [EraseCell.cfg, Config.tapes] at e2
  rw [E11_bank, E11_bank, EraseCell.erase_single] at e2
  refine ⟨_, (e1.seq e2), ?_⟩
  unfold cleanup_hoareBound
  omega


section Conditionals

theorem cond1_hoare (x y : List Bool) (p w : ℕ) (f g : ℤ → Fin (a + 4))
    (pX pY pXs pYs pP pP2 pO pRp pRw pR2 pF1 pF2 : ℤ) (hx : x.length = w) (hy : y.length = w)
    (hw : 1 ≤ w) (hpw : p ≤ w) (hfl : f (pX - 1) = blank) (hfr : f (pX + w) = blank)
    (hgl : g (pY - 1) = blank) (hgr : g (pY + w) = blank) :
    ∃ c, HoareTime cond1 (fun v => v = bank (putWord f pX (x.map bitSymbol)) (putWord g pY (y.map bitSymbol)) (putWord (fun _ => blank) pXs ((x).map bitSymbol)) (putWord (fun _ => blank) pYs ((y).map bitSymbol)) ((fun _ => blank)) ((fun _ => blank)) ((fun _ => blank)) (putWord (fun _ => blank) pRp (ruler p)) (putWord (fun _ => blank) pRw (ruler w)) (putWord (fun _ => blank) pR2 (ruler (2 * w))) ((fun _ => blank)) ((fun _ => blank)) (pX) (pY) (pXs + ↑w - 1) (pYs) (pP) (pP2) (pO) (pRp) (pRw) (pR2) (pF1) (pF2))
      (fun v => v = bank (putWord f pX (x.map bitSymbol)) (putWord g pY (y.map bitSymbol)) (putWord (fun _ => blank) pXs ((mag x).map bitSymbol)) (putWord (fun _ => blank) pYs ((y).map bitSymbol)) ((fun _ => blank)) ((fun _ => blank)) ((fun _ => blank)) (putWord (fun _ => blank) pRp (ruler p)) (putWord (fun _ => blank) pRw (ruler w)) (putWord (fun _ => blank) pR2 (ruler (2 * w))) (putWord (fun _ => blank) pF1 [bitSymbol (x.getLastD false)]) ((fun _ => blank)) (pX) (pY) (pXs) (pYs) (pP) (pP2) (pO) (pRp) (pRw) (pR2) (pF1) (pF2)) c ∧ c ≤ 3 * w + 11 := by
  obtain ⟨c1, ht, hc1⟩ := sxTrue_hoare x y p w f g pX pY pXs pYs pP pP2 pO pRp pRw pR2 pF1 pF2 hx hy hw hpw hfl hfr hgl hgr
  obtain ⟨c2, hf, hc2⟩ := sxFalse_hoare x y p w f g pX pY pXs pYs pP pP2 pO pRp pRw pR2 pF1 pF2 hx hy hw hpw hfl hfr hgl hgr
  have hx0 : x ≠ [] := by intro h0; rw [h0] at hx; simp at hx; omega
  have hread : (bank (putWord f pX (x.map bitSymbol)) (putWord g pY (y.map bitSymbol)) (putWord (fun _ => blank) pXs ((x).map bitSymbol)) (putWord (fun _ => blank) pYs ((y).map bitSymbol)) ((fun _ => blank)) ((fun _ => blank)) ((fun _ => blank)) (putWord (fun _ => blank) pRp (ruler p)) (putWord (fun _ => blank) pRw (ruler w)) (putWord (fun _ => blank) pR2 (ruler (2 * w))) ((fun _ => blank)) ((fun _ => blank)) (pX) (pY) (pXs + ↑w - 1) (pYs) (pP) (pP2) (pO) (pRp) (pRw) (pR2) (pF1) (pF2)).reads 2 = bitSymbol (x.getLastD false) := by
    simp only [Tapes.reads, bank, ↓reduceIte, Fin.isValue]
    exact putWord_last _ _ _ hx0 w hx
  refine ⟨max c1 c2 + 1, ?_, by unfold sxTrue_hoareBound at hc1; unfold sxFalse_hoareBound at hc2; omega⟩
  unfold cond1
  cases hsx : x.getLastD false
  · refine branch_hoare _ (fun v ⟨hv, hv'⟩ => ?_) (hf.consequence (fun v hv => hv.1) (fun v hv => ?_) le_rfl)
    · exfalso; rw [hv, hread, hsx] at hv'; simp [bitSymbol] at hv'
    · rw [hv]; simp only [mag, hsx, Bool.false_eq_true, ↓reduceIte]
  · refine branch_hoare _ (ht.consequence (fun v hv => hv.1) (fun v hv => ?_) le_rfl) (fun v ⟨hv, hv'⟩ => ?_)
    · rw [hv]; simp only [mag, hsx, ↓reduceIte]
    · exfalso; rw [hv, hread, hsx] at hv'; simp [bitSymbol] at hv'

theorem cond2_hoare (x y : List Bool) (p w : ℕ) (f g : ℤ → Fin (a + 4))
    (pX pY pXs pYs pP pP2 pO pRp pRw pR2 pF1 pF2 : ℤ) (hx : x.length = w) (hy : y.length = w)
    (hw : 1 ≤ w) (hpw : p ≤ w) (hfl : f (pX - 1) = blank) (hfr : f (pX + w) = blank)
    (hgl : g (pY - 1) = blank) (hgr : g (pY + w) = blank) :
    ∃ c, HoareTime cond2 (fun v => v = bank (putWord f pX (x.map bitSymbol)) (putWord g pY (y.map bitSymbol)) (putWord (fun _ => blank) pXs ((mag x).map bitSymbol)) (putWord (fun _ => blank) pYs ((y).map bitSymbol)) ((fun _ => blank)) ((fun _ => blank)) ((fun _ => blank)) (putWord (fun _ => blank) pRp (ruler p)) (putWord (fun _ => blank) pRw (ruler w)) (putWord (fun _ => blank) pR2 (ruler (2 * w))) (putWord (fun _ => blank) pF1 [bitSymbol (x.getLastD false)]) ((fun _ => blank)) (pX) (pY) (pXs) (pYs + ↑w - 1) (pP) (pP2) (pO) (pRp) (pRw) (pR2) (pF1) (pF2))
      (fun v => v = bank (putWord f pX (x.map bitSymbol)) (putWord g pY (y.map bitSymbol)) (putWord (fun _ => blank) pXs ((mag x).map bitSymbol)) (putWord (fun _ => blank) pYs ((mag y).map bitSymbol)) ((fun _ => blank)) ((fun _ => blank)) ((fun _ => blank)) (putWord (fun _ => blank) pRp (ruler p)) (putWord (fun _ => blank) pRw (ruler w)) (putWord (fun _ => blank) pR2 (ruler (2 * w))) (putWord (fun _ => blank) pF1 [bitSymbol (x.getLastD false)]) (putWord (fun _ => blank) pF2 [bitSymbol (y.getLastD false)]) (pX) (pY) (pXs) (pYs) (pP) (pP2) (pO) (pRp) (pRw) (pR2) (pF1) (pF2)) c ∧ c ≤ 3 * w + 11 := by
  obtain ⟨c1, ht, hc1⟩ := syTrue_hoare x y p w f g pX pY pXs pYs pP pP2 pO pRp pRw pR2 pF1 pF2 hx hy hw hpw hfl hfr hgl hgr
  obtain ⟨c2, hf, hc2⟩ := syFalse_hoare x y p w f g pX pY pXs pYs pP pP2 pO pRp pRw pR2 pF1 pF2 hx hy hw hpw hfl hfr hgl hgr
  have hy0 : y ≠ [] := by intro h0; rw [h0] at hy; simp at hy; omega
  have hread : (bank (putWord f pX (x.map bitSymbol)) (putWord g pY (y.map bitSymbol)) (putWord (fun _ => blank) pXs ((mag x).map bitSymbol)) (putWord (fun _ => blank) pYs ((y).map bitSymbol)) ((fun _ => blank)) ((fun _ => blank)) ((fun _ => blank)) (putWord (fun _ => blank) pRp (ruler p)) (putWord (fun _ => blank) pRw (ruler w)) (putWord (fun _ => blank) pR2 (ruler (2 * w))) (putWord (fun _ => blank) pF1 [bitSymbol (x.getLastD false)]) ((fun _ => blank)) (pX) (pY) (pXs) (pYs + ↑w - 1) (pP) (pP2) (pO) (pRp) (pRw) (pR2) (pF1) (pF2)).reads 3 = bitSymbol (y.getLastD false) := by
    simp only [Tapes.reads, bank, ↓reduceIte, Fin.isValue]
    exact putWord_last _ _ _ hy0 w hy
  refine ⟨max c1 c2 + 1, ?_, by unfold syTrue_hoareBound at hc1; unfold syFalse_hoareBound at hc2; omega⟩
  unfold cond2
  cases hsy : y.getLastD false
  · refine branch_hoare _ (fun v ⟨hv, hv'⟩ => ?_) (hf.consequence (fun v hv => hv.1) (fun v hv => ?_) le_rfl)
    · exfalso; rw [hv, hread, hsy] at hv'; simp [bitSymbol] at hv'
    · rw [hv]; simp only [mag, hsy, Bool.false_eq_true, ↓reduceIte]
  · refine branch_hoare _ (ht.consequence (fun v hv => hv.1) (fun v hv => ?_) le_rfl) (fun v ⟨hv, hv'⟩ => ?_)
    · rw [hv]; simp only [mag, hsy, ↓reduceIte]
    · exfalso; rw [hv, hread, hsy] at hv'; simp [bitSymbol] at hv'

/-- The sign branches: negate the output exactly when the flags differ. -/
theorem final_hoare (x y : List Bool) (p w : ℕ) (f g : ℤ → Fin (a + 4))
    (pX pY pXs pYs pP pP2 pO pRp pRw pR2 pF1 pF2 : ℤ) (hx : x.length = w) (hy : y.length = w)
    (hw : 1 ≤ w) (hpw : p ≤ w) (hfl : f (pX - 1) = blank) (hfr : f (pX + w) = blank)
    (hgl : g (pY - 1) = blank) (hgr : g (pY + w) = blank) :
    ∃ c, HoareTime final (fun v => v = bank (putWord f pX (x.map bitSymbol)) (putWord g pY (y.map bitSymbol)) ((fun _ => blank)) ((fun _ => blank)) ((fun _ => blank)) ((fun _ => blank)) (putWord (fun _ => blank) pO ((Gather.field (padProd x y w) p w).map bitSymbol)) (putWord (fun _ => blank) pRp (ruler p)) (putWord (fun _ => blank) pRw (ruler w)) (putWord (fun _ => blank) pR2 (ruler (2 * w))) (putWord (fun _ => blank) pF1 [bitSymbol (x.getLastD false)]) (putWord (fun _ => blank) pF2 [bitSymbol (y.getLastD false)]) (pX) (pY) (pXs) (pYs) (pP) (pP2) (pO) (pRp) (pRw) (pR2) (pF1) (pF2))
      (fun v => v = bank (putWord f pX (x.map bitSymbol)) (putWord g pY (y.map bitSymbol)) ((fun _ => blank)) ((fun _ => blank)) ((fun _ => blank)) ((fun _ => blank)) (putWord (fun _ => blank) pO ((result x y p w).map bitSymbol)) (putWord (fun _ => blank) pRp (ruler p)) (putWord (fun _ => blank) pRw (ruler w)) (putWord (fun _ => blank) pR2 (ruler (2 * w))) (putWord (fun _ => blank) pF1 [bitSymbol (x.getLastD false)]) (putWord (fun _ => blank) pF2 [bitSymbol (y.getLastD false)]) (pX) (pY) (pXs) (pYs) (pP) (pP2) (pO) (pRp) (pRw) (pR2) (pF1) (pF2)) c ∧ c ≤ 2 * w + 7 := by
  obtain ⟨c1, hn, hc1⟩ := negChain_hoare x y p w f g pX pY pXs pYs pP pP2 pO pRp pRw pR2 pF1 pF2 hx hy hw hpw hfl hfr hgl hgr
  unfold negChain_hoareBound at hc1
  have hsk := skip_hoare (by norm_num : 0 < 12) (bank (putWord f pX (x.map bitSymbol)) (putWord g pY (y.map bitSymbol)) ((fun _ => blank)) ((fun _ => blank)) ((fun _ => blank)) ((fun _ => blank)) (putWord (fun _ => blank) pO ((Gather.field (padProd x y w) p w).map bitSymbol)) (putWord (fun _ => blank) pRp (ruler p)) (putWord (fun _ => blank) pRw (ruler w)) (putWord (fun _ => blank) pR2 (ruler (2 * w))) (putWord (fun _ => blank) pF1 [bitSymbol (x.getLastD false)]) (putWord (fun _ => blank) pF2 [bitSymbol (y.getLastD false)]) (pX) (pY) (pXs) (pYs) (pP) (pP2) (pO) (pRp) (pRw) (pR2) (pF1) (pF2))
  have hread1 : (bank (putWord f pX (x.map bitSymbol)) (putWord g pY (y.map bitSymbol)) ((fun _ => blank)) ((fun _ => blank)) ((fun _ => blank)) ((fun _ => blank)) (putWord (fun _ => blank) pO ((Gather.field (padProd x y w) p w).map bitSymbol)) (putWord (fun _ => blank) pRp (ruler p)) (putWord (fun _ => blank) pRw (ruler w)) (putWord (fun _ => blank) pR2 (ruler (2 * w))) (putWord (fun _ => blank) pF1 [bitSymbol (x.getLastD false)]) (putWord (fun _ => blank) pF2 [bitSymbol (y.getLastD false)]) (pX) (pY) (pXs) (pYs) (pP) (pP2) (pO) (pRp) (pRw) (pR2) (pF1) (pF2)).reads 10 = bitSymbol (x.getLastD false) := by
    simp [Tapes.reads, bank, putWord]
  have hread2 : (bank (putWord f pX (x.map bitSymbol)) (putWord g pY (y.map bitSymbol)) ((fun _ => blank)) ((fun _ => blank)) ((fun _ => blank)) ((fun _ => blank)) (putWord (fun _ => blank) pO ((Gather.field (padProd x y w) p w).map bitSymbol)) (putWord (fun _ => blank) pRp (ruler p)) (putWord (fun _ => blank) pRw (ruler w)) (putWord (fun _ => blank) pR2 (ruler (2 * w))) (putWord (fun _ => blank) pF1 [bitSymbol (x.getLastD false)]) (putWord (fun _ => blank) pF2 [bitSymbol (y.getLastD false)]) (pX) (pY) (pXs) (pYs) (pP) (pP2) (pO) (pRp) (pRw) (pR2) (pF1) (pF2)).reads 11 = bitSymbol (y.getLastD false) := by
    simp [Tapes.reads, bank, putWord]
  refine ⟨max (max 0 c1 + 1) (max c1 0 + 1) + 1, ?_, by omega⟩
  unfold final
  cases hsx : x.getLastD false <;> cases hsy : y.getLastD false
  all_goals simp only [hsx, hsy] at hread1 hread2 hsk hn
  · refine branch_hoare _ (fun v ⟨hv, hv'⟩ => ?_) ?_
    · exfalso; rw [hv, hread1] at hv'; simp [bitSymbol] at hv'
    · refine branch_hoare _ (fun v ⟨⟨hv, _⟩, hv'⟩ => ?_)
        (hsk.consequence (fun v hv => hv.1.1) (fun v hv => ?_) le_rfl)
      · exfalso; rw [hv, hread2] at hv'; simp [bitSymbol] at hv'
      · rw [hv]; simp only [result, hsx, hsy]; simp
  · refine branch_hoare _ (fun v ⟨hv, hv'⟩ => ?_) ?_
    · exfalso; rw [hv, hread1] at hv'; simp [bitSymbol] at hv'
    · refine branch_hoare _ (hn.consequence (fun v hv => hv.1.1) (fun v hv => ?_) le_rfl)
        (fun v ⟨⟨hv, _⟩, hv'⟩ => ?_)
      · rw [hv]; simp only [result, hsx, hsy]; simp
      · exfalso; rw [hv, hread2] at hv'; simp [bitSymbol] at hv'
  · refine branch_hoare _ ?_ (fun v ⟨hv, hv'⟩ => ?_)
    · refine branch_hoare _ (fun v ⟨⟨hv, _⟩, hv'⟩ => ?_)
        (hn.consequence (fun v hv => hv.1.1) (fun v hv => ?_) le_rfl)
      · exfalso; rw [hv, hread2] at hv'; simp [bitSymbol] at hv'
      · rw [hv]; simp only [result, hsx, hsy]; simp
    · exfalso; rw [hv, hread1] at hv'; simp [bitSymbol] at hv'
  · refine branch_hoare _ ?_ (fun v ⟨hv, hv'⟩ => ?_)
    · refine branch_hoare _ (hsk.consequence (fun v hv => hv.1.1) (fun v hv => ?_) le_rfl)
        (fun v ⟨⟨hv, _⟩, hv'⟩ => ?_)
      · rw [hv]; simp only [result, hsx, hsy]; simp
      · exfalso; rw [hv, hread2] at hv'; simp [bitSymbol] at hv'
    · exfalso; rw [hv, hread1] at hv'; simp [bitSymbol] at hv'

end Conditionals

section Main

/-- The total cost bound. -/
def cost (p w : ℕ) : ℕ := w * (5 * w + 2 * w + 18) + 50 * w + 4 * p + 140

/-- The multiply's contract: operands and rulers preserved, every scratch tape
blank again, and the output word placed at its origin. -/
theorem mul_hoare (x y : List Bool) (p w : ℕ) (f g : ℤ → Fin (a + 4))
    (pX pY pXs pYs pP pP2 pO pRp pRw pR2 pF1 pF2 : ℤ) (hx : x.length = w) (hy : y.length = w)
    (hw : 1 ≤ w) (hpw : p ≤ w) (hfl : f (pX - 1) = blank) (hfr : f (pX + w) = blank)
    (hgl : g (pY - 1) = blank) (hgr : g (pY + w) = blank) :
    HoareTime program (fun v => v = bank (putWord f pX (x.map bitSymbol)) (putWord g pY (y.map bitSymbol)) ((fun _ => blank)) ((fun _ => blank)) ((fun _ => blank)) ((fun _ => blank)) ((fun _ => blank)) (putWord (fun _ => blank) pRp (ruler p)) (putWord (fun _ => blank) pRw (ruler w)) (putWord (fun _ => blank) pR2 (ruler (2 * w))) ((fun _ => blank)) ((fun _ => blank)) (pX) (pY) (pXs) (pYs) (pP) (pP2) (pO) (pRp) (pRw) (pR2) (pF1) (pF2))
      (fun v => v = bank (putWord f pX (x.map bitSymbol)) (putWord g pY (y.map bitSymbol)) ((fun _ => blank)) ((fun _ => blank)) ((fun _ => blank)) ((fun _ => blank)) (putWord (fun _ => blank) pO ((result x y p w).map bitSymbol)) (putWord (fun _ => blank) pRp (ruler p)) (putWord (fun _ => blank) pRw (ruler w)) (putWord (fun _ => blank) pR2 (ruler (2 * w))) ((fun _ => blank)) ((fun _ => blank)) (pX) (pY) (pXs) (pYs) (pP) (pP2) (pO) (pRp) (pRw) (pR2) (pF1) (pF2)) (cost p w) := by
  obtain ⟨c1, h1, hc1⟩ := prefix1_hoare x y p w f g pX pY pXs pYs pP pP2 pO pRp pRw pR2 pF1 pF2 hx hy hw hpw hfl hfr hgl hgr
  obtain ⟨c2, h2, hc2⟩ := cond1_hoare x y p w f g pX pY pXs pYs pP pP2 pO pRp pRw pR2 pF1 pF2 hx hy hw hpw hfl hfr hgl hgr
  obtain ⟨c3, h3, hc3⟩ := prefix2_hoare x y p w f g pX pY pXs pYs pP pP2 pO pRp pRw pR2 pF1 pF2 hx hy hw hpw hfl hfr hgl hgr
  obtain ⟨c4, h4, hc4⟩ := cond2_hoare x y p w f g pX pY pXs pYs pP pP2 pO pRp pRw pR2 pF1 pF2 hx hy hw hpw hfl hfr hgl hgr
  obtain ⟨c5, h5, hc5⟩ := core_hoare x y p w f g pX pY pXs pYs pP pP2 pO pRp pRw pR2 pF1 pF2 hx hy hw hpw hfl hfr hgl hgr
  obtain ⟨c6, h6, hc6⟩ := final_hoare x y p w f g pX pY pXs pYs pP pP2 pO pRp pRw pR2 pF1 pF2 hx hy hw hpw hfl hfr hgl hgr
  obtain ⟨c7, h7, hc7⟩ := cleanup_hoare x y p w f g pX pY pXs pYs pP pP2 pO pRp pRw pR2 pF1 pF2 hx hy hw hpw hfl hfr hgl hgr
  unfold prefix1_hoareBound at hc1
  unfold prefix2_hoareBound at hc3
  unfold core_hoareBound at hc5
  unfold cleanup_hoareBound at hc7
  refine ((((((h1.seq h2).seq h3).seq h4).seq h5).seq h6).seq h7).consequence
    (fun v hv => hv) (fun v hv => hv) ?_
  unfold cost
  omega

end Main

end IntegerMultBounds.Machine.FixedMul
