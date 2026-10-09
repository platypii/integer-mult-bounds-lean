import IntegerMultBounds.Swap.Recurrence
import IntegerMultBounds.Machine.Shared50RecursiveDepth
import IntegerMultBounds.Machine.FlatCoordinateLayout

/-! The manuscript's arbitrary-width partition into consecutive power-width
pieces. This is executable shape data and address semantics, not an assertion
that partition construction or tape views have already been implemented. -/
namespace IntegerMultBounds.Machine.ArbitraryWidthPieces
noncomputable section
open Networks
open RecursiveInterchangeLayout (Descriptor volume)

/-- One list entry per power-width call; the entry is the recursion depth.
Least-significant base-m width digits come first in the partition. -/
def depths (m n k : ℕ) : List ℕ :=
  (List.range (k+1)).flatMap (fun j => List.replicate (n/m^j%m) j)

def widths (m n k : ℕ) : List ℕ := (depths m n k).map (fun j => m^j)

/-- Every piece uses an allowed power and requires at most k recursion levels. -/
theorem depth_le {m n k j : ℕ} (hj : j ∈ depths m n k) : j ≤ k := by
  obtain ⟨i,hi,hj⟩ := List.mem_flatMap.mp hj
  have he : j=i := (List.mem_replicate.mp hj).2
  subst j
  have := List.mem_range.mp hi
  omega

private theorem range_sum {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ((List.range n).map f).sum = ∑ j ∈ Finset.range n, f j := by
  induction n with
  | zero => simp
  | succ n ih => simp only [List.sum_range_succ,Finset.sum_range_succ,ih]

private theorem sum_map_le (xs : List ℕ) (f : ℕ → ℕ) (c : ℕ)
    (h : ∀ j ∈ xs, f j ≤ c) : (xs.map f).sum ≤ c*xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := h x (by simp)
    have ht := ih (fun j hj => h j (by simp [hj]))
    simp only [List.map_cons,List.sum_cons,List.length_cons]
    nlinarith

/-- The partition covers the width exactly, including zero width. -/
theorem widths_sum {m : ℕ} (hm : 2 ≤ m) (n k : ℕ) (hn : n < m^(k+1)) :
    (widths m n k).sum = n := by
  unfold widths depths
  simp only [List.flatMap_def,List.map_flatten,List.map_map,Function.comp_def,List.map_replicate,List.sum_flatten,List.sum_replicate,
    nsmul_eq_mul]
  rw [range_sum]
  exact Swap.Recurrence.base_expansion hm k n hn

/-- The actual finite piece list has exactly the digit-weighted cost sum
used in the manuscript and the existing arbitrary-width arithmetic bound. -/
theorem real_piece_sum (m n k : ℕ) (f : ℕ → ℝ) :
    ((depths m n k).map f).sum =
      ∑ j ∈ Finset.range (k+1), (n/m^j%m : ℕ)*f j := by
  unfold depths
  simp only [List.flatMap_def,List.map_flatten,List.map_map,Function.comp_def,
    List.map_replicate,List.sum_flatten,List.sum_replicate,nsmul_eq_mul]
  exact range_sum _ _

/-- The least base-m exponent computed by integer logarithm suffices for
all positive widths and also handles the empty-width partition. -/
theorem canonical_sum {m : ℕ} (hm : 2 ≤ m) (n : ℕ) :
    (widths m n (Nat.log m n)).sum = n :=
  widths_sum hm n _ (Nat.lt_pow_succ_log_self (by omega) n)

/-- At most m-1 pieces per base-m digit position. -/
theorem count_le {m : ℕ} (hm : 2 ≤ m) (n k : ℕ) :
    (depths m n k).length ≤ (m-1)*(k+1) := by
  unfold depths
  rw [List.length_flatMap]
  simp only [List.length_replicate]
  have hh : ∀ j ∈ List.range (k+1), n/m^j%m ≤ m-1 := by
    intro j _
    have := Swap.Recurrence.base_digit_lt hm n j
    omega
  have h := sum_map_le (List.range (k+1)) (fun j => n/m^j%m) (m-1) hh
  simpa only [List.length_range] using h

/-- Prefix sums locate each consecutive piece entirely inside the full width. -/
theorem prefix_fit (ws : List ℕ) (i : Fin ws.length) :
    (ws.take i.val).sum+ws[i] ≤ ws.sum := by
  have he := congrArg List.sum (List.take_append_drop (i.val+1) ws)
  rw [List.sum_append,List.sum_take_succ ws i.val i.isLt] at he
  simpa only [Fin.getElem_fin] using (show (ws.take i.val).sum+ws[i.val] ≤ ws.sum by omega)

/-- The computed offset and width of every actual partition piece fit. -/
theorem piece_fit {m n k : ℕ} (hm : 2 ≤ m) (hn : n < m^(k+1))
    (i : Fin (widths m n k).length) :
    ((widths m n k).take i.val).sum+(widths m n k)[i] ≤ n := by
  simpa only [widths_sum hm n k hn] using prefix_fit (widths m n k) i

/-- Exchange one corresponding digit interval without changing its spectators. -/
def swapWindow {α : Type*} {n : ℕ} (start width : ℕ) (data : Fin n → α×α) : Fin n → α×α :=
  fun z => if start ≤ z.val ∧ z.val < start+width then (data z).swap else data z

/-- Corresponding consecutive H/D pieces are exchanged in list order. -/
def runWindows {α : Type*} {n : ℕ} : List ℕ → ℕ → (Fin n → α×α) → (Fin n → α×α)
  | [], _, data => data
  | w::ws, start, data => runWindows ws (start+w) (swapWindow start w data)

/-- Consecutive piece exchanges affect exactly their union, once per digit. -/
theorem runWindows_cell {α : Type*} {n : ℕ} (ws : List ℕ) (start : ℕ)
    (data : Fin n → α×α) (z : Fin n) :
    runWindows ws start data z =
      if start ≤ z.val ∧ z.val < start+ws.sum then (data z).swap else data z := by
  induction ws generalizing start data with
  | nil => simp [runWindows]
  | cons w ws ih =>
    change runWindows ws (start+w) (swapWindow start w data) z =
      if start ≤ z.val ∧ z.val < start+(w+ws.sum) then (data z).swap else data z
    rw [ih]
    unfold swapWindow
    by_cases hf : start ≤ z.val ∧ z.val < start+w
    · have ht : ¬(start+w ≤ z.val ∧ z.val < start+w+ws.sum) := by omega
      have hb : start ≤ z.val ∧ z.val < start+(w+ws.sum) := by omega
      rw [ite_eq_right ht,ite_eq_left hf,ite_eq_left hb]
    · by_cases ht : start+w ≤ z.val ∧ z.val < start+w+ws.sum
      · have hb : start ≤ z.val ∧ z.val < start+(w+ws.sum) := by omega
        rw [ite_eq_left ht,ite_eq_right hf,ite_eq_left hb]
      · have hb : ¬(start ≤ z.val ∧ z.val < start+(w+ws.sum)) := by omega
        rw [ite_eq_right ht,ite_eq_right hf,ite_eq_right hb]

/-- An exact width partition exchanges both full digit chunks. -/
theorem runWindows_full {α : Type*} {n : ℕ} (ws : List ℕ) (hws : ws.sum=n)
    (data : Fin n → α×α) : runWindows ws 0 data = fun z => (data z).swap := by
  funext z
  rw [runWindows_cell,hws,ite_eq_left]
  exact ⟨Nat.zero_le _,by simpa only [Nat.zero_add] using z.isLt⟩

/-- The concrete base-m power partition therefore performs the full swap. -/
theorem pieces_swap {α : Type*} {m n k : ℕ} (hm : 2 ≤ m) (hn : n < m^(k+1))
    (data : Fin n → α×α) :
    runWindows (widths m n k) 0 data = fun z => (data z).swap :=
  runWindows_full _ (widths_sum hm n k hn) data

/-- Numeric radix-q address chunks exchange too; rank is the existing
most-significant-first coordinate encoding used by the actual tape views. -/
theorem pieces_rank {q m n k : ℕ} [NeZero q] (hm : 2 ≤ m) (hn : n < m^(k+1))
    (h d : Fin n → ZMod q) :
    let out := runWindows (widths m n k) 0 (fun z => (h z,d z))
    (FlatCoordinateLayout.rank (fun z => (out z).1), FlatCoordinateLayout.rank (fun z => (out z).2)) =
      (FlatCoordinateLayout.rank d,FlatCoordinateLayout.rank h) := by
  dsimp only
  rw [pieces_swap hm hn]
  rfl

/-- Numeric chunk addresses need no new digit conversion for the semantic
partition: the existing rank/coordinates equivalence names the same addresses. -/
def scalarPieces {q m n k : ℕ} [NeZero q] (h d : Fin (q^n)) : Fin (q^n)×Fin (q^n) :=
  let out := runWindows (widths m n k) 0
    (fun z => (FlatCoordinateLayout.coordinates h z,FlatCoordinateLayout.coordinates d z))
  (FlatCoordinateLayout.rank (fun z => (out z).1),FlatCoordinateLayout.rank (fun z => (out z).2))

theorem scalarPieces_swap {q m n k : ℕ} [NeZero q] (hm : 2 ≤ m) (hn : n < m^(k+1))
    (h d : Fin (q^n)) : scalarPieces (m := m) (k := k) h d = (d,h) := by
  simpa only [scalarPieces,FlatCoordinateLayout.rank_coordinates] using
    pieces_rank hm hn (FlatCoordinateLayout.coordinates h) (FlatCoordinateLayout.coordinates d)

/-- Viewing an interval inside both equal chunks packs the unaffected digits
into the existing prefix, gap and suffix fields, without changing row counts. -/
def slice (q : ℕ) (v : Descriptor) (offset width : ℕ) : Descriptor where
  beforeRows := v.beforeRows
  rows := v.rows
  beforeH := v.beforeH*q^offset
  width := width
  between := q^(v.width-offset-width)*v.between*q^offset
  afterD := q^(v.width-offset-width)*v.afterD

theorem slice_positive (q : ℕ) (hq : 0 < q) (v : Descriptor) (hp : v.Positive)
    (offset width : ℕ) : (slice q v offset width).Positive :=
  ⟨hp.1,hp.2.1,Nat.mul_pos hp.2.2.1 (pow_pos hq _),
    Nat.mul_pos (Nat.mul_pos (pow_pos hq _) hp.2.2.2.1) (pow_pos hq _),
    Nat.mul_pos (pow_pos hq _) hp.2.2.2.2⟩

/-- Each power-piece call processes the full logical padded parent volume;
its extra address digits are spectators, rather than discarded storage. -/
theorem slice_volume (q : ℕ) (v : Descriptor) (offset width : ℕ)
    (hfit : offset+width ≤ v.width) : volume q (slice q v offset width) = volume q v := by
  have hp : q^offset*q^width*q^(v.width-offset-width) = q^v.width := by
    rw [← pow_add,← pow_add]
    congr 1
    omega
  unfold volume slice
  dsimp only
  calc v.beforeRows*v.rows*(v.beforeH*q^offset)*q^width*
          (q^(v.width-offset-width)*v.between*q^offset)*q^width*
          (q^(v.width-offset-width)*v.afterD)
      = v.beforeRows*v.rows*v.beforeH*(q^offset*q^width*q^(v.width-offset-width))*v.between*
          (q^offset*q^width*q^(v.width-offset-width))*v.afterD := by ring
    _ = _ := by rw [hp]

/-- A common W^k-padded row field meets the actual power-width machine's
shape contract for every depth appearing in the arbitrary-width partition. -/
theorem slice_shape {v : Descriptor} {k j : ℕ} (hp : v.Positive)
    (hrows : Shared50TapeGlobal.roleCount^k ∣ v.rows) (hj : j ≤ k) (offset : ℕ) :
    Shared50RecursiveDepth.Shape j (slice Shared50ModularControl.prime v offset (125000^j)) :=
  ⟨slice_positive _ Shared50ModularControl.prime_prime.pos v hp offset _,rfl,
    dvd_trans (pow_dvd_pow Shared50TapeGlobal.roleCount hj) hrows⟩

/-- Every concrete list entry is ready for the power-width shape contract. -/
theorem piece_shape {v : Descriptor} {n k j : ℕ} (hp : v.Positive)
    (hrows : Shared50TapeGlobal.roleCount^k ∣ v.rows) (hj : j ∈ depths 125000 n k) (offset : ℕ) :
    Shared50RecursiveDepth.Shape j (slice Shared50ModularControl.prime v offset (125000^j)) :=
  slice_shape hp hrows (depth_le hj) offset

/-- Offset of a piece in the consecutive most-significant-first partition. -/
def offset (m n k i : ℕ) : ℕ :=
  (((depths m n k).take i).map (fun j => m^j)).sum

/-- Every computed interval fits the original chunk, so its volume equality
is applicable to the actual power-width call. -/
theorem offset_fit {m n k : ℕ} (hm : 2 ≤ m) (hn : n < m^(k+1))
    (i : Fin (depths m n k).length) : offset m n k i.val+m^((depths m n k)[i]) ≤ n := by
  have hf := piece_fit hm hn (⟨i.val,by simpa only [widths,List.length_map] using i.isLt⟩ :
    Fin (widths m n k).length)
  simpa only [offset,widths,List.map_take,List.getElem_map,Fin.getElem_fin] using hf

/-- The actual power-width Shape and logical volume for every arbitrary-width
piece. The common padded row field is retained throughout the piece schedule. -/
theorem piece_view {v : Descriptor} {k : ℕ} (hp : v.Positive)
    (hrows : Shared50TapeGlobal.roleCount^k ∣ v.rows) (hwidth : v.width < 125000^(k+1))
    (i : Fin (depths 125000 v.width k).length) :
    Shared50RecursiveDepth.Shape ((depths 125000 v.width k)[i])
        (slice Shared50ModularControl.prime v (offset 125000 v.width k i.val)
          (125000^((depths 125000 v.width k)[i]))) ∧
      volume Shared50ModularControl.prime
        (slice Shared50ModularControl.prime v (offset 125000 v.width k i.val)
          (125000^((depths 125000 v.width k)[i]))) = volume Shared50ModularControl.prime v := by
  refine ⟨piece_shape hp hrows (List.getElem_mem i.isLt) _,?_⟩
  exact slice_volume _ v _ _ (offset_fit (by decide) hwidth i)

end
end IntegerMultBounds.Machine.ArbitraryWidthPieces
