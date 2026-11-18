module

public import IntegerMultBounds.Machine.RecursiveInterchangeLayout

/-!
# Label columns as views of the interchange descriptor

A role stream of the cover keeps its label box at the low end of the prefix of its descriptor:
`v.beforeH = B q^(k c)`, with `k` columns of `c` digits. Exchanging columns `s < t` is the plain
interchange of the view `colView`: the two columns are its fields, the columns before `s` join
the prefix, the columns between are its middle, and the later columns and the whole payload of
`v` are its suffix.

* `colView_volume`, `colView_index`: the view has the volume of `v` and moves no symbol.
* `swap_cols`: an interchange of the view exchanges the two columns in the label of every
  address of `v` and keeps the payload.

So a column exchange of a route is one call of the interchange supplier on a caller's
descriptor, with no new machine.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Cover.LabelView

open IntegerMultBounds.Machine.RecursiveInterchangeLayout

/-- The view whose two fields are label columns `s < t` of `k` columns of `c` digits. -/
def colView (q c k s t B : ℕ) (v : Descriptor) : Descriptor where
  beforeRows := v.beforeRows
  rows := v.rows
  beforeH := B * q ^ (s * c)
  width := c
  between := q ^ ((t - s - 1) * c)
  afterD := q ^ ((k - 1 - t) * c) * (q ^ v.width * v.between * q ^ v.width * v.afterD)

theorem split_cols (q c k s t : ℕ) (hst : s < t) (ht : t < k) :
    q ^ (k * c) =
      q ^ (s * c) * q ^ c * q ^ ((t - s - 1) * c) * q ^ c * q ^ ((k - 1 - t) * c) := by
  have hk : k * c = s * c + c + (t - s - 1) * c + c + (k - 1 - t) * c := by
    have h : k = s + 1 + (t - s - 1) + 1 + (k - 1 - t) := by omega
    conv_lhs => rw [h]
    ring
  rw [hk, pow_add, pow_add, pow_add, pow_add]

theorem colView_volume (q c k s t B : ℕ) (v : Descriptor) (hv : v.beforeH = B * q ^ (k * c))
    (hst : s < t) (ht : t < k) : volume q (colView q c k s t B v) = volume q v := by
  simp only [volume, colView, hv, split_cols q c k s t hst ht]
  ring

/-- The label with columns `cs` at `s` and `ct` at `t`: `lp | cs | mid | ct | ls`. -/
def label (q c k s t lp cs mid ct ls : ℕ) : ℕ :=
  (((lp * q ^ c + cs) * q ^ ((t - s - 1) * c) + mid) * q ^ c + ct) * q ^ ((k - 1 - t) * c) + ls

/-- **The view moves no symbol.** -/
theorem colView_index (q c k s t B : ℕ) (v : Descriptor) (hv : v.beforeH = B * q ^ (k * c))
    (hst : s < t) (ht : t < k) (a row b lp cs mid ct ls h m d after : ℕ) :
    index q (colView q c k s t B v) a row (b * q ^ (s * c) + lp) cs mid ct
        (ls * (q ^ v.width * v.between * q ^ v.width * v.afterD) +
          (((h * v.between + m) * q ^ v.width + d) * v.afterD + after)) =
      index q v a row (b * q ^ (k * c) + label q c k s t lp cs mid ct ls) h m d after := by
  simp only [index, colView, label, hv, split_cols q c k s t hst ht]
  ring

/-- `y` is the plain interchange of `x` on every address of `v`. -/
def Swapped {α : Type*} (q : ℕ) (v : Descriptor) (x y : ℕ → α) : Prop :=
  ∀ a < v.beforeRows, ∀ row < v.rows, ∀ before < v.beforeH, ∀ h < q ^ v.width,
    ∀ mid < v.between, ∀ d < q ^ v.width, ∀ after < v.afterD,
      y (index q v a row before h mid d after) = x (index q v a row before d mid h after)

private theorem pack_lt {a A b B : ℕ} (ha : a < A) (hb : b < B) : a * B + b < A * B := by
  nlinarith

/-- **A column exchange is an interchange of the view.** On every address of `v` the two
columns of the label are exchanged; the other columns and the payload stay. -/
theorem swap_cols {α : Type*} {q c k s t B : ℕ} {v : Descriptor}
    (hv : v.beforeH = B * q ^ (k * c)) (hst : s < t) (ht : t < k) {x y : ℕ → α}
    (hT : Swapped q (colView q c k s t B v) x y)
    {a row b lp cs mid ct ls h m d after : ℕ} (ha : a < v.beforeRows) (hrow : row < v.rows)
    (hb : b < B) (hlp : lp < q ^ (s * c)) (hcs : cs < q ^ c) (hmid : mid < q ^ ((t - s - 1) * c))
    (hct : ct < q ^ c) (hls : ls < q ^ ((k - 1 - t) * c)) (hh : h < q ^ v.width)
    (hm : m < v.between) (hd : d < q ^ v.width) (hafter : after < v.afterD) :
    y (index q v a row (b * q ^ (k * c) + label q c k s t lp cs mid ct ls) h m d after) =
      x (index q v a row (b * q ^ (k * c) + label q c k s t lp ct mid cs ls) h m d after) := by
  rw [← colView_index q c k s t B v hv hst ht, ← colView_index q c k s t B v hv hst ht]
  exact hT a ha row hrow (b * q ^ (s * c) + lp) (pack_lt hb hlp) cs hcs mid hmid ct hct _
    (pack_lt hls (pack_lt (pack_lt (pack_lt hh hm) hd) hafter))

end IntegerMultBounds.MathlibTM2.Cover.LabelView
