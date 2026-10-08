import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

/-! Fixed-size child descriptors for manuscript §4, “Power-width interchange
with rows” and “A fixed-tape depth-first schedule” (04-swap.tex, lines129–267).
A descriptor retains the ordered factors [A,row,B,H,C,D,E], where H and D have
q^width addresses. A,B,C,E collect adjacent spectator fields; they are never
permuted. The actual cyclic role split must produce row/roles rows, requiring
roles ∣ row. Selecting the ith H and jth D fields in a width=m*b parent then
regroups spectators into the same seven-factor descriptor. These are literal
row-major address and size equalities, not tape operations, descriptor runtime
bounds, or a recursive-machine construction. Arbitrary spectator cardinalities
and the row range remain explicit; existing radix-power prefix routines do not
automatically implement them. -/
namespace IntegerMultBounds.Machine.RecursiveInterchangeLayout

structure Descriptor where
  beforeRows : ℕ
  rows : ℕ
  beforeH : ℕ
  width : ℕ
  between : ℕ
  afterD : ℕ
  deriving DecidableEq

def Descriptor.Positive (v : Descriptor) : Prop :=
  0 < v.beforeRows ∧ 0 < v.rows ∧ 0 < v.beforeH ∧ 0 < v.between ∧ 0 < v.afterD

def volume (q : ℕ) (v : Descriptor) : ℕ :=
  v.beforeRows*v.rows*v.beforeH*q^v.width*v.between*q^v.width*v.afterD

/-- Literal row-major index in [A,row,B,H,C,D,E] order. -/
def index (q : ℕ) (v : Descriptor) (a row before h middle d after : ℕ) : ℕ :=
  (((((a*v.rows+row)*v.beforeH+before)*q^v.width+h)*v.between+middle)*q^v.width+d)*v.afterD+after

/-- Shape of one role stream after the separate physical cyclic row split. -/
def role (v : Descriptor) (roles : ℕ) : Descriptor := { v with rows := v.rows/roles }

/-- Child target fields are the ith and jth b-digit fields. Each group of
spectators remains in its original order and is packed into an adjacent range. -/
def child (q roles b : ℕ) (v : Descriptor) {m : ℕ} (i j : Fin m) : Descriptor where
  beforeRows := v.beforeRows
  rows := v.rows/roles
  beforeH := v.beforeH*q^(i.val*b)
  width := b
  between := q^((m-1-i.val)*b)*v.between*q^(j.val*b)
  afterD := q^((m-1-j.val)*b)*v.afterD

theorem split_power (q b : ℕ) {m : ℕ} (i : Fin m) :
    q^(m*b) = q^(i.val*b)*q^b*q^((m-1-i.val)*b) := by
  rw [← pow_add,← pow_add]
  congr 1
  have hi := i.isLt
  have hm : i.val+1+(m-1-i.val) = m := by omega
  nlinarith

/-- Regrouping spectators does not move a single symbol within a role stream.
The two parent chunks are explicitly split into prefix, selected digit-field,
and suffix components. -/
theorem child_index (q roles b : ℕ) (v : Descriptor) {m : ℕ} (i j : Fin m)
    (hw : v.width = m*b) (a row before hp h hs middle dp d ds after : ℕ) :
    index q (child q roles b v i j) a row (before*q^(i.val*b)+hp) h
      ((hs*v.between+middle)*q^(j.val*b)+dp) d (ds*v.afterD+after) =
    index q (role v roles) a row before
      ((hp*q^b+h)*q^((m-1-i.val)*b)+hs) middle
      ((dp*q^b+d)*q^((m-1-j.val)*b)+ds) after := by
  simp only [index,child,role,hw]
  nth_rw 1 [split_power q b i]
  rw [split_power q b j]
  ring

/-- Selecting subchunks preserves the complete role-stream volume, including
all digits outside the selected chunks. -/
theorem child_volume (q roles b : ℕ) (v : Descriptor) {m : ℕ} (i j : Fin m)
    (hw : v.width = m*b) : volume q (child q roles b v i j) = volume q (role v roles) := by
  simp only [volume,child,role,hw]
  nth_rw 1 [split_power q b i]
  rw [split_power q b j]
  ring

theorem role_volume_mul (q roles : ℕ) (v : Descriptor) (hdiv : roles ∣ v.rows) :
    volume q (role v roles)*roles = volume q v := by
  unfold volume role
  calc
    _ = v.beforeRows*((v.rows/roles)*roles)*v.beforeH*q^v.width*v.between*q^v.width*v.afterD := by ring
    _ = _ := by rw [Nat.div_mul_cancel hdiv]

/-- The recursion denominator is the number of role streams, not parked space. -/
theorem child_volume_div (q roles b : ℕ) (v : Descriptor) {m : ℕ} (i j : Fin m)
    (hw : v.width = m*b) (hr : 0 < roles) (hdiv : roles ∣ v.rows) :
    volume q (child q roles b v i j) = volume q v/roles := by
  rw [child_volume q roles b v i j hw,← role_volume_mul q roles v hdiv]
  exact (Nat.mul_div_cancel _ hr).symm

theorem child_positive (q roles b : ℕ) (v : Descriptor) {m : ℕ} (i j : Fin m)
    (hq : 0 < q) (hr : 0 < roles) (hdiv : roles ∣ v.rows) (hv : v.Positive) :
    (child q roles b v i j).Positive := by
  rcases hv with ⟨ha,hrow,hb,hc,he⟩
  exact ⟨ha,Nat.div_pos (Nat.le_of_dvd hrow hdiv) hr,
    Nat.mul_pos hb (pow_pos hq _),Nat.mul_pos (Nat.mul_pos (pow_pos hq _) hc) (pow_pos hq _),
    Nat.mul_pos (pow_pos hq _) he⟩

/-- A child has precisely the row divisibility required at the next depth. -/
theorem child_rows_divisible (q roles b k : ℕ) (v : Descriptor) {m : ℕ} (i j : Fin m)
    (hr : 0 < roles) (hdiv : roles^(k+1) ∣ v.rows) :
    roles^k ∣ (child q roles b v i j).rows := by
  obtain ⟨n,hn⟩ := hdiv
  change roles^k ∣ v.rows/roles
  rw [hn,pow_succ]
  have he : roles^k*roles*n = (roles^k*n)*roles := by ring
  rw [he,Nat.mul_div_cancel _ hr]
  exact dvd_mul_right _ _

private theorem pack_lt {a A b B : ℕ} (ha : a < A) (hb : b < B) : a*B+b < A*B := by
  nlinarith

/-- The regrouped spectator addresses lie in exactly their declared ranges. -/
theorem child_spectators_bounded (q roles b : ℕ) (v : Descriptor) {m : ℕ} (i j : Fin m)
    (before hp hs middle dp ds after : ℕ)
    (hb : before < v.beforeH) (hp' : hp < q^(i.val*b))
    (hs' : hs < q^((m-1-i.val)*b)) (hc : middle < v.between)
    (dp' : dp < q^(j.val*b)) (ds' : ds < q^((m-1-j.val)*b)) (he : after < v.afterD) :
    before*q^(i.val*b)+hp < (child q roles b v i j).beforeH ∧
    (hs*v.between+middle)*q^(j.val*b)+dp < (child q roles b v i j).between ∧
    ds*v.afterD+after < (child q roles b v i j).afterD :=
  ⟨pack_lt hb hp',pack_lt (pack_lt hs' hc) dp',pack_lt ds' he⟩

/-- Original row coordinates are the cyclic-role index roles*g+w. This theorem
only checks its range; splitting and merging these rows remain physical tasks. -/
theorem cyclic_row_lt (roles : ℕ) (v : Descriptor) (g w : ℕ)
    (hg : g < v.rows/roles) (hw : w < roles) (hdiv : roles ∣ v.rows) :
    roles*g+w < v.rows := by
  have hh := pack_lt hg hw
  rw [Nat.div_mul_cancel hdiv] at hh
  simpa only [Nat.mul_comm g roles] using hh

end IntegerMultBounds.Machine.RecursiveInterchangeLayout
