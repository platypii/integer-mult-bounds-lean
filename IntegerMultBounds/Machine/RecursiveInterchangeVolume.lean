import IntegerMultBounds.Machine.RecursiveInterchangeLayout

/-! Logical volume along genuine seven-factor child selections. The row count
shrinks by the number of roles, while all original target digits remain present
in target or spectator fields. No parked storage is counted as child volume. -/
namespace IntegerMultBounds.Machine.RecursiveInterchangeVolume
open RecursiveInterchangeLayout

def nonrowVolume (q : ℕ) (v : Descriptor) : ℕ :=
  v.beforeRows*v.beforeH*q^v.width*v.between*q^v.width*v.afterD

theorem volume_factor (q : ℕ) (v : Descriptor) :
    volume q v = v.rows*nonrowVolume q v := by unfold volume nonrowVolume; ring

theorem child_nonrow (q roles b : ℕ) (v : Descriptor) {m : ℕ} (i j : Fin m)
    (hw : v.width = m*b) : nonrowVolume q (child q roles b v i j) = nonrowVolume q v := by
  simp only [nonrowVolume,child,hw]
  nth_rw 1 [split_power q b i]
  rw [split_power q b j]
  ring

theorem original_chunks_lower (q : ℕ) (v : Descriptor) (hv : v.Positive) :
    q^(2*v.width) ≤ nonrowVolume q v := by
  rcases hv with ⟨ha,_,hb,hc,he⟩
  rw [two_mul,pow_add]
  unfold nonrowVolume
  calc
    q^v.width*q^v.width = 1*1*q^v.width*1*q^v.width*1 := by ring
    _ ≤ _ := by gcongr <;> omega

/-- A sequence of actual descriptor child selections, with the row divisibility
required by every cyclic split. Each selection may choose different subchunks. -/
inductive Path (q roles m : ℕ) (root : Descriptor) : ℕ → Descriptor → Prop
  | start : Path q roles m root 0 root
  | descend {n : ℕ} {v : Descriptor} (prior : Path q roles m root n v)
      (b : ℕ) (i j : Fin m) (hw : v.width = m*b) (hdiv : roles ∣ v.rows) :
      Path q roles m root (n+1) (child q roles b v i j)

theorem Path.nonrow {q roles m n : ℕ} {root v : Descriptor}
    (path : Path q roles m root n v) : nonrowVolume q v = nonrowVolume q root := by
  induction path with
  | start => rfl
  | descend prior b i j hw _ ih => exact (child_nonrow q roles b _ i j hw).trans ih

theorem Path.positive {q roles m n : ℕ} {root v : Descriptor}
    (path : Path q roles m root n v) (hq : 0 < q) (hr : 0 < roles) (hv : root.Positive) :
    v.Positive := by
  induction path with
  | start => exact hv
  | descend prior b i j hw hdiv ih => exact child_positive q roles b _ i j hq hr hdiv ih

/-- Row multiplicity is the sole recursion-volume denominator. -/
theorem Path.rows_mul {q roles m n : ℕ} {root v : Descriptor}
    (path : Path q roles m root n v) : v.rows*roles^n = root.rows := by
  induction path with
  | start => simp
  | @descend n v prior b i j hw hdiv ih =>
    change (v.rows/roles)*roles^(n+1) = root.rows
    rw [pow_succ]
    calc
      _ = ((v.rows / roles)*roles)*roles^n := by ring
      _ = _ := by rw [Nat.div_mul_cancel hdiv]; exact ih

/-- Every descent divides the selected chunk width by the fixed arity. -/
theorem Path.width_mul {q roles m n : ℕ} {root v : Descriptor}
    (path : Path q roles m root n v) : v.width*m^n = root.width := by
  induction path with
  | start => simp
  | @descend n v prior b i j hw hdiv ih =>
    change b*m^(n+1) = root.width
    rw [pow_succ]
    calc
      _ = (m*b)*m^n := by ring
      _ = _ := by rw [← hw]; exact ih

/-- For a power-width root, an actual child path cannot exceed its root depth. -/
theorem Path.depth_bound {q roles m n k : ℕ} {root v : Descriptor}
    (path : Path q roles m root n v) (hm : 1 < m) (hw : root.width = m^k) : n ≤ k := by
  have hp : 0 < root.width := by rw [hw]; exact pow_pos (by omega) _
  have hv : 0 < v.width := by
    have hh := path.width_mul
    by_contra hn
    have hz : v.width = 0 := by omega
    rw [hz,zero_mul] at hh
    omega
  apply (Nat.pow_le_pow_iff_right hm).mp
  calc
    m^n ≤ v.width*m^n := Nat.le_mul_of_pos_left _ hv
    _ = m^k := path.width_mul.trans hw

/-- Exact depth-wise logical volume, independent of inactive parked arrays. -/
theorem Path.volume_mul {q roles m n : ℕ} {root v : Descriptor}
    (path : Path q roles m root n v) : volume q v*roles^n = volume q root := by
  rw [volume_factor,volume_factor,path.nonrow]
  calc
    _ = (v.rows*roles^n)*nonrowVolume q root := by ring
    _ = _ := by rw [path.rows_mul]

theorem Path.volume_div {q roles m n : ℕ} {root v : Descriptor}
    (path : Path q roles m root n v) (hr : 0 < roles) :
    volume q v = volume q root/roles^n := by
  rw [← path.volume_mul]
  exact (Nat.mul_div_cancel _ (pow_pos hr _)).symm

/-- Even the deepest child retains both entire original chunks in its logical
volume. This is the lower bound used to absorb descriptor processing costs. -/
theorem Path.original_chunks {q roles m n : ℕ} {root v : Descriptor}
    (path : Path q roles m root n v) (hq : 0 < q) (hr : 0 < roles) (hv : root.Positive) :
    q^(2*root.width) ≤ volume q v := by
  have hp := path.positive hq hr hv
  rw [volume_factor,path.nonrow]
  calc
    _ ≤ nonrowVolume q root := original_chunks_lower q root hv
    _ ≤ v.rows*nonrowVolume q root := Nat.le_mul_of_pos_left _ hp.2.1

end IntegerMultBounds.Machine.RecursiveInterchangeVolume
