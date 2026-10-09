import IntegerMultBounds.Machine.RecursiveRowPadding

/-! Numerical range padding of both chunk coordinates is two ordinary
grouped row extensions. The intervening regrouping preserves the literal
flat word. Cropping after the padded transpose is the original transpose. -/
namespace IntegerMultBounds.Machine.RadixRangePadding
open RecursiveInterchangeRows (pack pack_val)
variable {P N G B : ℕ} {α : Type*}

def volume (P N G B : ℕ) := P*N*G*N*B

def index (p : Fin P) (h : Fin N) (g : Fin G) (d : Fin N) (b : Fin B) :
    Fin (volume P N G B) := pack (pack (pack (pack p h) g) d) b

def coordinates (z : Fin (volume P N G B)) :
    Fin P × Fin N × Fin G × Fin N × Fin B :=
  let db := finProdFinEquiv.symm z
  let gd := finProdFinEquiv.symm db.1
  let hg := finProdFinEquiv.symm gd.1
  let ph := finProdFinEquiv.symm hg.1
  (ph.1,ph.2,hg.2,gd.2,db.2)

@[simp] theorem coordinates_index (p : Fin P) (h : Fin N) (g : Fin G) (d : Fin N) (b : Fin B) :
    coordinates (index p h g d b) = (p,h,g,d,b) := by simp [coordinates,index,pack]

theorem index_coordinates (z : Fin (volume P N G B)) :
    index (coordinates z).1 (coordinates z).2.1 (coordinates z).2.2.1
      (coordinates z).2.2.2.1 (coordinates z).2.2.2.2 = z := by
  obtain ⟨⟨phgd,b⟩,rfl⟩ := finProdFinEquiv.surjective z
  obtain ⟨⟨phg,d⟩,rfl⟩ := finProdFinEquiv.surjective phgd
  obtain ⟨⟨ph,g⟩,rfl⟩ := finProdFinEquiv.surjective phg
  obtain ⟨⟨p,h⟩,rfl⟩ := finProdFinEquiv.surjective ph
  simp [coordinates,index,pack]
  rfl

def transpose (x : Fin (volume P N G B) → α) : Fin (volume P N G B) → α := fun z =>
  let c := coordinates z
  x (index c.1 c.2.2.2.1 c.2.2.1 c.2.1 c.2.2.2.2)

@[simp] theorem transpose_entry (x : Fin (volume P N G B) → α)
    (p : Fin P) (h : Fin N) (g : Fin G) (d : Fin N) (b : Fin B) :
    transpose x (index p h g d b) = x (index p d g h b) := by simp [transpose]

theorem regroup (P N G M B : ℕ) : P*N*(G*M*B) = P*N*G*M*B := by ring

def pad (M : ℕ) (zero : α) (x : Fin (volume P N G B) → α) :
    Fin (volume P M G B) → α :=
  let first := RecursiveRowPadding.pad (A := P*N*G) (R := N) (L := B) M zero x
  let grouped := fun z : Fin (P*N*(G*M*B)) => first (Fin.cast (regroup P N G M B) z)
  let second := RecursiveRowPadding.pad (A := P) (R := N) (L := G*M*B) M zero grouped
  fun z => second (Fin.cast (regroup P M G M B).symm z)

private theorem regroup_index (p : Fin P) (h : Fin N) (g : Fin G) (d : Fin M) (b : Fin B) :
    Fin.cast (regroup P N G M B) (pack (pack p h) (pack (pack g d) b)) =
      pack (pack (pack (pack p h) g) d) b := by
  apply Fin.ext
  simp only [Fin.val_cast,pack_val]
  ring

theorem pad_entry (M : ℕ) (zero : α) (x : Fin (volume P N G B) → α)
    (p : Fin P) (h : Fin M) (g : Fin G) (d : Fin M) (b : Fin B) :
    pad M zero x (index p h g d b) =
      if hh : h.val < N then
        if hd : d.val < N then x (index p ⟨h.val,hh⟩ g ⟨d.val,hd⟩ b) else zero
      else zero := by
  have hi : Fin.cast (regroup P M G M B).symm (index p h g d b) =
      pack (pack p h) (pack (pack g d) b) := by
    apply Fin.ext
    simp only [Fin.val_cast,index,pack_val]
    ring
  unfold pad
  rw [hi,RecursiveRowPadding.pad_entry]
  by_cases hh : h.val < N
  · rw [dite_eq_left hh,dite_eq_left hh,regroup_index]
    have he := RecursiveRowPadding.pad_entry (A := P*N*G) (R := N) (L := B)
      M zero x (pack (pack p ⟨h.val,hh⟩) g) d b
    exact he
  · rw [dite_eq_right hh,dite_eq_right hh]

def crop {M : ℕ} (hNM : N ≤ M) (x : Fin (volume P M G B) → α) :
    Fin (volume P N G B) → α := fun z =>
  let c := coordinates z
  x (index c.1 ⟨c.2.1.val,c.2.1.isLt.trans_le hNM⟩ c.2.2.1
    ⟨c.2.2.2.1.val,c.2.2.2.1.isLt.trans_le hNM⟩ c.2.2.2.2)

@[simp] theorem crop_entry {M : ℕ} (hNM : N ≤ M) (x : Fin (volume P M G B) → α)
    (p : Fin P) (h : Fin N) (g : Fin G) (d : Fin N) (b : Fin B) :
    crop hNM x (index p h g d b) =
      x (index p ⟨h.val,h.isLt.trans_le hNM⟩ g ⟨d.val,d.isLt.trans_le hNM⟩ b) := by
  simp [crop]

/-- Reverse grouped scans: crop H first, then D. No data reordering is
hidden in the association of the suffix product. -/
def cropStages {M : ℕ} (hNM : N ≤ M) (x : Fin (volume P M G B) → α) :
    Fin (volume P N G B) → α :=
  let grouped := fun z : Fin (P*M*(G*M*B)) => x (Fin.cast (regroup P M G M B) z)
  let first := RecursiveRowPadding.crop (A := P) (R := N) (L := G*M*B) hNM grouped
  let ungrouped := fun z : Fin (P*N*G*M*B) => first (Fin.cast (regroup P N G M B).symm z)
  RecursiveRowPadding.crop (A := P*N*G) (R := N) (L := B) hNM ungrouped

theorem cropStages_eq {M : ℕ} (hNM : N ≤ M) (x : Fin (volume P M G B) → α) :
    cropStages hNM x = crop hNM x := by
  funext z
  rw [← index_coordinates z]
  let c := coordinates z
  have hi : Fin.cast (regroup P N G M B).symm
      (pack (pack (pack (pack c.1 c.2.1) c.2.2.1)
        ⟨c.2.2.2.1.val,c.2.2.2.1.isLt.trans_le hNM⟩) c.2.2.2.2) =
      pack (pack c.1 c.2.1)
        (pack (pack c.2.2.1 ⟨c.2.2.2.1.val,c.2.2.2.1.isLt.trans_le hNM⟩) c.2.2.2.2) := by
    apply Fin.ext
    simp only [Fin.val_cast,pack_val]
    ring
  change cropStages hNM x (index c.1 c.2.1 c.2.2.1 c.2.2.2.1 c.2.2.2.2) = _
  unfold cropStages index
  rw [RecursiveRowPadding.crop_entry,hi,RecursiveRowPadding.crop_entry]
  have hr := regroup_index c.1 (⟨c.2.1.val,c.2.1.isLt.trans_le hNM⟩ : Fin M)
    c.2.2.1 (⟨c.2.2.2.1.val,c.2.2.2.1.isLt.trans_le hNM⟩ : Fin M) c.2.2.2.2
  exact (congrArg x hr).trans
    (crop_entry hNM x c.1 c.2.1 c.2.2.1 c.2.2.2.1 c.2.2.2.2).symm

theorem crop_transpose_pad {M : ℕ} (hNM : N ≤ M) (zero : α)
    (x : Fin (volume P N G B) → α) : crop hNM (transpose (pad M zero x)) = transpose x := by
  funext z
  rw [← index_coordinates z]
  rw [crop_entry,transpose_entry,pad_entry]
  simp only [dite_eq_left (coordinates z).2.2.2.1.isLt,
    dite_eq_left (coordinates z).2.1.isLt,transpose_entry]

theorem cropStages_transpose_pad {M : ℕ} (hNM : N ≤ M) (zero : α)
    (x : Fin (volume P N G B) → α) :
    cropStages hNM (transpose (pad M zero x)) = transpose x := by
  rw [cropStages_eq,crop_transpose_pad]

theorem volume_bound (P N G B M q : ℕ) (h : M ≤ q*N) :
    volume P M G B ≤ q^2*volume P N G B := by
  have hs : M^2 ≤ (q*N)^2 := Nat.pow_le_pow_left h 2
  have hm := Nat.mul_le_mul_left (P*G*B) hs
  simpa only [volume] using (show P*M*G*M*B ≤ q^2*(P*N*G*N*B) by nlinarith [hm])

end IntegerMultBounds.Machine.RadixRangePadding
