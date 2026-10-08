import IntegerMultBounds.Machine.FiberLayoutData
import IntegerMultBounds.Networks.OrderedAffine
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Rev

/-! One common physical row-major layout for every target of an ordered-affine
schedule. The first coordinate is most significant and an arbitrary trailing
record is least significant. Target-specific fibers are views of the same
finite array, not independently supplied address families. -/
namespace IntegerMultBounds.Machine.FlatCoordinateLayout
noncomputable section
variable {d Q W : ℕ} [NeZero Q]

/-- Encode coordinates most-significant first using the standard digit equivalence. -/
def rank (x : Fin d → ZMod Q) : Fin (Q^d) :=
  finFunctionFinEquiv (fun i => (ZMod.finEquiv Q).symm (x i.rev))

/-- Exact inverse: each coordinate is its fixed-width digit slice. -/
def coordinates (n : Fin (Q^d)) (i : Fin d) : ZMod Q :=
  ZMod.finEquiv Q (finFunctionFinEquiv.symm n i.rev)

@[simp] theorem coordinates_rank (x : Fin d → ZMod Q) : coordinates (rank x) = x := by
  funext i
  simp [coordinates,rank]

@[simp] theorem rank_coordinates (n : Fin (Q^d)) : rank (coordinates n) = n := by
  unfold rank coordinates
  have he : (fun i : Fin d => (ZMod.finEquiv Q).symm
      (ZMod.finEquiv Q (finFunctionFinEquiv.symm n i.rev.rev))) = finFunctionFinEquiv.symm n := by
    funext i; simp
  rw [he,Equiv.apply_symm_apply]

def rankEquiv : (Fin d → ZMod Q) ≃ Fin (Q^d) :=
  ⟨rank,coordinates,coordinates_rank,rank_coordinates⟩

/-- The same array index is used before and after every scheduled operation. -/
def index (x : Fin d → ZMod Q) (j : Fin W) : Fin (Q^d*W) := finProdFinEquiv (rank x,j)

def arrayEquiv : ((Fin d → ZMod Q) × Fin W) ≃ Fin (Q^d*W) :=
  (Equiv.prodCongr rankEquiv (Equiv.refl (Fin W))).trans finProdFinEquiv

@[simp] theorem index_val (x : Fin d → ZMod Q) (j : Fin W) :
    (index x j).val = (rank x).val*W+j.val := by simp [index,finProdFinEquiv,Nat.mul_comm,Nat.add_comm]

/-- Number of equally-sized fields to the right of a chosen target. -/
def suffixFields (t : Fin d) := d-1-t.val

def prefixSize (t : Fin d) := Q^t.val

def suffixSize (t : Fin d) := Q^suffixFields t*W

omit [NeZero Q] in
/-- Changing the target only changes the split; the physical volume is identical. -/
theorem split_volume (t : Fin d) : Q^d*W = prefixSize (Q := Q) t*(Q*suffixSize (Q := Q) (W := W) t) := by
  have he : d = t.val+1+suffixFields t := by unfold suffixFields; omega
  unfold prefixSize suffixSize
  conv_lhs => rw [he,pow_add,pow_add]
  simp only [pow_one]
  ring

@[simp] theorem finEquiv_symm_val (z : ZMod Q) : ((ZMod.finEquiv Q).symm z).val = z.val := by
  cases Q with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n => rfl

@[simp] theorem rev_val (t : Fin d) : t.rev.val = suffixFields t := by
  simp [Fin.val_rev,suffixFields,Nat.sub_sub,Nat.add_comm]

/-- Exact coordinate extraction, including the degenerate one-element modulus. -/
theorem coordinate_value (x : Fin d → ZMod Q) (t : Fin d) :
    ((rank x).val/Q^suffixFields t)%Q = (x t).val := by
  have he := congrFun (finFunctionFinEquiv.symm_apply_apply
    (fun i : Fin d => (ZMod.finEquiv Q).symm (x i.rev))) t.rev
  have hv := congrArg Fin.val he
  change (rank x).val/Q^t.rev.val%Q = ((ZMod.finEquiv Q).symm (x t.rev.rev)).val at hv
  simpa only [Fin.rev_rev,rev_val,finEquiv_symm_val] using hv

def prefixIndex (x : Fin d → ZMod Q) (t : Fin d) : ℕ := (rank x).val/(Q*Q^suffixFields t)

def suffix (x : Fin d → ZMod Q) (t : Fin d) (j : Fin W) : ℕ :=
  ((rank x).val%Q^suffixFields t)*W+j.val

/-- A physical prefix is within its exact target-specific range. -/
theorem prefix_lt (x : Fin d → ZMod Q) (t : Fin d) : prefixIndex x t < prefixSize (Q := Q) t := by
  have hpos : 0 < Q*Q^suffixFields t := Nat.mul_pos (NeZero.pos Q) (pow_pos (NeZero.pos Q) _)
  apply (Nat.div_lt_iff_lt_mul hpos).2
  have he : Q^d = Q^t.val*(Q*Q^suffixFields t) := by
    have hd : d = t.val+1+suffixFields t := by unfold suffixFields; omega
    conv_lhs => rw [hd,pow_add,pow_add,pow_one]
    ring
  simpa only [he,prefixSize] using (rank x).isLt

/-- The entire suffix, including its record position, is one preserved block index. -/
theorem suffix_lt (x : Fin d → ZMod Q) (t : Fin d) (j : Fin W) :
    suffix x t j < suffixSize (Q := Q) (W := W) t := by
  have hm := Nat.mod_lt (rank x).val (pow_pos (NeZero.pos Q) (suffixFields t))
  unfold suffix suffixSize
  nlinarith [j.isLt]

private theorem rank_decompose (x : Fin d → ZMod Q) (t : Fin d) :
    (rank x).val = prefixIndex x t*(Q*Q^suffixFields t)+(x t).val*Q^suffixFields t+
      (rank x).val%Q^suffixFields t := by
  have h₁ := Nat.mod_add_div (rank x).val (Q^suffixFields t)
  have h₂ := Nat.mod_add_div ((rank x).val/Q^suffixFields t) Q
  rw [coordinate_value] at h₂
  have hd : ((rank x).val/Q^suffixFields t)/Q = prefixIndex x t := by
    rw [Nat.div_div_eq_div_mul]
    simp only [prefixIndex,Nat.mul_comm]
  rw [hd] at h₂
  rw [← h₂] at h₁
  nlinarith [h₁]

/-- The chosen fiber view exactly partitions the common row-major address. -/
theorem index_split (x : Fin d → ZMod Q) (t : Fin d) (j : Fin W) :
    (index x j).val = prefixIndex x t*(Q*suffixSize (Q := Q) (W := W) t)+
      (x t).val*suffixSize (Q := Q) (W := W) t+suffix x t j := by
  rw [index_val,rank_decompose x t]
  unfold suffixSize suffix
  ring

/-- An earlier control is extracted from the same physical prefix number. -/
theorem earlier_control (x : Fin d → ZMod Q) (t k : Fin d) (hk : k < t) :
    (prefixIndex x t/Q^(t.val-1-k.val))%Q = (x k).val := by
  have he : (Q*Q^suffixFields t)*Q^(t.val-1-k.val) = Q^suffixFields k := by
    rw [← pow_succ',← pow_add]
    congr 1
    unfold suffixFields
    have := t.isLt
    have hlt : k.val < t.val := hk
    omega
  rw [prefixIndex,Nat.div_div_eq_div_mul,he,coordinate_value]

/-- Updating one coordinate changes its weighted contribution only. -/
theorem rank_update_balance (x : Fin d → ZMod Q) (t : Fin d) (z : ZMod Q) :
    (rank (Function.update x t z)).val+(x t).val*Q^suffixFields t =
      (rank x).val+z.val*Q^suffixFields t := by
  simp only [rank,finFunctionFinEquiv_apply]
  have he : (fun i : Fin d => ((ZMod.finEquiv Q).symm (Function.update x t z i.rev)).val*Q^i.val) =
      Function.update (fun i : Fin d => ((ZMod.finEquiv Q).symm (x i.rev)).val*Q^i.val)
        t.rev (z.val*Q^suffixFields t) := by
    funext i
    by_cases hi : i = t.rev
    · subst i; simp only [Fin.rev_rev,Function.update_self,finEquiv_symm_val,rev_val]
    · have ht : i.rev ≠ t := by intro h; apply hi; have hh := congrArg Fin.rev h; simpa using hh
      simp [Function.update_of_ne hi,Function.update_of_ne ht]
  rw [he,Finset.sum_update_of_mem (Finset.mem_univ t.rev)]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ t.rev)]
  simp only [Finset.sdiff_singleton_eq_erase,Fin.rev_rev,rev_val,finEquiv_symm_val]
  omega

/-- The same prefix and complete suffix surround the updated target. -/
theorem index_update (x : Fin d → ZMod Q) (t : Fin d) (z : ZMod Q) (j : Fin W) :
    (index (Function.update x t z) j).val = prefixIndex x t*(Q*suffixSize (Q := Q) (W := W) t)+
      z.val*suffixSize (Q := Q) (W := W) t+suffix x t j := by
  have hu := rank_update_balance x t z
  have hd := rank_decompose x t
  rw [index_val]
  unfold suffixSize suffix
  nlinarith

/-- Concrete scaling destination equals the ordered-affine coordinate update. -/
theorem scale_destination (x : Fin d → ZMod Q) (t : Fin d) (a : ZMod Q) (j : Fin W) :
    (index (Networks.OrderedAffine.execute (.scale t a) x) j).val =
      prefixIndex x t*(Q*suffixSize (Q := Q) (W := W) t)+
        (a*x t).val*suffixSize (Q := Q) (W := W) t+suffix x t j :=
  index_update x t (a*x t) j

/-- Concrete prefix-controlled rotation equals the ordered-affine shift. -/
theorem shift_destination (x : Fin d → ZMod Q) (t k : Fin d) (a : ZMod Q) (j : Fin W) :
    (index (Networks.OrderedAffine.execute (.shift t k a) x) j).val =
      prefixIndex x t*(Q*suffixSize (Q := Q) (W := W) t)+
        (((x t).val+(a*x k).val)%Q)*suffixSize (Q := Q) (W := W) t+suffix x t j := by
  rw [show Networks.OrderedAffine.execute (.shift t k a) x = Function.update x t (x t+a*x k) by rfl,
    index_update,ZMod.val_add]


/-- Target-specific array view is only a size cast of the common physical array. -/
def fiberView {α : Type*} (a : Fin (Q^d*W) → α) (t : Fin d) :
    Fin (prefixSize (Q := Q) t*(Q*suffixSize (Q := Q) (W := W) t)) → α :=
  fun i => a (Fin.cast (split_volume t).symm i)

omit [NeZero Q] in
/-- Every target view has literally the same serialized source word. -/
theorem fiberView_word {α : Type*} (a : Fin (Q^d*W) → α) (t : Fin d) :
    List.ofFn (fiberView a t) = List.ofFn a :=
  (List.ofFn_congr (split_volume t) a).symm

/-- Typed fiber positions are the common array positions. -/
theorem fiberView_index {α : Type*} (a : Fin (Q^d*W) → α) (x : Fin d → ZMod Q)
    (t : Fin d) (j : Fin W) :
    fiberView a t (FiberLayoutData.index ⟨prefixIndex x t,prefix_lt x t⟩
      ⟨(x t).val,ZMod.val_lt _⟩ ⟨suffix x t j,suffix_lt x t j⟩) = a (index x j) := by
  unfold fiberView
  congr 1
  apply Fin.ext
  simpa only [Fin.val_cast,FiberLayoutData.index_val] using (index_split x t j).symm

/-- Concrete per-fiber scaling correctness implies common-coordinate transport. -/
theorem scale_transport {α : Type*} (a : Fin (Q^d*W) → α) (out : List α)
    (t : Fin d) (u : ZMod Q)
    (h : ∀ (p : Fin (prefixSize (Q := Q) t)) (y : Fin Q)
        (j : Fin (suffixSize (Q := Q) (W := W) t)),
      out[p.val*(Q*suffixSize (Q := Q) (W := W) t)+
        (u*(y.val : ZMod Q)).val*suffixSize (Q := Q) (W := W) t+j.val]? =
          some (fiberView a t (FiberLayoutData.index p y j)))
    (x : Fin d → ZMod Q) (j : Fin W) :
    out[(index (Networks.OrderedAffine.execute (.scale t u) x) j).val]? =
      some (a (index x j)) := by
  have hh := h ⟨prefixIndex x t,prefix_lt x t⟩ ⟨(x t).val,ZMod.val_lt _⟩
    ⟨suffix x t j,suffix_lt x t j⟩
  rw [fiberView_index] at hh
  simpa only [scale_destination,ZMod.natCast_zmod_val] using hh

/-- A physical prefix offset which agrees with its extracted control gives
exactly the common-coordinate ordered-affine shift. -/
theorem shift_transport {α : Type*} (a : Fin (Q^d*W) → α) (out : List α)
    (t k : Fin d) (u : ZMod Q) (offset : Fin (prefixSize (Q := Q) t) → ℕ)
    (hoffset : ∀ x : Fin d → ZMod Q,
      offset ⟨prefixIndex x t,prefix_lt x t⟩ = (u*x k).val)
    (h : ∀ (p : Fin (prefixSize (Q := Q) t)) (y : Fin Q)
        (j : Fin (suffixSize (Q := Q) (W := W) t)),
      out[p.val*(Q*suffixSize (Q := Q) (W := W) t)+
        ((y.val+offset p)%Q)*suffixSize (Q := Q) (W := W) t+j.val]? =
          some (fiberView a t (FiberLayoutData.index p y j)))
    (x : Fin d → ZMod Q) (j : Fin W) :
    out[(index (Networks.OrderedAffine.execute (.shift t k u) x) j).val]? =
      some (a (index x j)) := by
  have hh := h ⟨prefixIndex x t,prefix_lt x t⟩ ⟨(x t).val,ZMod.val_lt _⟩
    ⟨suffix x t j,suffix_lt x t j⟩
  rw [fiberView_index,hoffset] at hh
  simpa only [shift_destination] using hh

/-- For an earlier control, the literal physical prefix digit supplies the
required shift coefficient without an abstract address-family hypothesis. -/
theorem shift_offset (x : Fin d → ZMod Q) (t k : Fin d) (hk : k < t) (u : ZMod Q) :
    (u * (((prefixIndex x t / Q^(t.val-1-k.val))%Q : ℕ) : ZMod Q)).val =
      (u*x k).val := by
  rw [earlier_control x t k hk,ZMod.natCast_zmod_val]


/-- Prime-power coordinate fields use exactly the radix slice consumed by the
actual prefix-counter-controlled shift machines. -/
theorem earlier_control_radix {radix b : ℕ} [NeZero (radix^b)]
    (x : Fin d → ZMod (radix^b)) (t k : Fin d) (hk : k < t) :
    (prefixIndex x t/radix^(b*(t.val-1-k.val)))%(radix^b) = (x k).val := by
  simpa only [pow_mul] using earlier_control x t k hk

end
end IntegerMultBounds.Machine.FlatCoordinateLayout
