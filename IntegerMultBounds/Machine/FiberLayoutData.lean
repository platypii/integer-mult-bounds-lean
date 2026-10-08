import IntegerMultBounds.Machine.BlockRotationData
import IntegerMultBounds.Machine.PrefixAddressData
import Mathlib.Data.List.OfFn

/-! Canonical whole-array fibers, constructed from the physical array itself.
A prefix is most significant, a target coordinate comes next, and every symbol
of the arbitrary suffix record remains least significant. -/
namespace IntegerMultBounds.Machine.FiberLayoutData
variable {α : Type*} {P Q B : ℕ}

/-- Row-major physical position, without storing an address alongside a record. -/
def index (p : Fin P) (y : Fin Q) (j : Fin B) : Fin (P*(Q*B)) :=
  finProdFinEquiv (p,finProdFinEquiv (y,j))

@[simp] theorem index_val (p : Fin P) (y : Fin Q) (j : Fin B) :
    (index p y j).val = p.val*(Q*B)+y.val*B+j.val := by
  simp [index,finProdFinEquiv]; ring

def fiber (a : Fin (P*(Q*B)) → α) (p : Fin P) : List (List α) :=
  List.ofFn (fun y : Fin Q => List.ofFn (fun j : Fin B => a (index p y j)))

def fibers (a : Fin (P*(Q*B)) → α) : List (List (List α)) := List.ofFn (fiber a)

@[simp] theorem fiber_length (a : Fin (P*(Q*B)) → α) (p : Fin P) : (fiber a p).length = Q := by
  simp [fiber]

theorem fiber_uniform (a : Fin (P*(Q*B)) → α) (p : Fin P) :
    BlockRotationData.Uniform B (fiber a p) := by
  intro block hb
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hb
  simp

/-- Splitting the physical array into represented fibers introduces no assumed
address family: concatenating the constructed fibers is literally the array. -/
theorem flatten_fibers (a : Fin (P*(Q*B)) → α) :
    ((fibers a).map List.flatten).flatten = List.ofFn a := by
  rw [fibers,List.map_ofFn,List.ofFn_mul a]
  congr 1
  apply congrArg List.ofFn
  funext p
  change (fiber a p).flatten = _
  rw [List.ofFn_mul]
  unfold fiber
  congr 1
  apply congrArg List.ofFn
  funext y
  apply congrArg List.ofFn
  funext j
  congr 1
  apply Fin.ext
  simp [index,finProdFinEquiv]
  ring

/-- A selected offset may depend on every prefix coordinate. -/
def translated (a : Fin (P*(Q*B)) → α) (offset : Fin P → ℕ) : List α :=
  (List.ofFn (fun p : Fin P => (BlockRotationData.rotate (offset p) (fiber a p)).flatten)).flatten

/-- Destination semantics on the complete physical array. The complete suffix
position j survives even when B contains arbitrary temporary fields/records. -/
theorem translated_entry (a : Fin (P*(Q*B)) → α) (offset : Fin P → ℕ)
    (p : Fin P) (y : Fin Q) (j : Fin B) :
    (translated a offset)[p.val*(Q*B)+((y.val+offset p)%Q)*B+j.val]? = some (a (index p y j)) := by
  have hu : BlockRotationData.Uniform (Q*B)
      (List.ofFn (fun p : Fin P => (BlockRotationData.rotate (offset p) (fiber a p)).flatten)) := by
    intro block hb
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hb
    rw [BlockRotationData.rotated_volume _ B _ (fiber_uniform a i),fiber_length]
  have hi : ((y.val+offset p)%Q)*B+j.val < Q*B := by
    have hm := Nat.mod_lt (y.val+offset p) (Nat.zero_lt_of_lt y.isLt)
    nlinarith [j.isLt]
  change (List.ofFn _).flatten[_]? = _
  rw [show p.val*(Q*B)+((y.val+offset p)%Q)*B+j.val =
    p.val*(Q*B)+(((y.val+offset p)%Q)*B+j.val) by omega]
  rw [BlockRotationData.flatten_index (Q*B) _ hu p.val _ (by simp) hi]
  simp only [List.getElem_ofFn,Fin.eta]
  have h := BlockRotationData.payload_destination_entry (offset p) B (fiber a p)
    (fiber_uniform a p) y.val j.val (by simp) j.isLt
  simpa only [fiber_length,fiber,List.length_ofFn,List.getElem_ofFn,Fin.eta] using h

/-- For every physical prefix fiber, a selected actual counter field supplies
exactly the corresponding ordered-coordinate offset. -/
theorem scheduled_entry {radix c : ℕ} (hq : 2 ≤ radix)
    (low high : List (Fin c)) (control : Fin c) (hn : (low++control::high).Nodup)
    (width : Fin c → ℕ) (coefficient : ℕ → ℕ)
    (a : Fin (radix^PrefixAddressData.widthSum (low++control::high) width*(Q*B)) → α)
    (p : Fin (radix^PrefixAddressData.widthSum (low++control::high) width))
    (y : Fin Q) (j : Fin B) :
    let offsets := fun p : Fin (radix^PrefixAddressData.widthSum (low++control::high) width) =>
      coefficient (RadixDigits.value (PrefixCounterData.iterateFields hq (low++control::high) p.val
        (fun i => RadixCounterData.zeros hq (width i)) control))
    (translated a offsets)[p.val*(Q*B)+
      ((y.val+coefficient ((p.val/radix^PrefixAddressData.widthSum low width)%radix^(width control)))%Q)*B+j.val]? =
      some (a (index p y j)) := by
  dsimp only
  have he := PrefixAddressData.enumeration_selected hq low high control hn width p.val p.isLt
  have h := translated_entry a
    (fun p => coefficient (RadixDigits.value (PrefixCounterData.iterateFields hq (low++control::high) p.val
      (fun i => RadixCounterData.zeros hq (width i)) control))) p y j
  simpa only [he] using h

/-- Physical volume includes every prefix, target coordinate and suffix symbol. -/
theorem translated_length (a : Fin (P*(Q*B)) → α) (offset : Fin P → ℕ) :
    (translated a offset).length = P*(Q*B) := by
  rw [translated,BlockRotationData.uniform_volume (Q*B)]
  · simp
  · intro block hb
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hb
    rw [BlockRotationData.rotated_volume _ B _ (fiber_uniform a i),fiber_length]

end IntegerMultBounds.Machine.FiberLayoutData
