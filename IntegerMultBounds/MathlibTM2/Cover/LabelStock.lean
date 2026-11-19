module

public import IntegerMultBounds.MathlibTM2.Cover.LabelPadding
public import IntegerMultBounds.MathlibTM2.Cover.LabelTransport
public import IntegerMultBounds.MathlibTM2.Host.GatherSpread

/-! Spreading compact stock into the live positions of the physical label box. -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Cover.LabelStock
noncomputable section

open IntegerMultBounds.Machine
open IntegerMultBounds.Networks.Shared50ModularControl (prime prime_prime)
open RecursiveInterchangeLayout (Descriptor volume)
open LabelTransport (payload)
open LabelAddress (address)
open Host IntegerMultBounds.MathlibTM2.Stack
variable {m w : ℕ}
local instance : NeZero (prime^w) := ⟨(pow_pos prime_prime.pos _).ne'⟩

/-- The low digit of each atom of the label at physical bit offset `i`. -/
def residue (m w W i : ℕ) : Matrix (Fin m) (Fin m) (ZMod prime) := fun r c =>
  ((i / W / (prime^w)^FlatCoordinateLayout.suffixFields (finProdFinEquiv (c,r)) %
    (prime^w) : ℕ) : ZMod prime)

theorem residue_at (hw : 0 < w) (p W j : ℕ) (hj : j < W) (g : LabelPadding.Label m w) :
    residue m w W ((p*(prime^w)^(m*m)+(address g).val)*W+j) =
      (LabelRing.res prime w hw).mapMatrix g := by
  funext r c
  have hW : 0 < W := by omega
  simp only [residue]
  rw [Nat.mul_comm _ W, Nat.mul_add_div hW, Nat.div_eq_of_lt hj, Nat.add_zero]
  let e := FlatCoordinateLayout.suffixFields (finProdFinEquiv (c,r))
  have he : e < m*m := by
    have h := (finProdFinEquiv (c,r)).isLt
    dsimp [e, FlatCoordinateLayout.suffixFields]
    omega
  have hpow : (prime^w)^(m*m) = (prime^w)^e * ((prime^w)^(m*m-e-1)*(prime^w)) := by
    rw [← pow_succ, ← pow_add]
    congr 1
    omega
  change (((p*(prime^w)^(m*m)+(address g).val) / (prime^w)^e % (prime^w) : ℕ) : ZMod prime) = _
  rw [show p*(prime^w)^(m*m) = (prime^w)^e * ((p*(prime^w)^(m*m-e-1))*(prime^w)) by rw [hpow]; ring, Nat.mul_add_div (pow_pos (pow_pos prime_prime.pos w) e)]
  simp only [Nat.add_mod, Nat.mul_mod_left, Nat.zero_add, Nat.mod_mod]
  rw [show (address g).val / (prime^w)^e % (prime^w) = (g r c).val from LabelAddress.entry g r c]
  exact ZMod.natCast_val _

def live (m w W i : ℕ) : Bool := decide ((residue m w W i).det ≠ 0)

/-- Each spectator prefix has the same live and padding labels. -/
theorem count_boxes (m w n : ℕ) (select : Bool → Bool) :
    let box := (prime^w)^(m*m)
    let keep := fun j => select (live m w 1 j)
    (List.range (n*box)).countP keep = n*(List.range box).countP keep := by
  intro box keep
  have periodic (p j : ℕ) : keep (p*box+j) = keep j := by
    suffices h : residue m w 1 (p*box+j) = residue m w 1 j by simp [keep,live,h]
    funext r c
    let e := FlatCoordinateLayout.suffixFields (finProdFinEquiv (c,r))
    have he : e < m*m := by
      have bound := (finProdFinEquiv (c,r)).isLt
      dsimp [e,FlatCoordinateLayout.suffixFields]
      omega
    have factor : box = ((prime^w)^(m*m-e-1)*(prime^w)) * (prime^w)^e := by
      rw [← pow_succ, ← pow_add]
      exact congrArg ((prime^w)^·) (by omega)
    unfold residue
    simp only [Nat.div_one]
    change (((p*box+j)/(prime^w)^e%(prime^w) : ℕ) : ZMod prime) = _
    rw [factor,← Nat.mul_assoc,Nat.mul_comm _ ((prime^w)^e),Nat.mul_add_div (pow_pos (pow_pos prime_prime.pos w) e)]
    simp [← Nat.mul_assoc,Nat.add_mod,e]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.succ_mul,List.range_add,List.countP_append,List.countP_map,ih,Nat.succ_mul]
    simp only [Function.comp_def,periodic]

theorem live_at {v : Descriptor} {B : ℕ} (hw : 0 < w)
    (hv : v.beforeH = B*prime^(m*(w*m))) (g : LabelPadding.Label m w) (z : LabelEntry.Cell v B) :
    live m w (payload v) (RecursiveInterchangeLayout.index prime v z.a z.row
      (z.b.val*prime^(m*(w*m))+(address g).val) z.h z.mid z.d z.after) = true ↔ IsUnit g := by
  let j := ((z.h.val*v.between+z.mid.val)*prime^v.width+z.d.val)*v.afterD+z.after.val
  have pack {i n k s : ℕ} (hi : i < n) (hk : k < s) : i*s+k < n*s := by nlinarith
  have hj : j < payload v := pack (pack (pack z.h.isLt z.mid.isLt) z.d.isLt) z.after.isLt
  have radix : (prime^w)^(m*m) = prime^(m*(w*m)) := by rw [← pow_mul]; congr 1; ring
  have hi : RecursiveInterchangeLayout.index prime v z.a z.row
      (z.b.val*prime^(m*(w*m))+(address g).val) z.h z.mid z.d z.after =
      (((z.a.val*v.rows+z.row.val)*B+z.b.val)*(prime^w)^(m*m)+(address g).val)*payload v+j := by
    unfold RecursiveInterchangeLayout.index payload
    rw [hv, ← radix]
    dsimp [j]
    ring
  simp only [live, hi, residue_at hw _ _ _ hj, decide_eq_true_eq]
  exact (not_congr (LabelPadding.singular_iff hw g)).symm.trans (by simp)

private theorem spread_gather {α : Type*} (keep bit : α → Bool) (xs : List α) :
    spreadL ((xs.filter keep).map bit) (xs.map keep) =
      xs.map (fun i => if keep i then bit i else false) := by
  induction xs with
  | nil => rfl
  | cons i xs ih => cases h : keep i <;> simp [h, spreadL, ih]

/-- With one selector per physical bit, the host pass expands the compact input in tape order.
The input is specified only at live positions, and all three spare registers are restored. -/
theorem spread_stock {T Q A : ℕ} {P U : Type} (body : P → Pr P T Q A U)
    {src mask ts tm dst out : Fin T} (hr : GSRegs src mask ts tm dst out)
    (v : Descriptor) (m w : ℕ) (bit : ℕ → Bool) (u : HS T Q A U) (S : Stacks T A)
    (h : let keep := live m w (payload v)
     let xs := List.range (volume prime v)
     S.R mask = (xs.map keep).map bitSymbol ∧ S.R src = ((xs.filter keep).map bit).map bitSymbol)
    (hts : S.R ts = []) (htm : S.R tm = []) (hdst : S.R dst = []) :
    ∃ u' n, u'.user = u.user ∧ n ≤ 8 * volume prime v + 8 ∧
      Exec body (spread src mask ts tm dst out) (mk u S) n
        (mk u' { S with R := Function.update S.R out (((List.range (volume prime v)).map
                  (fun i => bitSymbol (if live m w (payload v) i then bit i else false))) ++ S.R out) }) := by
  let xs := List.range (volume prime v)
  let keep := live m w (payload v)
  have hc : (xs.map keep).count true = ((xs.filter keep).map bit).length := by
    simp [List.count_eq_countP, List.countP_map, Function.comp_def]
    exact List.countP_eq_length_filter
  obtain ⟨u', n, hu, hn, he⟩ := spread_exec body hr (xs.map keep) ((xs.filter keep).map bit)
    hc u S h.1 h.2 hts htm hdst
  refine ⟨u', n, hu, by simpa [xs] using hn, ?_⟩
  simpa only [spread_gather, List.map_map, Function.comp_def, xs, keep] using he

end
end IntegerMultBounds.MathlibTM2.Cover.LabelStock
