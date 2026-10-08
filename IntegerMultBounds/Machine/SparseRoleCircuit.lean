import IntegerMultBounds.Machine.PointwiseRoleCircuit
import IntegerMultBounds.Networks.SparseCircuit

/-! Physical realization of Networks.SparseCircuit's fixed one-source XOR
lists. Each scalar register is a literal bit stream. Gate placement, counted
pointwise XOR, head restoration and every list join are all charged. -/
namespace IntegerMultBounds.Machine.SparseRoleCircuit
open Networks
variable {t a n : ℕ}
noncomputable section

def encode (x : ZMod 2) : Fin (a+4) := bitSymbol (decide (x = 1))

theorem encode_add (x y : ZMod 2) :
    PointwiseBinary.xorSymbol (a := a) (encode x) (encode y) = encode (y+x) := by
  fin_cases x <;> fin_cases y <;> rfl

def encoded (data : Fin t → Fin n → ZMod 2) : Fin t → Fin n → Fin (a+4) :=
  fun k i => encode (data k i)

def scalar (g : PointwiseRoleGate.Gate t) : Circuit.Gate (Fin t) (ZMod 2) :=
  ReversibleFanout.add g.dst g.src

private theorem gate_encoded (g : PointwiseRoleGate.Gate t) (data : Fin t → Fin n → ZMod 2) :
    PointwiseRoleGate.applyGate g PointwiseBinary.xorSymbol (encoded (a := a) data) =
      encoded (fun k i => (scalar g).run (fun k => data k i) k) := by
  funext k i
  by_cases hk : k = g.dst
  · subst k
    simp only [PointwiseRoleGate.applyGate,Function.update_self,encoded,scalar,
      ReversibleFanout.add_run]
    simp only [encode_add]
  · simp [PointwiseRoleGate.applyGate,encoded,scalar,ReversibleFanout.add_run,hk]

/-- Circuit semantics apply separately at every literal stream position. -/
theorem execute_encoded (gs : List (PointwiseRoleGate.Gate t)) (data : Fin t → Fin n → ZMod 2) :
    PointwiseRoleCircuit.execute PointwiseBinary.xorSymbol gs (encoded (a := a) data) =
      encoded (fun k i => Circuit.run (gs.map scalar) (fun k => data k i) k) := by
  induction gs generalizing data with
  | nil => rfl
  | cons g gs ih =>
    simp only [PointwiseRoleCircuit.execute,gate_encoded,ih,List.map_cons,Circuit.run_cons]

def gates {α β : Type*} (dst : α → Fin t) (src : β → Fin t)
    (separate : ∀ x y, dst x ≠ src y) (entries : List (α × β)) : List (PointwiseRoleGate.Gate t) :=
  entries.map (fun e => ⟨src e.2,dst e.1,(separate e.1 e.2).symm⟩)

theorem gates_scalar {α β : Type*} (dst : α → Fin t) (src : β → Fin t)
    (separate : ∀ x y, dst x ≠ src y) (entries : List (α × β)) :
    (gates dst src separate entries).map scalar = Networks.SparseCircuit.copies dst src entries := by
  simp [gates,scalar,Networks.SparseCircuit.copies,List.map_map]

def program {α β : Type*} (dst : α → Fin t) (src : β → Fin t)
    (separate : ∀ x y, dst x ≠ src y) (entries : List (α × β)) :=
  PointwiseRoleCircuit.program (PointwiseBinary.xorSymbol (a := a)) (gates dst src separate entries)

/-- The literal machine implements the existing scalar sparse circuit on all
stream entries simultaneously, preserving backgrounds, heads, and count tapes.
Repeated targets and repeated source labels are handled by the circuit theorem. -/
theorem copies_hoare {α β : Type*} (dst : α → Fin t) (src : β → Fin t)
    (separate : ∀ x y, dst x ≠ src y) (entries : List (α × β))
    (background : Fin t → ℤ → Fin (a+4)) (origins : Fin t → ℤ)
    (data : Fin t → Fin n → ZMod 2) (bs : List Bool) (hn : Counter.value bs = n) :
    HoareTime (program dst src separate entries)
      (fun w => w = PointwiseRoleGate.bank background origins (encoded data) bs)
      (fun w => w = PointwiseRoleGate.bank background origins
        (encoded (fun k i => Circuit.run (Networks.SparseCircuit.copies dst src entries)
          (fun k => data k i) k)) bs)
      (entries.length*(14*n+14*bs.length+34)) := by
  have hh := PointwiseRoleCircuit.circuit_hoare PointwiseBinary.xorSymbol (gates dst src separate entries)
    background origins (encoded data) bs hn
  rw [execute_encoded,gates_scalar] at hh
  simpa only [program,gates,List.length_map] using hh

/-- An explicit pointwise sum postcondition for the physical sparse XOR list. -/
theorem copies_sum_hoare {α β : Type*} (dst : α → Fin t) (src : β → Fin t)
    (separate : ∀ x y, dst x ≠ src y) (entries : List (α × β))
    (background : Fin t → ℤ → Fin (a+4)) (origins : Fin t → ℤ)
    (data : Fin t → Fin n → ZMod 2) (bs : List Bool) (hn : Counter.value bs = n) :
    HoareTime (program dst src separate entries)
      (fun w => w = PointwiseRoleGate.bank background origins (encoded data) bs)
      (fun w => w = PointwiseRoleGate.bank background origins
        (encoded (fun k i => data k i+
          (entries.map (fun e => if dst e.1 = k then data (src e.2) i else 0)).sum)) bs)
      (entries.length*(14*n+14*bs.length+34)) := by
  simpa only [Networks.SparseCircuit.copies_run dst src entries separate] using
    copies_hoare dst src separate entries background origins data bs hn

/-- A fixed sparse list has linear stream-volume cost, including normalization
and every real sequence join. -/
theorem cost_linear (gateCount n : ℕ) (bs : List Bool) (hn : Counter.value bs = n)
    (hc : GrowingCounterData.Canonical bs) (hpos : 0 < n) :
    gateCount*(14*n+14*bs.length+34) ≤ 76*gateCount*n := by
  have hh := PointwiseBinaryNormalized.cost_linear bs hc
  rw [hn] at hh
  have hb : 14*n+14*bs.length+34 ≤ 76*n := by omega
  have hm := Nat.mul_le_mul_left gateCount hb
  nlinarith

end
end IntegerMultBounds.Machine.SparseRoleCircuit
