module

public import IntegerMultBounds.MathlibTM2.M6.MoveProfile
public import IntegerMultBounds.Networks.Certificates.PR589.Copy.Boundary

/-! The address word for each retained source supplies the temporary read by every
ADD in its COPY window. Streams are indexed by the modular address halves. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6

open Matrix IntegerMultBounds.Networks IntegerMultBounds.Networks.Certificates.PR589
open IntegerMultBounds.Networks.Shared50ModularControl
open M8.Exchange (exchange)

private def streamFrame {R : Type*} [CommRing R] (P : Fin 636 → Matrix (Fin 8) (Fin 8) R)
    (idem : ∀ i, P i * P i = P i) (label : ℕ) :
    FramedCircuit.Frame (ZMod 2) (Swap.Shear.State (Fin 8) R → ZMod 2) :=
  let i : Fin 636 := ⟨label % 636, Nat.mod_lt _ (by decide)⟩
  { toFun := fun f x => f (exchange (P i) x)
    invFun := fun f x => f (exchange (P i) x)
    left_inv := fun f => by funext x; simp only [M8.Global.exchange_involutive (idem _) _]
    right_inv := fun f => by funext x; simp only [M8.Global.exchange_involutive (idem _) _]
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

/-- The COPY window explicitly reads the retained stream at the address computed
by its modular program, fans out from register 661, then clears that register. -/
def scatterWindow {R : Type*} [CommRing R]
    (word : ℕ × ℕ → List (AffineFieldProgram.Op (Fin 8) R)) (life : Copy.Lifecycle)
    (stored : ℕ → Swap.Shear.State (Fin 8) R → ZMod 2) : ℕ → Swap.Shear.State (Fin 8) R → ZMod 2 :=
  let temp := fun x => stored life.source (AffineFieldProgram.run (word (life.sourceFrame, 0)) x)
  Function.update (Copy.addTargets life.targets (Function.update stored 661 temp)) 661 0

theorem modular_scatter (w : ℕ) :
    let R := ZMod (prime ^ w)
    let E := Swap.Shear.State (Fin 8) R → ZMod 2
    ∃ (frame : ℕ → FramedCircuit.Frame (ZMod 2) E)
      (word : ℕ × ℕ → List (AffineFieldProgram.Op (Fin 8) R)),
      (∀ p, Geometry.Moves.CheckedPair p → ∀ f : E,
        (fun x => f (AffineFieldProgram.run (word p) x)) = frame p.2 ((frame p.1).symm f)) ∧
      LocalMoveProfile word ∧
      (∀ bank : ℕ → E, Copy.lifecycles.foldl (fun b l => scatterWindow word l b) bank =
        Copy.run frame Copy.lifecycles bank) ∧
      ∀ stored : Fin 661 → E,
        let input := FramedCircuit.encode (fun j => frame (Frames.beforeScatter j)) (Copy.extendStored stored)
        let output := Copy.lifecycles.foldl (fun bank life => scatterWindow word life bank) input
        output 661 = 0 ∧ ∀ i : Fin 661, output i.val = frame (Frames.beforeScatter i.val)
          (FramedCircuit.moduleRun (sectionscatter.map RawGate.toCircuit) (Copy.extendStored stored) i.val) := by
  intro R E
  obtain ⟨P, word, idem, commute, spec, profile⟩ := modular_move_profile w
  let frame := streamFrame P idem
  have read (p : ℕ × ℕ) (h : Geometry.Moves.CheckedPair p) (f : E) :
      (fun x => f (AffineFieldProgram.run (word p) x)) = frame p.2 ((frame p.1).symm f) := by
    let i : Fin 636 := ⟨p.1, h.1⟩
    let j : Fin 636 := ⟨p.2, h.2.1⟩
    have index (k : Fin 636) : (⟨k.val % 636, Nat.mod_lt _ (by decide)⟩ : Fin 636) = k :=
      Fin.ext (Nat.mod_eq_of_lt k.isLt)
    funext x
    rw [spec p h]
    change f (exchange (P j) (exchange (P i) x)) =
      f (exchange (P ⟨i.val % 636, _⟩) (exchange (P ⟨j.val % 636, _⟩) x))
    rw [index i, index j, M8.Global.exchange_exchange, M8.Global.exchange_exchange,
      commute i j h, add_comm (P i)]
  have step (life : Copy.Lifecycle) (hl : life ∈ Copy.lifecycles) (bank : ℕ → E) :
      scatterWindow word life bank = Copy.execute frame life bank := by
    have valid : ∀ l ∈ Copy.lifecycles, Geometry.Moves.CheckedPair (l.sourceFrame, 0) := by decide +kernel
    rw [scatterWindow, Copy.execute, read _ (valid life hl)]
  have fold (ls : List Copy.Lifecycle) (hl : ∀ l ∈ ls, l ∈ Copy.lifecycles) (bank : ℕ → E) :
      ls.foldl (fun b l => scatterWindow word l b) bank = Copy.run frame ls bank := by
    induction ls generalizing bank with
    | nil => rfl
    | cons l ls ih =>
      rw [List.foldl_cons, step l (hl _ List.mem_cons_self), Copy.run]
      exact ih (fun k hk => hl _ (List.mem_cons_of_mem _ hk)) _
  refine ⟨frame, word, read, profile, fold _ (fun _ h => h), ?_⟩
  intro stored input output
  dsimp only [output]
  rw [fold _ (fun _ h => h)]
  exact ⟨Copy.temporary_cleared frame stored, Copy.decoded_scatter frame stored⟩

end IntegerMultBounds.MathlibTM2.M6
