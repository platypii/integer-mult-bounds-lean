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

private def scatterFrame {R : Type*} [CommRing R] (P : Fin 636 → Matrix (Fin 8) (Fin 8) R)
    (idem : ∀ i, P i * P i = P i) (label : ℕ) :
    FramedCircuit.Frame (ZMod 2) (Swap.Shear.State (Fin 8) R → ZMod 2) :=
  let i : Fin 636 := ⟨label % 636, Nat.mod_lt _ (by decide)⟩
  { toFun := fun f x => f (exchange (P i) (exchange (P 0) x))
    invFun := fun f x => f (exchange (P 0) (exchange (P i) x))
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
      (retainedCopyEdges.map word).map AffineFieldProgram.interchanges = List.replicate 9 7 ∧
      ∀ stored : Fin 661 → E,
        let input := FramedCircuit.encode (fun j => frame (Frames.beforeScatter j)) (Copy.extendStored stored)
        let output := Copy.lifecycles.foldl (fun bank life => scatterWindow word life bank) input
        output 661 = 0 ∧ ∀ i : Fin 661, output i.val = frame (Frames.beforeScatter i.val)
          (FramedCircuit.moduleRun (sectionscatter.map RawGate.toCircuit) (Copy.extendStored stored) i.val) := by
  intro R E
  obtain ⟨P, word, idem, spec, _, _, count, _⟩ := modular_move_profile w
  let frame := scatterFrame P idem
  have step (life : Copy.Lifecycle) (hl : life ∈ Copy.lifecycles) (bank : ℕ → E) :
      scatterWindow word life bank = Copy.execute frame life bank := by
    have valid : ∀ l ∈ Copy.lifecycles, Geometry.Moves.CheckedPair (l.sourceFrame, 0) := by decide +kernel
    have h := valid life hl
    have run := (spec _ h).2
    have temp : (fun x => bank life.source (AffineFieldProgram.run (word (life.sourceFrame, 0)) x)) =
        frame 0 ((frame life.sourceFrame).symm (bank life.source)) := by
      funext x
      rw [run]
      let src : Fin 636 := ⟨life.sourceFrame, h.1⟩
      let idx : Fin 636 := ⟨life.sourceFrame % 636, Nat.mod_lt _ (by decide)⟩
      have eq : idx = src := Fin.ext (Nat.mod_eq_of_lt h.1)
      change bank life.source (exchange (P 0) (exchange (P src) x)) =
        bank life.source (exchange (P 0) (exchange (P idx) (exchange (P 0) (exchange (P 0) x))))
      rw [eq, M8.Global.exchange_involutive (idem 0) x]
    rw [scatterWindow, Copy.execute, temp]
  have fold (ls : List Copy.Lifecycle) (hl : ∀ l ∈ ls, l ∈ Copy.lifecycles) (bank : ℕ → E) :
      ls.foldl (fun b l => scatterWindow word l b) bank = Copy.run frame ls bank := by
    induction ls generalizing bank with
    | nil => rfl
    | cons l ls ih =>
      rw [List.foldl_cons, step l (hl _ List.mem_cons_self), Copy.run]
      exact ih (fun k hk => hl _ (List.mem_cons_of_mem _ hk)) _
  refine ⟨frame, word, count, ?_⟩
  intro stored input output
  dsimp only [output]
  rw [fold _ (fun _ h => h)]
  exact ⟨Copy.temporary_cleared frame stored, Copy.decoded_scatter frame stored⟩

end IntegerMultBounds.MathlibTM2.M6
