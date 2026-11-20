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

/-- The actual modular instructions are the specialization of a COPY word
whose two rational basis passes are executable at every width. -/
def SelectedCopyWord (w : ℕ) (ops : List (AffineFieldProgram.Op (Fin 8) (ZMod (prime^w)))) : Prop :=
  ∃ C : Matrix (Fin 8) (Fin 8) ℚ, CopyBasisPass C.adjugate ∧ CopyBasisPass C ∧
    ops = (rationalMoveWord 0 7 C).map (AffineFieldProgram.mapOp (Swap.Modular.ratMod (prime^w)))

theorem modular_scatter (w : ℕ) :
    let R := ZMod (prime ^ w)
    let E := Swap.Shear.State (Fin 8) R → ZMod 2
    ∃ (frame : ℕ → FramedCircuit.Frame (ZMod 2) E)
      (word : ℕ × ℕ → List (AffineFieldProgram.Op (Fin 8) R)),
      (∀ p, Geometry.Moves.CheckedPair p → ∀ f : E,
        (fun x => f (AffineFieldProgram.run (word p) x)) = frame p.2 ((frame p.1).symm f)) ∧
      (∀ p, Geometry.Moves.CheckedPair p → Function.Involutive (AffineFieldProgram.run (word p))) ∧
      LocalMoveProfile word ∧ (∀ p ∈ retainedCopyEdges, SelectedCopyWord w (word p)) ∧
      (∀ bank : ℕ → E, Copy.lifecycles.foldl (fun b l => scatterWindow word l b) bank =
        Copy.run frame Copy.lifecycles bank) ∧
      ∀ stored : Fin 661 → E,
        let input := FramedCircuit.encode (fun j => frame (Frames.beforeScatter j)) (Copy.extendStored stored)
        let output := Copy.lifecycles.foldl (fun bank life => scatterWindow word life bank) input
        output 661 = 0 ∧ ∀ i : Fin 661, output i.val = frame (Frames.beforeScatter i.val)
          (FramedCircuit.moduleRun (sectionscatter.map RawGate.toCircuit) (Copy.extendStored stored) i.val) := by
  intro R E
  obtain ⟨raw, copies, _, widths⟩ := modular_move_profile
  let word := fun p => (raw p).map (AffineFieldProgram.mapOp (Swap.Modular.ratMod (prime ^ w)))
  obtain ⟨P, idem, commute, spec, profile⟩ := widths w
  change ∀ p (h : Geometry.Moves.CheckedPair p) s, AffineFieldProgram.run (word p) s =
    exchange (P ⟨p.2,h.2.1⟩) (exchange (P ⟨p.1,h.1⟩) s) at spec
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
  have invol (p : ℕ × ℕ) (h : Geometry.Moves.CheckedPair p) :
      Function.Involutive (AffineFieldProgram.run (word p)) := by
    let i : Fin 636 := ⟨p.1,h.1⟩
    let j : Fin 636 := ⟨p.2,h.2.1⟩
    have swap (s) : exchange (P i) (exchange (P j) s) = exchange (P j) (exchange (P i) s) := by
      rw [M8.Global.exchange_exchange, M8.Global.exchange_exchange, commute i j h, add_comm (P i)]
    intro s
    simp only [spec p h]
    change exchange (P j) (exchange (P i) (exchange (P j) (exchange (P i) s))) = s
    rw [swap, M8.Global.exchange_involutive (idem i), M8.Global.exchange_involutive (idem j)]
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
  have selected (p) (hp : p ∈ retainedCopyEdges) : SelectedCopyWord w (word p) := by
    obtain ⟨C, eq, rev, fwd⟩ := copies p hp
    exact ⟨C,rev,fwd,congrArg _ eq⟩
  refine ⟨frame, word, read, invol, profile, selected, fold _ (fun _ h => h), ?_⟩
  intro stored input output
  dsimp only [output]
  rw [fold _ (fun _ h => h)]
  exact ⟨Copy.temporary_cleared frame stored, Copy.decoded_scatter frame stored⟩

/-- Apply a stream frame separately on each spectator slice of a serialized tape. -/
def tapeFrame {S : Type*} {N W : ℕ} (addr : Fin N ≃ S × Fin W)
    (F : FramedCircuit.Frame (ZMod 2) (S → ZMod 2)) :
    FramedCircuit.Frame (ZMod 2) (Fin N → ZMod 2) where
  toFun f i := F (fun x => f (addr.symm (x,(addr i).2))) (addr i).1
  invFun f i := F.symm (fun x => f (addr.symm (x,(addr i).2))) (addr i).1
  left_inv f := by
    funext i
    simp
  right_inv f := by
    funext i
    simp
  map_add' f g := by
    funext i
    exact congrFun (F.map_add (fun x => f (addr.symm (x,(addr i).2))) (fun x => g (addr.symm (x,(addr i).2)))) _
  map_smul' k f := by
    funext i
    exact congrFun (F.map_smul k (fun x => f (addr.symm (x,(addr i).2)))) _

/-- The temporary's source address on a serialized tape. The same selected
word acts independently on every spectator position and uses seven interchanges
in each scheduled COPY window. -/
theorem copyAddress_word (w : ℕ) :
    let S := Swap.Shear.State (Fin 8) (ZMod (prime^w))
    ∃ (frame : ℕ → FramedCircuit.Frame (ZMod 2) (S → ZMod 2))
      (word : ℕ × ℕ → List (AffineFieldProgram.Op (Fin 8) (ZMod (prime^w)))),
      LocalMoveProfile word ∧ ∀ life ∈ Copy.lifecycles,
        let ops := word (life.sourceFrame,0)
        SelectedCopyWord w ops ∧ AffineFieldProgram.interchanges ops = 7 ∧ Function.Involutive (AffineFieldProgram.run ops) ∧
        ∀ {N W : ℕ} (addr : Fin N ≃ S × Fin W) (data : Fin N → ZMod 2) (i : Fin N),
          data (addr.symm (AffineFieldProgram.run ops (addr i).1,(addr i).2)) =
          tapeFrame addr (frame 0) ((tapeFrame addr (frame life.sourceFrame)).symm data) i := by
  intro S
  obtain ⟨frame,word,read,invol,profile,selected,_,_⟩ := modular_scatter w
  refine ⟨frame,word,profile,?_⟩
  intro life scheduled ops
  have source : life.source ∈ Frames.retained := Copy.source_order ▸ List.mem_map_of_mem scheduled
  have pair : (life.sourceFrame,0) ∈ retainedCopyEdges := by
    apply List.mem_map.mpr
    exact ⟨Frames.beforeScatter life.source,List.mem_map_of_mem source,
      Prod.ext (Copy.wellformed life scheduled).2.2.1 rfl⟩
  have count := List.mem_map_of_mem (f := AffineFieldProgram.interchanges) (List.mem_map_of_mem (f := word) pair)
  rw [profile.copies] at count
  refine ⟨selected _ pair,(List.mem_replicate.mp count).2,invol _ (retainedCopy_checked.1 _ pair),?_⟩
  intro N W addr data i
  have checked := retainedCopy_checked.1 _ pair
  simpa [tapeFrame] using congrFun (read _ checked (fun x => data (addr.symm (x,(addr i).2)))) (addr i).1

end IntegerMultBounds.MathlibTM2.M6
