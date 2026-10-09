import IntegerMultBounds.Machine.PackedOffsetPayloadPlaced

/-! A direct controlled rotation of an active target field. Target width is
unrestricted by the compact reservation capacity: only rotations use it, and
the complete physical runtime is linear in the original containing volume.
The offset table is an explicit physical stage input, not a semantic oracle. -/
namespace IntegerMultBounds.Machine.ActiveTargetRotation
noncomputable section
open SharedPlacementAlphabet (setTape)
variable {t a : ℕ}

def word {m : ℕ} (x : Fin m → Bool) : ℤ → Fin (a+4) :=
  putWord (fun _ => blank) 0 (List.ofFn (fun i => bitSymbol (x i)))
def offsets (V : List Bool) : ℤ → Fin (a+4) :=
  putWord (fun _ => blank) 0 (V.map bitSymbol)
def result (caller : Tapes t a) (focus : Fin 5 → Fin t) (V : List Bool) (w P B : ℕ)
    (x : Fin (P*(2^w*B)) → Bool) :=
  setTape caller (focus 0) (word (PackedOffsetPayloadArray.array V w P B x)) 0
def constant := FixedBasePowerDescriptor.constant 2+760

theorem cost_bound (w P B : ℕ) (hP : 0<P) (hB : 0<B) :
    (FixedBasePowerDescriptor.constant 2+8)*2^w+600*(P*(2^w*B))+152≤
      constant*(P*(2^w*B)) := by
  have h := PackedOffsetPayloadPlaced.cost_nonempty w P B hP hB
  have hV : 0<P*(2^w*B) := by positivity
  unfold constant
  nlinarith

/-- Original P/B/width words and arbitrary caller tapes are retained. The
target is rotated in its current serialized position; no target swap occurs. -/
theorem runs (caller : Tapes t a) (focus : Fin 5 → Fin t) (hf : Function.Injective focus)
    (V : List Bool) (w P B : ℕ) (hV : V.length=P*w) (hP : 0<P) (hB : 0<B)
    (bs ps ws : List Bool) (hb : Counter.value bs=B) (hp : Counter.value ps=P)
    (hw : Counter.value ws=w) (cb : GrowingCounterData.Canonical bs)
    (cp : GrowingCounterData.Canonical ps) (cw : GrowingCounterData.Canonical ws)
    (x : Fin (P*(2^w*B)) → Bool)
    (ht : ∀ i,caller.tape (focus i)=PackedOffsetPayloadPlaced.tapes (word x) (offsets V) bs ps ws i)
    (hh : ∀ i,caller.head (focus i)=PackedOffsetPayloadPlaced.heads 0 0 i) :
    HoareTime (PackedOffsetPayloadPlaced.program a focus hf)
      (fun v => v=PackedOffsetPayloadPlaced.input caller)
      (fun v => v=PackedOffsetPayloadPlaced.input (result caller focus V w P B x))
      (constant*(P*(2^w*B))) := by
  have hr := PackedOffsetPayloadPlaced.runs caller focus hf V w P B hV hB
    (fun _ => blank) (fun _ => blank) 0 0 rfl rfl bs ps ws hb hp hw cb cp cw x ht hh
  exact hr.consequence (fun _ h => h) (fun _ h => h) (cost_bound w P B hP hB)

/-- Full forward destination semantics include arbitrary prefix and suffix
coordinates, even on overflowing addresses. -/
theorem entry (V : List Bool) (w P B : ℕ) (hV : V.length=P*w)
    (x : Fin (P*(2^w*B)) → Bool) (p : Fin P) (v : Fin (2^w)) (s : Fin B) :
    PackedOffsetPayloadArray.array V w P B x
      (FiberLayoutData.index p
        ⟨(v.val+PackedOffsetPayloadValue.offset V w p.val)%2^w,Nat.mod_lt _ (by positivity)⟩ s)=
      x (FiberLayoutData.index p v s) :=
  PackedOffsetPayloadArray.array_entry V w P B hV x p v s

end
end IntegerMultBounds.Machine.ActiveTargetRotation
