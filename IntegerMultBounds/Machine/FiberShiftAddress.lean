import IntegerMultBounds.Machine.FiberShiftReuse

/-! Address-level interpretation of the actual repeated-fiber machine. Each
fiber has Q target-address blocks with B payload symbols. One common offset
moves the target coordinate forward modulo Q without changing payload order.
The outer prefix count and suffix width can be arbitrarily large. -/

namespace IntegerMultBounds.Machine.FiberShiftAddress

/-- A flat raw rotation by the exact piece boundary realizes block translation. -/
theorem shift_eq (blocks : List (List (Fin 4))) (Q B a : ℕ)
    (hQ : blocks.length = Q) (hB : BlockRotationData.Uniform B blocks) (ha : a < Q) :
    FiberShift.shift ((Q-a)*B) blocks.flatten = (BlockRotationData.rotate a blocks).flatten := by
  simpa only [FiberShift.shift,hQ,Nat.mod_eq_of_lt ha] using
    (BlockRotationData.rotated_payload_split a B blocks hB).symm

/-- Actual linear-volume execution for an arbitrarily long prefix stream of
Q-by-B fibers. The common offset and canonical binary descriptors are supplied;
no control-dependent descriptor computation is implicit in this theorem. -/
theorem translate_hoare (source dest : ℤ → Fin 4) (p q : ℤ)
    (fibers : List (List (List (Fin 4)))) (Q B a : ℕ)
    (hQ : ∀ f ∈ fibers, f.length = Q)
    (hB : ∀ f ∈ fibers, BlockRotationData.Uniform B f) (ha : a < Q) (hBpos : 1 ≤ B)
    (b c d countBits : List Bool) (hb : Counter.value b = (Q-a)*B)
    (hc : Counter.value c = a*B) (hd : Counter.value d = Q*B)
    (hn : Counter.value countBits = fibers.length)
    (cb : GrowingCounterData.Canonical b) (cc : GrowingCounterData.Canonical c)
    (cd : GrowingCounterData.Canonical d) (cn : GrowingCounterData.Canonical countBits) :
    HoareTime FiberShiftReuse.program
      (fun v => v = CountedLoopReuse.bank
        (CountedRotate.bank (putWord source p (fibers.map List.flatten).flatten) dest b c d p q)
        CountedCopyReuse.empty (CountedCopyReuse.binary countBits) 1 1)
      (fun v => v = CountedLoopReuse.bank
        (CountedRotate.bank (putWord source p (fibers.map List.flatten).flatten)
          (putWord dest q (fibers.map (fun f => (BlockRotationData.rotate a f).flatten)).flatten)
          b c d (p+((fibers.length*(Q*B) : ℕ) : ℤ)) (q+((fibers.length*(Q*B) : ℕ) : ℤ)))
        CountedCopyReuse.empty (CountedCopyReuse.binary countBits) 1 1)
      (182*(fibers.map List.flatten).flatten.length+23) := by
  have hu : BlockRotationData.Uniform (Q*B) (fibers.map List.flatten) := by
    intro xs hx
    obtain ⟨f,hf,rfl⟩ := List.mem_map.mp hx
    rw [BlockRotationData.uniform_volume B f (hB f hf),hQ f hf]
  have hsum : (Q-a)*B+a*B = Q*B := by rw [← Nat.add_mul,Nat.sub_add_cancel ha.le]
  have hmap : (fibers.map List.flatten).map (FiberShift.shift ((Q-a)*B)) =
      fibers.map (fun f => (BlockRotationData.rotate a f).flatten) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro f hf
    exact shift_eq f Q B a (hQ f hf) (hB f hf) ha
  have hh := FiberShiftReuse.shift_hoare_linear source dest p q (fibers.map List.flatten)
    ((Q-a)*B) (Q*B) hu (by omega) (by nlinarith) b c d countBits hb
    (by omega) hd (by simpa using hn) cb cc cd cn
  simpa only [hmap,List.length_map] using hh

end IntegerMultBounds.Machine.FiberShiftAddress
