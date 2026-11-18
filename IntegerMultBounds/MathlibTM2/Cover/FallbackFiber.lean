module

public import IntegerMultBounds.Machine.TranslationExecutionReuse
import IntegerMultBounds.Machine.BinaryDivide

/-! Physical destination of each symbol in one fiber of a modular row addition. -/
public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine TranslationExecutionReuse

/-- With the canonical offset descriptor in place, the reusable translation machine
moves block `y` to `(y+c*x)%M` and preserves its internal symbol order. -/
theorem fiber_hoare (M B c x : ℕ) (hM : 0 < M) (hB : 0 < B)
    (source dest : ℤ → Fin 4) (p q : ℤ) (blocks : List (List (Fin 4)))
    (hlen : blocks.length = M) (hwidth : BlockRotationData.Uniform B blocks)
    (bs ms offset : List Bool) (hb : Counter.value bs = B) (hm : Counter.value ms = M)
    (hv : Counter.value offset = c*x % M) (cb : GrowingCounterData.Canonical bs)
    (cm : GrowingCounterData.Canonical ms) (co : GrowingCounterData.Canonical offset) :
    HoareTime program (fun v => v = input source dest p q blocks bs ms offset)
      (fun v => v = output M (c*x % M) B source dest p q blocks bs ms offset ∧
        ∀ (y : Fin M) (j : Fin B), v.tape 11 (q + (((y.val+c*x)%M)*B+j.val : ℕ)) =
          (blocks[y.val]'(hlen ▸ y.isLt))[j.val]'(by rw [hwidth _ (List.getElem_mem _)]; exact j.isLt))
      (207*(M*B)+241) := by
  apply (translate_hoare M _ B (Nat.mod_lt _ hM).le hB source dest p q blocks hlen hwidth
    bs ms offset hb hm hv cb cm co).consequence (fun _ h => h) _ le_rfl
  rintro _ rfl
  refine ⟨rfl, fun y j => ?_⟩
  have he := BlockRotationData.payload_destination_entry (c*x % M) B blocks hwidth
    y.val j.val (hlen ▸ y.isLt) j.isLt
  simp only [hlen, Nat.add_mod_mod] at he
  obtain ⟨hk, heq⟩ := List.getElem?_eq_some_iff.mp he
  rw [output_tape, BinaryDivide.putWord_getElem _ _ _ _ hk, heq]

end IntegerMultBounds.MathlibTM2.Cover.Fallback
