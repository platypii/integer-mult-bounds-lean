import IntegerMultBounds.Machine.Partition
import IntegerMultBounds.Machine.RadixSort

/-! The concrete partition's two output words represent the stable list pass.
This connects the interfaces without assuming that concatenation or selection
of subsequent key bits is free on tapes. -/

namespace IntegerMultBounds.Machine.Partition

theorem encode_append (xs ys : List Record) :
    encode (xs ++ ys) = encode xs ++ encode ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [encode, ih, List.append_assoc]

theorem buckets_eq_pass (xs : List Record) :
    bucket false xs ++ bucket true xs = encode (RadixSort.pass Record.key xs) := by
  simp only [RadixSort.pass, encode_append, bucket]
  congr 1 <;> congr 1 <;> apply List.filter_congr <;> intro x _ <;> cases x.key <;> rfl

/-- The two words produced by the actual tape execution concatenate to the
stable pass, and their combined length is exactly its actual runtime. -/
theorem stream_stable_pass (xs : List Record) :
    ∃ low high : List (Fin 4),
      low ++ high = encode (RadixSort.pass Record.key xs) ∧
      low.length + high.length = (encode xs).length ∧
      run program (encode xs).length
        (cfg false (wordTape (encode xs)) (fun _ => blank) (fun _ => blank) 0 0 0 0) =
        some (cfg false (wordTape (encode xs)) (wordTape low) (wordTape high)
          (encode xs).length low.length high.length 0) ∧
      step program (cfg false (wordTape (encode xs)) (wordTape low) (wordTape high)
          (encode xs).length low.length high.length 0) = none := by
  exact ⟨bucket false xs, bucket true xs, buckets_eq_pass xs, bucket_lengths xs,
    stream_blank xs⟩

end IntegerMultBounds.Machine.Partition
