import IntegerMultBounds.Machine.PackedOffsetStream
import IntegerMultBounds.Compact.PowerTwoDigits

/-! The packed-offset stream builder applied directly to a raw n*w-bit word.
The emitted canonical integers are exactly its radix-2^w digits, in order. -/
namespace IntegerMultBounds.Machine.PackedOffsetStreamRaw
open Compact.PowerTwo

def blocks (V : List Bool) (w : ℕ) : ℕ → List (List Bool)
  | 0 => []
  | n+1 => V.take w :: blocks (V.drop w) w n

@[simp] theorem blocks_length (V : List Bool) (w n : ℕ) : (blocks V w n).length = n := by
  induction n generalizing V with
  | zero => rfl
  | succ n ih => simp [blocks,ih]

theorem blocks_uniform (V : List Bool) (w n : ℕ) (hV : V.length = n*w) :
    BlockRotationData.Uniform w (blocks V w n) := by
  induction n generalizing V with
  | zero => simp [blocks,BlockRotationData.Uniform]
  | succ n ih =>
    have hw : w ≤ V.length := by rw [hV]; nlinarith
    have hd : (V.drop w).length = n*w := by simp only [List.length_drop]; rw [hV,Nat.succ_mul]; omega
    intro xs hx
    rcases List.mem_cons.mp hx with rfl | hx
    · simp [List.length_take,Nat.min_eq_left hw]
    · exact ih (V.drop w) hd xs hx

theorem blocks_flatten (V : List Bool) (w n : ℕ) (hV : V.length = n*w) : (blocks V w n).flatten = V := by
  induction n generalizing V with
  | zero =>
    have he : V = [] := List.eq_nil_of_length_eq_zero (by omega)
    simp [blocks,he]
  | succ n ih =>
    have hd : (V.drop w).length = n*w := by simp only [List.length_drop]; rw [hV,Nat.succ_mul]; omega
    simp only [blocks,List.flatten_cons,ih (V.drop w) hd,List.take_append_drop]

theorem blocks_values (V : List Bool) (w n : ℕ) (hV : V.length = n*w) :
    (blocks V w n).map (fun xs => (Counter.value xs : ℤ)) = blockValues V w n := by
  induction n generalizing V with
  | zero => simp [blocks,blockValues]
  | succ n ih =>
    have hw : w ≤ V.length := by rw [hV]; nlinarith
    have hd : (V.drop w).length = n*w := by simp only [List.length_drop]; rw [hV,Nat.succ_mul]; omega
    rw [blockValues_succ V w n hw]
    simp only [blocks,List.map_cons,ih (V.drop w) hd]

noncomputable def words (V : List Bool) (w n : ℕ) := PackedOffsetStream.words (blocks V w n)
noncomputable def output (V : List Bool) (w n : ℕ) := PackedOffsetStream.output (blocks V w n)

theorem words_length (V : List Bool) (w n : ℕ) : (words V w n).length = n := by
  simp [words,PackedOffsetStream.words]

theorem words_canonical (V : List Bool) (w n : ℕ) :
    ∀ xs ∈ words V w n, GrowingCounterData.Canonical xs := PackedOffsetStream.words_canonical _

/-- The synthesized physical controls are precisely the packed input's digit
values. This includes width zero, where every control is canonical zero. -/
theorem words_values (V : List Bool) (w n : ℕ) (hV : V.length = n*w) :
    (words V w n).map (fun xs => (Counter.value xs : ℤ)) =
      Compact.Radix.digits ((2 : ℤ)^w) n (Counter.value V) := by
  have hh := congrArg (List.map (fun x : ℕ => (x : ℤ))) (PackedOffsetStream.words_values (blocks V w n))
  simp only [List.map_map,Function.comp_def] at hh
  exact hh.trans ((blocks_values V w n hV).trans (digits_blocks V w n hV).symm)

theorem words_bounded (V : List Bool) (w n : ℕ) (hV : V.length = n*w) :
    ∀ xs ∈ words V w n, Counter.value xs < 2^w := by
  intro xs hx
  obtain ⟨ys,hy,rfl⟩ := List.mem_map.mp hx
  rw [(PackedOffsetStreamBlock.canonical_facts ys).2.1]
  have hh := Counter.value_lt ys
  rw [blocks_uniform V w n hV ys hy] at hh
  exact hh

theorem output_length (V : List Bool) (w n : ℕ) (hV : V.length = n*w) :
    (output V w n).length ≤ n*(w+1) := by
  simpa only [blocks_length,output] using PackedOffsetStream.output_length (blocks V w n) w (blocks_uniform V w n hV)

/-- A fixed 51-state program reads the original width/count descriptors and
raw packed word. Source and descriptors survive, all private tapes return
blank, and the output stream contains the canonical radix digits. -/
theorem runs (V : List Bool) (w n : ℕ) (hV : V.length = n*w)
    (f g : ℤ → Fin 4) (p q : ℤ) (bs ns : List Bool)
    (hb : Counter.value bs = w) (hn : Counter.value ns = n)
    (cb : GrowingCounterData.Canonical bs) (cn : GrowingCounterData.Canonical ns) :
    HoareTime PackedOffsetStream.program
      (fun v => v = PackedOffsetStream.input (putWord f p (V.map bitSymbol)) g p q bs ns)
      (fun v => v = PackedOffsetStream.input (putWord f p (V.map bitSymbol)) (putWord g q (output V w n))
        (p+((n*w : ℕ) : ℤ)) (q+(output V w n).length) bs ns)
      (66*(n*(w+1))+28) := by
  have hh := PackedOffsetStream.runs (blocks V w n) w (blocks_uniform V w n hV)
    f g p q bs ns hb (by simpa using hn) cb cn
  simpa only [blocks_flatten V w n hV,blocks_length,output] using hh

end IntegerMultBounds.Machine.PackedOffsetStreamRaw
