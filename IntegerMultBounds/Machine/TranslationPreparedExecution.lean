import IntegerMultBounds.Machine.TranslationDescriptors
import IntegerMultBounds.Machine.CountedRotateAdvance

/-! Fully prepared literal cyclic translation of a uniform block fiber. Only
canonical Q, a and B descriptors are supplied. Subtraction, length products,
work markers, all payload movement and head restoration are actual programs;
the derived descriptor metadata is retained explicitly in the final bank. -/

namespace IntegerMultBounds.Machine.TranslationPreparedExecution

open CountedCopyReuse (empty binary)

/-- Source and destination follow the ten physical descriptor-synthesis tapes. -/
def payload (source dest : ℤ → Fin 4) (p q : ℤ) : Tapes 2 0 :=
  ⟨![p,q],![source,dest]⟩

def bank (ds : Fin 3 → List Bool) (bs qs as : List Bool) (diff : ℤ → Fin 4) (r : ℤ)
    (source dest : ℤ → Fin 4) (p q : ℤ) : Tapes 12 0 :=
  (TranslationDescriptors.bank ds bs qs as diff r).append (payload source dest p q)

/-- The rotation shares the synthesized lengths and the already-clean B clock. -/
def rotationPlacement : Fin (6+6) ≃ Fin 12 where
  toFun := ![10,11,4,1,2,3,0,5,6,7,8,9]
  invFun := ![6,3,4,5,2,7,8,9,10,11,0,1]
  left_inv := by intro i; fin_cases i <;> decide
  right_inv := by intro i; fin_cases i <;> decide

private theorem active_bank (ds : Fin 3 → List Bool) (bs qs as : List Bool) (diff : ℤ → Fin 4) (r : ℤ)
    (source dest : ℤ → Fin 4) (p q : ℤ) :
    Placement.active rotationPlacement (bank ds bs qs as diff r source dest p q) =
      CountedRotate.bank source dest (ds 0) (ds 1) (ds 2) p q := by
  unfold Placement.active
  congr 1 <;> funext i <;> fin_cases i <;> rfl

private theorem extra_bank (ds : Fin 3 → List Bool) (bs qs as : List Bool) (diff : ℤ → Fin 4) (r : ℤ)
    (source dest source' dest' : ℤ → Fin 4) (p q p' q' : ℤ) :
    Placement.extra rotationPlacement (bank ds bs qs as diff r source dest p q) =
      Placement.extra rotationPlacement (bank ds bs qs as diff r source' dest' p' q') := by
  unfold Placement.extra
  congr 1 <;> funext i <;> fin_cases i <;> rfl

private theorem replace_bank (ds : Fin 3 → List Bool) (bs qs as : List Bool) (diff : ℤ → Fin 4) (r : ℤ)
    (source dest source' dest' : ℤ → Fin 4) (p q p' q' : ℤ) :
    Placement.replace rotationPlacement (bank ds bs qs as diff r source dest p q)
      (CountedRotate.bank source' dest' (ds 0) (ds 1) (ds 2) p' q') =
      bank ds bs qs as diff r source' dest' p' q' := by
  rw [Placement.replace,extra_bank ds bs qs as diff r source dest source' dest' p q p' q',← active_bank]
  exact Placement.view _ _

/-- Both endpoint cases a=0 and a=Q are literal identity rotations. -/
theorem rotate_split {α : Type*} (a Q : ℕ) (blocks : List (List α))
    (hlen : blocks.length = Q) (ha : a ≤ Q) :
    BlockRotationData.rotate a blocks = blocks.drop (Q-a) ++ blocks.take (Q-a) := by
  by_cases hlt : a < Q
  · simpa only [hlen] using BlockRotationData.split_at a blocks (by omega)
  · have he : a = Q := by omega
    subst a
    simp [BlockRotationData.rotate,← hlen]

private theorem split_lengths (a Q B : ℕ) (blocks : List (List (Fin 4)))
    (hlen : blocks.length = Q) (ha : a ≤ Q) (hwidth : BlockRotationData.Uniform B blocks) :
    (blocks.take (Q-a)).flatten.length = (Q-a)*B ∧
    (blocks.drop (Q-a)).flatten.length = a*B := by
  constructor
  · rw [BlockRotationData.uniform_volume B _ (fun b hb => hwidth b (List.mem_of_mem_take hb)),List.length_take,hlen]
    rw [Nat.min_eq_left (Nat.sub_le Q a)]
  · rw [BlockRotationData.uniform_volume B _ (fun b hb => hwidth b (List.mem_of_mem_drop hb)),List.length_drop,hlen]
    congr 1
    omega

def rotateProgram : Program 12 80 0 := Placement.placed CountedRotateAdvance.program rotationPlacement

/-- Rotation consumes exactly the three generated lengths and preserves every
metadata tape; both payload heads finish after the complete input fiber. -/
theorem rotate_hoare (Q a B : ℕ) (ha : a ≤ Q) (bs qs as : List Bool)
    (source dest : ℤ → Fin 4) (p q : ℤ) (blocks : List (List (Fin 4)))
    (hlen : blocks.length = Q) (hwidth : BlockRotationData.Uniform B blocks) :
    HoareTime rotateProgram
      (fun v => v = bank (TranslationDescriptors.descriptors Q a B) bs qs as
        (binary (BinarySubReuse.difference qs as)) 1 (putWord source p blocks.flatten) dest p q)
      (fun v => v = bank (TranslationDescriptors.descriptors Q a B) bs qs as
        (binary (BinarySubReuse.difference qs as)) 1 (putWord source p blocks.flatten)
        (putWord dest q (BlockRotationData.rotate a blocks).flatten) (p+Q*B) (q+Q*B))
      (36*(Q*B)+119) := by
  let ds := TranslationDescriptors.descriptors Q a B
  let xs := (blocks.take (Q-a)).flatten
  let ys := (blocks.drop (Q-a)).flatten
  obtain ⟨hx,hy⟩ := split_lengths a Q B blocks hlen ha hwidth
  have hsum : xs.length+ys.length = Q*B := by
    dsimp only [xs,ys]
    rw [hx,hy,← Nat.add_mul,Nat.sub_add_cancel ha]
  have hjoin : xs++ys = blocks.flatten := by
    dsimp [xs,ys]
    rw [← List.flatten_append,List.take_append_drop]
  have hrot : ys++xs = (BlockRotationData.rotate a blocks).flatten := by
    rw [rotate_split a Q blocks hlen ha,List.flatten_append]
  obtain ⟨h₀,h₁,h₂⟩ := TranslationDescriptors.descriptor_values Q a B
  have h := CountedRotateAdvance.rotate_hoare source dest p q xs ys (ds 0) (ds 1) (ds 2)
    (h₀.trans hx.symm) (h₁.trans hy.symm) (h₂.trans hsum.symm)
  rw [hjoin,hrot,hsum] at h
  have hh := Placement.hoare_at h rotationPlacement
    (bank ds bs qs as (binary (BinarySubReuse.difference qs as)) 1 (putWord source p blocks.flatten) dest p q)
    (active_bank _ _ _ _ _ _ _ _ _ _)
  apply hh.consequence (fun _ hv => hv) _ _
  · rintro v ⟨w,rfl,rfl⟩
    simpa only [Nat.cast_mul] using replace_bank ds bs qs as (binary (BinarySubReuse.difference qs as)) 1
      (putWord source p blocks.flatten) dest (putWord source p blocks.flatten)
      (putWord dest q (BlockRotationData.rotate a blocks).flatten) p q (p+(Q*B : ℕ)) (q+(Q*B : ℕ))
  · have hw (j : Fin 3) : (ds j).length ≤ Counter.value (ds j)+1 := by
      have hc := GrowingCounterData.canonical_width (ds j) (TranslationDescriptors.descriptors_canonical Q a B j)
      have hl := Nat.log2_le_self (Counter.value (ds j))
      omega
    have w₀ := hw 0
    have w₁ := hw 1
    have w₂ := hw 2
    rw [h₀] at w₀
    rw [h₁] at w₁
    rw [h₂] at w₂
    have hsplit : (Q-a)*B+a*B = Q*B := by rw [← Nat.add_mul,Nat.sub_add_cancel ha]
    omega

/-- Initially only canonical numeric inputs and source payload are prepared. -/
def input (source dest : ℤ → Fin 4) (p q : ℤ) (blocks : List (List (Fin 4)))
    (bs qs as : List Bool) : Tapes 12 0 :=
  (TranslationDescriptors.initial bs qs as).append (payload (putWord source p blocks.flatten) dest p q)

/-- Final metadata includes all immutable inputs, three synthesized canonical
lengths and Q-a; the two mutable clocks are clean and all descriptor heads one. -/
def output (Q a B : ℕ) (source dest : ℤ → Fin 4) (p q : ℤ) (blocks : List (List (Fin 4)))
    (bs qs as : List Bool) : Tapes 12 0 :=
  bank (TranslationDescriptors.descriptors Q a B) bs qs as (binary (BinarySubReuse.difference qs as)) 1
    (putWord source p blocks.flatten) (putWord dest q (BlockRotationData.rotate a blocks).flatten)
    (p+Q*B) (q+Q*B)

/-- Fixed 200-state program, independent of every input dimension and offset. -/
def program : Program 12 200 0 := seq (extend TranslationDescriptors.program 2) rotateProgram

/-- Complete physical translation including synthesis and all head movement.
The old block at y occurs at y+a modulo Q in the emitted fiber. -/
theorem translate_hoare (Q a B : ℕ) (ha : a ≤ Q) (hB : 0 < B)
    (source dest : ℤ → Fin 4) (p q : ℤ) (blocks : List (List (Fin 4)))
    (hlen : blocks.length = Q) (hwidth : BlockRotationData.Uniform B blocks) (bs qs as : List Bool)
    (hb : Counter.value bs = B) (hq : Counter.value qs = Q) (ha' : Counter.value as = a)
    (cb : GrowingCounterData.Canonical bs) (cq : GrowingCounterData.Canonical qs)
    (ca : GrowingCounterData.Canonical as) :
    HoareTime program
      (fun v => v = input source dest p q blocks bs qs as)
      (fun v => v = output Q a B source dest p q blocks bs qs as)
      (199*(Q*B)+212) := by
  have hs := (TranslationDescriptors.descriptors_hoare Q a B ha hB bs qs as hb hq ha' cb cq ca).extend
    (payload (putWord source p blocks.flatten) dest p q)
  have hs' : HoareTime (extend TranslationDescriptors.program 2)
      (fun v => v = input source dest p q blocks bs qs as)
      (fun v => v = bank (TranslationDescriptors.descriptors Q a B) bs qs as
        (binary (BinarySubReuse.difference qs as)) 1 (putWord source p blocks.flatten) dest p q)
      (163*(Q*B)+92) := by
    apply hs.consequence _ _ le_rfl
    · intro v hv; exact ⟨_,rfl,hv⟩
    · rintro v ⟨w,rfl,hv⟩; exact hv
  have h := hs'.seq (rotate_hoare Q a B ha bs qs as source dest p q blocks hlen hwidth)
  exact h.consequence (fun _ hv => hv) (fun _ hv => hv) (by omega)

theorem output_tape (Q a B : ℕ) (source dest : ℤ → Fin 4) (p q : ℤ) (blocks : List (List (Fin 4)))
    (bs qs as : List Bool) :
    (output Q a B source dest p q blocks bs qs as).tape 11 =
      putWord dest q (BlockRotationData.rotate a blocks).flatten := rfl

/-- Pure forward-index statement for the exact block list emitted by the machine. -/
theorem block_destination (a Q : ℕ) (blocks : List (List (Fin 4))) (hlen : blocks.length = Q)
    (y : ℕ) (hy : y < Q) :
    (BlockRotationData.rotate a blocks)[(y+a)%Q]'(by
      rw [BlockRotationData.rotate_length,hlen]
      exact Nat.mod_lt _ (by omega)) = blocks[y]'(by omega) := by
  simpa only [hlen] using BlockRotationData.block_destination a blocks y (by omega)

end IntegerMultBounds.Machine.TranslationPreparedExecution
