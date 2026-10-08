import IntegerMultBounds.Machine.TranslationPreparedExecution
import IntegerMultBounds.Machine.TranslationDescriptorsReuse

/-! Reusable single-fiber translation. Each invocation synthesizes its physical
split lengths, runs the actual rotation, and erases every derived descriptor.
The recurring complete bank retains only canonical Q/a/B and empty workspaces. -/

namespace IntegerMultBounds.Machine.TranslationExecutionReuse

open CountedCopyReuse (binary)

/-- Exact recurring layout: no prepared derived numeric data is required. -/
def bank (source dest : ℤ → Fin 4) (p q : ℤ) (bs qs as : List Bool) : Tapes 12 0 :=
  TranslationPreparedExecution.bank (fun _ => []) bs qs as (fun _ => blank) 0 source dest p q

def input (source dest : ℤ → Fin 4) (p q : ℤ) (blocks : List (List (Fin 4)))
    (bs qs as : List Bool) : Tapes 12 0 := bank (putWord source p blocks.flatten) dest p q bs qs as

def output (Q a B : ℕ) (source dest : ℤ → Fin 4) (p q : ℤ) (blocks : List (List (Fin 4)))
    (bs qs as : List Bool) : Tapes 12 0 :=
  bank (putWord source p blocks.flatten) (putWord dest q (BlockRotationData.rotate a blocks).flatten)
    (p+Q*B) (q+Q*B) bs qs as

/-- Clean only metadata; payload and both advanced heads are complete frames. -/
def cleanupProgram : Program 12 19 0 := extend TranslationDescriptorsReuse.cleanupProgram 2

theorem cleanup_hoare (Q a B : ℕ) (ha : a ≤ Q) (hB : 0 < B) (source dest : ℤ → Fin 4)
    (p q : ℤ) (blocks : List (List (Fin 4))) (bs qs as : List Bool)
    (hq : Counter.value qs = Q) (ha' : Counter.value as = a)
    (cq : GrowingCounterData.Canonical qs) (ca : GrowingCounterData.Canonical as) :
    HoareTime cleanupProgram
      (fun v => v = TranslationPreparedExecution.output Q a B source dest p q blocks bs qs as)
      (fun v => v = output Q a B source dest p q blocks bs qs as)
      (8*(Q*B)+30) := by
  have h := (TranslationDescriptorsReuse.cleanup_hoare_linear Q a B ha hB bs qs as hq ha' cq ca).extend
    (TranslationPreparedExecution.payload (putWord source p blocks.flatten)
      (putWord dest q (BlockRotationData.rotate a blocks).flatten) (p+Q*B) (q+Q*B))
  apply h.consequence _ _ le_rfl
  · intro v hv; exact ⟨_,rfl,hv⟩
  · rintro v ⟨w,rfl,hv⟩; exact hv

/-- Marked-workspace synthesis, rotation, then complete metadata cleanup. -/
def program : Program 12 217 0 :=
  seq (seq (extend TranslationDescriptorsReuse.program 2) TranslationPreparedExecution.rotateProgram) cleanupProgram

/-- Every complete call restores the exact recurring metadata state. The
source tape is unchanged and both payload heads advance the whole fiber. -/
theorem translate_hoare (Q a B : ℕ) (ha : a ≤ Q) (hB : 0 < B)
    (source dest : ℤ → Fin 4) (p q : ℤ) (blocks : List (List (Fin 4)))
    (hlen : blocks.length = Q) (hwidth : BlockRotationData.Uniform B blocks) (bs qs as : List Bool)
    (hb : Counter.value bs = B) (hq : Counter.value qs = Q) (ha' : Counter.value as = a)
    (cb : GrowingCounterData.Canonical bs) (cq : GrowingCounterData.Canonical qs)
    (ca : GrowingCounterData.Canonical as) :
    HoareTime program
      (fun v => v = input source dest p q blocks bs qs as)
      (fun v => v = output Q a B source dest p q blocks bs qs as)
      (207*(Q*B)+241) := by
  have hs := (TranslationDescriptorsReuse.descriptors_hoare Q a B ha hB bs qs as hb hq ha' cb cq ca).extend
    (TranslationPreparedExecution.payload (putWord source p blocks.flatten) dest p q)
  have hs' : HoareTime (extend TranslationDescriptorsReuse.program 2)
      (fun v => v = input source dest p q blocks bs qs as)
      (fun v => v = TranslationPreparedExecution.bank (TranslationDescriptors.descriptors Q a B) bs qs as
        (binary (BinarySubReuse.difference qs as)) 1 (putWord source p blocks.flatten) dest p q)
      (163*(Q*B)+90) := by
    apply hs.consequence _ _ le_rfl
    · intro v hv; exact ⟨_,rfl,hv⟩
    · rintro v ⟨w,rfl,hv⟩; exact hv
  have hr := TranslationPreparedExecution.rotate_hoare Q a B ha bs qs as source dest p q blocks hlen hwidth
  have hc := cleanup_hoare Q a B ha hB source dest p q blocks bs qs as hq ha' cq ca
  have h := (hs'.seq hr).seq hc
  exact h.consequence (fun _ hv => hv) (fun _ hv => hv) (by omega)

/-- First invocation can start with every writable metadata tape fully blank. -/
def initialProgram : Program 12 219 0 := seq TranslationPreparedExecution.program cleanupProgram

theorem initial_translate_hoare (Q a B : ℕ) (ha : a ≤ Q) (hB : 0 < B)
    (source dest : ℤ → Fin 4) (p q : ℤ) (blocks : List (List (Fin 4)))
    (hlen : blocks.length = Q) (hwidth : BlockRotationData.Uniform B blocks) (bs qs as : List Bool)
    (hb : Counter.value bs = B) (hq : Counter.value qs = Q) (ha' : Counter.value as = a)
    (cb : GrowingCounterData.Canonical bs) (cq : GrowingCounterData.Canonical qs)
    (ca : GrowingCounterData.Canonical as) :
    HoareTime initialProgram
      (fun v => v = TranslationPreparedExecution.input source dest p q blocks bs qs as)
      (fun v => v = output Q a B source dest p q blocks bs qs as)
      (207*(Q*B)+243) := by
  have h := (TranslationPreparedExecution.translate_hoare Q a B ha hB source dest p q blocks hlen hwidth
    bs qs as hb hq ha' cb cq ca).seq (cleanup_hoare Q a B ha hB source dest p q blocks bs qs as hq ha' cq ca)
  exact h.consequence (fun _ hv => hv) (fun _ hv => hv) (by omega)

/-- The literal destination is independent of the restored numeric workspaces. -/
theorem output_tape (Q a B : ℕ) (source dest : ℤ → Fin 4) (p q : ℤ) (blocks : List (List (Fin 4)))
    (bs qs as : List Bool) :
    (output Q a B source dest p q blocks bs qs as).tape 11 =
      putWord dest q (BlockRotationData.rotate a blocks).flatten := rfl

/-- Complete metadata equality makes subsequent calls with a newly supplied
canonical offset descriptor possible without a derived-descriptor oracle. -/
theorem output_metadata (Q a B : ℕ) (source dest : ℤ → Fin 4) (p q : ℤ) (blocks : List (List (Fin 4)))
    (bs qs as : List Bool) :
    Placement.active (Equiv.refl (Fin (10+2))) (output Q a B source dest p q blocks bs qs as) =
      TranslationDescriptors.bank (fun _ => []) bs qs as (fun _ => blank) 0 := by
  unfold Placement.active output bank TranslationPreparedExecution.bank
  congr 1 <;> funext i <;> simp [Tapes.append] <;> rfl

end IntegerMultBounds.Machine.TranslationExecutionReuse
