import IntegerMultBounds.Machine.CountedGuardConstantsPlacement

/-! Physically produce all three certified padded guard constants from sole
original canonical q/b headers. Every runtime fill, descriptor subtraction,
overwrite, replay, rewind and private-workspace erasure is included. -/
namespace IntegerMultBounds.Machine.CountedGuardConstants
noncomputable section
variable {a : ℕ}
open SharedPlacementAlphabet
open CountedGuardGadgetRecord (word)
open CountedGuardConstantsPlacement
open CountedGuardConstantsData

def input := CountedGuardConstantsPlacement.input (a := a)
def output (q b : ℕ) (qs bs : List Bool) : Tapes 8 a :=
  setTape (bank qs bs (RecursiveChildQuotientsConstant.bits (q-1))
    (word (c1 q b)) (word (c2 q b)) (word (c3 b)) 0 0 0) 5 (fun _ => blank) 0

def program := seq (seq (seq (seq (seq (seq (seq (seq (seq (seq (seq
  (setup (a := a)) (fill1 false)) rewind1) (edit1 true)) (fill2 true)) rewind2)
  (edit2 false)) (fill3 true)) rewind3) write3) left3) cleanup

theorem replicate_word (n : ℕ) (x : Bool) :
    putWord (fun _ => (blank : Fin (a+4))) 0 (List.replicate n (bitSymbol x))=word (List.replicate n x) := by
  simp only [word,List.map_replicate]

/-- Fixed eight tapes, sole q/b inputs, exact padded constants at head zero,
and all private controls blank at head zero. The runtime is linear in the
produced constant widths; no power-sized header is constructed. -/
theorem runs (q b : ℕ) (qs bs : List Bool) (hq : Counter.value qs=q)
    (cq : GrowingCounterData.Canonical qs) (hvb : Counter.value bs=b)
    (cb : GrowingCounterData.Canonical bs) (hb : 1 ≤ b) (hbq : b+3 ≤ q) :
    HoareTime (program (a := a)) (fun v => v=input qs bs) (fun v => v=output q b qs bs) (40*q+80*b+300) := by
  let ds := RecursiveChildQuotientsConstant.bits (q-1)
  let Z := fun _ : ℤ => (blank : Fin (a+4))
  let R0 := word (a := a) (List.replicate (q-1) false)
  let R1 := word (a := a) (List.replicate (q-1) true)
  let RB := word (a := a) (List.replicate b true)
  let C1 := word (a := a) (c1 q b)
  let C2 := word (a := a) (c2 q b)
  let C3 := word (a := a) (c3 b)
  have hd : Counter.value ds=q-1 := RecursiveChildQuotientsConstant.bits_value _
  have h1 := setsUp (a := a) qs bs q hq cq (by omega)
  have h2 := fills1 (a := a) false qs bs ds Z Z Z 0 0 0 (q-1) hd
  simp only [zero_add] at h2
  rw [replicate_word] at h2
  have h3 := rewinds1 (a := a) qs bs ds Z Z Z 0 0 0 (List.replicate (q-1) false)
  simp only [List.length_replicate] at h3
  have h4 := edits1 (a := a) true qs bs ds R0 Z Z 0 0 0 b hvb
  dsimp only [R0] at h4
  rw [overwrite_replicate q b hbq false true] at h4
  have h5 := fills2 (a := a) true qs bs ds C1 Z Z 0 0 0 (q-1) hd
  simp only [zero_add] at h5
  rw [replicate_word] at h5
  have h6 := rewinds2 (a := a) qs bs ds C1 Z Z 0 0 0 (List.replicate (q-1) true)
  simp only [List.length_replicate] at h6
  have h7 := edits2 (a := a) false qs bs ds C1 R1 Z 0 0 0 b hvb
  dsimp only [R1] at h7
  rw [overwrite_replicate q b hbq true false] at h7
  have h8 := fills3 (a := a) true qs bs ds C1 C2 Z 0 0 0 b hvb
  simp only [zero_add] at h8
  rw [replicate_word] at h8
  have h9 := rewinds3 (a := a) qs bs ds C1 C2 Z 0 0 0 (List.replicate b true)
  simp only [List.length_replicate] at h9
  have h10 := writes3 (a := a) qs bs ds C1 C2 RB 0 0 0
  dsimp only [RB] at h10
  rw [overwrite_c3 b hb] at h10
  have h11 := lefts3 (a := a) qs bs ds C1 C2 C3 0 0 1
  have h12 := BinaryDescriptorCleanupList.one_hoare (5 : Fin 8)
    (bank (a := a) qs bs ds C1 C2 C3 0 0 0) ds
    (by change CountedLoopReuseAlphabet.binary ds=BinaryDescriptorStack.descriptor ds
        rw [CountedGuardGadgetHeaders.binary_eq,BinaryDescriptorStackRoundtrip.descriptor_encoded]) rfl
  have hdl := GrowingCounterData.canonical_width ds (RecursiveChildQuotientsConstant.bits_canonical _)
  rw [hd] at hdl
  have hbl := GrowingCounterData.canonical_width bs cb
  rw [hvb] at hbl
  have hld := Nat.log2_le_self (q-1)
  have hlb := Nat.log2_le_self b
  exact (((((((((((h1.seq h2).seq h3).seq h4).seq h5).seq h6).seq h7).seq h8).seq h9).seq h10).seq h11).seq h12).consequence
    (fun _ h => h) (fun _ h => h) (by omega)

theorem input_private (qs bs : List Bool) (i : Fin 8)
    (hi : i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7) :
    (input (a := a) qs bs).tape i=(fun _ => blank) ∧ (input (a := a) qs bs).head i=0 := by
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨rfl,rfl⟩

theorem exact_constants (q b : ℕ) (qs bs : List Bool) :
    (output (a := a) q b qs bs).tape 2=word (c1 q b) ∧ (output (a := a) q b qs bs).head 2=0 ∧
    (output (a := a) q b qs bs).tape 3=word (c2 q b) ∧ (output (a := a) q b qs bs).head 3=0 ∧
    (output (a := a) q b qs bs).tape 4=word (c3 b) ∧ (output (a := a) q b qs bs).head 4=0 :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem retains_headers (q b : ℕ) (qs bs : List Bool) :
    (output (a := a) q b qs bs).tape 0=CountedLoopReuseAlphabet.binary qs ∧ (output (a := a) q b qs bs).head 0=1 ∧
    (output (a := a) q b qs bs).tape 1=CountedLoopReuseAlphabet.binary bs ∧ (output (a := a) q b qs bs).head 1=1 :=
  ⟨rfl,rfl,rfl,rfl⟩

theorem private_clean (q b : ℕ) (qs bs : List Bool) (i : Fin 8) (hi : i=5 ∨ i=6 ∨ i=7) :
    (output (a := a) q b qs bs).tape i=(fun _ => blank) ∧ (output (a := a) q b qs bs).head i=0 := by
  rcases hi with rfl | rfl | rfl <;> exact ⟨rfl,rfl⟩

end
end IntegerMultBounds.Machine.CountedGuardConstants
