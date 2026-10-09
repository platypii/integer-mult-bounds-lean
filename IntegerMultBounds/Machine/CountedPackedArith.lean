import IntegerMultBounds.Machine.CountedPackedRuntimeLine
import IntegerMultBounds.Compact.PackedArithValue

/-! Five genuine packed arithmetic lines with fixed control, using only
runtime q/b/count headers and returning all fourteen private tapes blank. -/
namespace IntegerMultBounds.Machine.CountedPackedArith
noncomputable section
variable {a : ℕ}
open PackedArith
open ColumnTransducer (Rule addRule subRule)

def tail (hs : Fin 3 → List Bool) : Tapes 17 a :=
  (FixedHeaderBankCopy.headerBank hs).append (FixedHeaderBankCopy.empty 14)
def bank (payload : Tapes 9 a) (hs : Fin 3 → List Bool) : Tapes 26 a := payload.append (tail hs)

def shuffle : Fin (22+4) ≃ Fin (9+17) where
  toFun := ![0,1,2,3,4,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,5,6,7,8]
  invFun := ![0,1,2,3,4,22,23,24,25,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def liftL (L : Fin 9 ≃ Fin 9) : Fin (9+17) ≃ Fin (9+17) where
  toFun := fun j => Fin.addCases (fun i => Fin.castAdd 17 (L i)) (Fin.natAdd 9) j
  invFun := fun j => Fin.addCases (fun i => Fin.castAdd 17 (L.symm i)) (Fin.natAdd 9) j
  left_inv := by intro j; induction j using Fin.addCases <;> simp [Fin.addCases_left,Fin.addCases_right]
  right_inv := by intro j; induction j using Fin.addCases <;> simp [Fin.addCases_left,Fin.addCases_right]
def placement (L : Fin 9 ≃ Fin 9) := shuffle.trans (liftL L)

theorem input_eq (payload : Tapes 5 a) (hs : Fin 3 → List Bool) :
    CountedPackedRuntimeLine.input payload hs = payload.append (tail hs) := by
  unfold CountedPackedRuntimeLine.input CountedPackedRuntimeLine.caller
    CountedPackedShapeHeaders.input tail Tapes.append
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem shuffle_bank (v : Tapes 5 a) (w : Tapes 17 a) (extra : Tapes 4 a) :
    ((v.append w).append extra).reindex shuffle = (v.append extra).append w := by
  unfold Tapes.reindex Tapes.append shuffle
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem lift_bank (v : Tapes 9 a) (w : Tapes 17 a) (L : Fin 9 ≃ Fin 9) :
    (v.append w).reindex (liftL L) = (v.reindex L).append w := by
  unfold Tapes.reindex Tapes.append liftL
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals induction i using Fin.addCases <;> simp [Fin.addCases_left,Fin.addCases_right]

theorem placed_bank (v : Tapes 5 a) (hs : Fin 3 → List Bool) (extra : Tapes 4 a) (L : Fin 9 ≃ Fin 9) :
    ((CountedPackedRuntimeLine.input v hs).append extra).reindex (placement L) =
      bank ((v.append extra).reindex L) hs := by
  rw [input_eq]
  change (((v.append (tail hs)).append extra).reindex shuffle).reindex (liftL L) = _
  rw [shuffle_bank,lift_bank]
  rfl

def line {s : ℕ} (kind : Fin 3) (op : Bool → Bool → Bool) (R : Rule s)
    (L : Fin 9 ≃ Fin 9) (a : ℕ) :=
  reindex (extend (CountedPackedRuntimeLine.program kind op R a) 4) (placement L)
def program (a : ℕ) := seq (seq (seq (seq
  (line 0 (fun x z => x && z) addRule L1 a)
  (line 1 (fun x _ => x) addRule L2 a))
  (line 2 (fun _ z => z) addRule L3a a))
  (line 0 (fun x z => x && z) subRule L3b a))
  (line 1 (fun x z => xor x z) subRule L4 a)

private theorem line_hoare {s : ℕ} (kind : Fin 3) (op : Bool → Bool → Bool) (R : Rule s)
    (q b : ℕ) (hb : 1 ≤ b) (hbq : b+1 ≤ q) (xs zs acc : List Bool)
    (f g h : ℤ → Fin (a+4)) (p0 p1 p2 p3 p4 : ℤ) (hs : Fin 3 → List Bool)
    (hv : ∀ i, Counter.value (hs i) = CountedPackedShapeHeaders.originalValues q b zs.length i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i))
    (hxs : zs.length*(CountedPackedShapeHeaders.shape kind q b hb hbq).sx ≤ xs.length)
    (hacc : acc.length = zs.length*(CountedPackedShapeHeaders.shape kind q b hb hbq).st)
    (hf : f (p0-1) = blank) (hg : g (p1-1) = blank) (hh : h (p3-1) = blank)
    (hh' : h (p3+acc.length) = blank) (L : Fin 9 ≃ Fin 9) (extra : Tapes 4 a) :
    HoareTime (line kind op R L a)
      (fun v => v = bank ((PackedLine.bank (putWord f p0 (xs.map bitSymbol))
        (putWord g p1 (zs.map bitSymbol)) (fun _ => blank)
        (putWord h p3 (acc.map bitSymbol)) (fun _ => blank) p0 p1 p2 p3 p4).append extra |>.reindex L) hs)
      (fun v => v = bank ((PackedLine.bank (putWord f p0 (xs.map bitSymbol))
        (putWord g p1 (zs.map bitSymbol)) (fun _ => blank)
        (putWord h p3 (acc.map bitSymbol))
        (putWord (fun _ => blank) p4 ((ColumnTransducer.digits R 0
          (acc.zip (Gather.gather op (CountedPackedShapeHeaders.shape kind q b hb hbq) xs zs zs.length))).map bitSymbol))
        p0 p1 p2 p3 p4).append extra |>.reindex L) hs)
      (530*((zs.length+1)*(q+b+1))+3*acc.length) := by
  have hh := hoare_place (CountedPackedRuntimeLine.runs kind op R q b hb hbq xs zs acc
    f g h p0 p1 p2 p3 p4 hs hv hc hxs hacc hf hg hh hh') (placement L) extra
  rw [placed_bank,placed_bank] at hh
  exact hh

variable (q b : ℕ) (hb : 1 ≤ b) (hbq : b+1 ≤ q)
variable (V W Z : List Bool) (f g z : ℤ → Fin (a+4)) (p0 p1 p2 p3 p4 p5 p6 p7 p8 : ℤ)
variable (hs : Fin 3 → List Bool)

/-- All five fixed-control calls preserve the original headers and clear private scratch. -/
theorem forward_hoare (hV : V.length = Z.length * q) (hW : W.length = Z.length * b)
    (hf : f (p0 - 1) = blank) (hf' : f (p0 + V.length) = blank) (hg : g (p1 - 1) = blank)
    (hg' : g (p1 + W.length) = blank) (hz : z (p2 - 1) = blank)
    (hv : ∀ i, Counter.value (hs i) = CountedPackedShapeHeaders.originalValues q b Z.length i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    HoareTime (program a)
      (fun v => v = bank (PackedArith.input V W Z f g z p0 p1 p2 p3 p4 p5 p6 p7 p8) hs)
      (fun v => v = bank (PackedArith.output q b hb hbq V W Z f g z p0 p1 p2 p3 p4 p5 p6 p7 p8) hs)
      (2669*((Z.length+1)*(q+b+1))) := by
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10⟩ := lengths q b hb hbq V W Z hV hW
  set O1 := off1 q b hb hbq W Z
  set V1 := v1 q b hb hbq V W Z
  set O2 := off2 q b hb hbq V W Z
  set W1 := w1 q b hb hbq V W Z
  set O3a := off3a q b hb hbq W Z
  set T1 := t1 q b hb hbq V W Z
  set O3b := off3b q b hb hbq V W Z
  set V2 := v2 q b hb hbq V W Z
  set O4 := off4 q b hb hbq V W Z
  set W2 := w2 q b hb hbq V W Z
  -- line 1: V₁ := V + off1
  have h1 := line_hoare 0 (fun x z => x && z) addRule q b hb hbq W Z V
    g z f p1 p2 p7 p0 p3 hs hv hc (by simp only [CountedPackedShapeHeaders.shape, Matrix.cons_val_zero, maskShift]; rw [hW]) (by simp only [CountedPackedShapeHeaders.shape, Matrix.cons_val_zero, maskShift]; exact hV)
    hg hz hf hf' L1
    (⟨fun i => if i = 0 then p4 else if i = 1 then p5 else if i = 2 then p6 else p8,
      fun i => if i = 0 then (fun _ => blank) else if i = 1 then (fun _ => blank) else if i = 2 then (fun _ => blank) else (fun _ => blank)⟩ : Tapes 4 a)
  rw [L1_bank, L1_bank] at h1
  -- line 2: W₁ := W + off2
  have h2 := line_hoare 1 (fun x _ => x) addRule q b hb hbq V1 Z W
    (fun _ => blank) z g p3 p2 p7 p1 p4 hs hv hc (by change Z.length*q ≤ V1.length; rw [l2]) (by change W.length = Z.length*b; exact hW)
    rfl hz hg hg' L2
    (⟨fun i => if i = 0 then p0 else if i = 1 then p5 else if i = 2 then p6 else p8,
      fun i => if i = 0 then putWord f p0 (V.map bitSymbol) else if i = 1 then (fun _ => blank)
        else if i = 2 then (fun _ => blank) else (fun _ => blank)⟩ : Tapes 4 a)
  rw [L2_bank, L2_bank] at h2
  -- line 3a: T₁ := V₁ + controls
  have h3 := line_hoare 2 (fun _ z => z) addRule q b hb hbq W Z V1
    g z (fun _ => blank) p1 p2 p7 p3 p8 hs hv hc
    (by change Z.length*1 ≤ W.length; rw [mul_one,hW]; exact Nat.le_mul_of_pos_right _ hb)
    (by change V1.length = Z.length*q; exact l2) hg hz rfl rfl L3a
    (⟨fun i => if i = 0 then p0 else if i = 1 then p4 else if i = 2 then p5 else p6,
      fun i => if i = 0 then putWord f p0 (V.map bitSymbol)
        else if i = 1 then putWord (fun _ => blank) p4 (W1.map bitSymbol) else if i = 2 then (fun _ => blank)
        else (fun _ => blank)⟩ : Tapes 4 a)
  rw [L3a_bank, L3a_bank] at h3
  -- line 3b: V₂ := T₁ − off3b
  have h4 := line_hoare 0 (fun x z => x && z) subRule q b hb hbq W1 Z T1
    (fun _ => blank) z (fun _ => blank) p4 p2 p7 p8 p5 hs hv hc (by simp only [CountedPackedShapeHeaders.shape, Matrix.cons_val_zero, maskShift]; rw [l4])
    (by simp only [CountedPackedShapeHeaders.shape, Matrix.cons_val_zero, maskShift]; exact l6) rfl hz rfl rfl L3b
    (⟨fun i => if i = 0 then p0 else if i = 1 then p1 else if i = 2 then p3 else p6,
      fun i => if i = 0 then putWord f p0 (V.map bitSymbol)
        else if i = 1 then putWord g p1 (W.map bitSymbol)
        else if i = 2 then putWord (fun _ => blank) p3 (V1.map bitSymbol) else (fun _ => blank)⟩ : Tapes 4 a)
  rw [L3b_bank, L3b_bank] at h4
  -- line 4: W₂ := W₁ − off4
  have h5 := line_hoare 1 (fun x z => xor x z) subRule q b hb hbq V2 Z W1
    (fun _ => blank) z (fun _ => blank) p5 p2 p7 p4 p6 hs hv hc (by change Z.length*q ≤ V2.length; rw [l8])
    (by change W1.length = Z.length*b; exact l4) rfl hz rfl rfl L4
    (⟨fun i => if i = 0 then p0 else if i = 1 then p1 else if i = 2 then p3 else p8,
      fun i => if i = 0 then putWord f p0 (V.map bitSymbol)
        else if i = 1 then putWord g p1 (W.map bitSymbol)
        else if i = 2 then putWord (fun _ => blank) p3 (V1.map bitSymbol)
        else putWord (fun _ => blank) p8 (T1.map bitSymbol)⟩ : Tapes 4 a)
  rw [L4_bank, L4_bank] at h5
  have hall := (((h1.seq h2).seq h3).seq h4).seq h5
  refine hall.consequence (fun v hv => by rw [hv]; rfl) (fun v hv => by rw [hv]; rfl) ?_
  simp only [hV, hW, l2, l4, l6]
  have hnq : Z.length*q ≤ (Z.length+1)*(q+b+1) := by nlinarith
  have hnb : Z.length*b ≤ (Z.length+1)*(q+b+1) := by nlinarith
  have hp : 1 ≤ (Z.length+1)*(q+b+1) := by nlinarith
  omega


/-- The machine endpoint realizes the compact arithmetic value specification. -/
theorem forward_hoare_value (hV : V.length = Z.length*q) (hW : W.length = Z.length*b)
    (hf : f (p0-1) = blank) (hf' : f (p0+V.length) = blank)
    (hg : g (p1-1) = blank) (hg' : g (p1+W.length) = blank) (hz : z (p2-1) = blank)
    (hv : ∀ i, Counter.value (hs i) = CountedPackedShapeHeaders.originalValues q b Z.length i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    HoareTime (program a)
      (fun v => v = bank (PackedArith.input V W Z f g z p0 p1 p2 p3 p4 p5 p6 p7 p8) hs)
      (fun v => v = bank (PackedArith.output q b hb hbq V W Z f g z p0 p1 p2 p3 p4 p5 p6 p7 p8) hs ∧
        ((Counter.value (v2 q b hb hbq V W Z) : ℤ), (Counter.value (w2 q b hb hbq V W Z) : ℤ)) =
          Compact.packedEarly ((2 : ℤ)^q) ((2 : ℤ)^b) (Z.map Compact.PowerTwo.ctrl)
            (Counter.value V) (Counter.value W))
      (2669*((Z.length+1)*(q+b+1))) := by
  refine (forward_hoare q b hb hbq V W Z f g z p0 p1 p2 p3 p4 p5 p6 p7 p8 hs
    hV hW hf hf' hg hg' hz hv hc).consequence (fun _ h => h) ?_ (le_refl _)
  intro v h
  exact ⟨h, Compact.PowerTwo.forward_value q b hb hbq V W Z hV hW⟩

end
end IntegerMultBounds.Machine.CountedPackedArith
