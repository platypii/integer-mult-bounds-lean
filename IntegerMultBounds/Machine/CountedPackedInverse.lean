import IntegerMultBounds.Machine.CountedPackedArith
import IntegerMultBounds.Compact.PackedInverseValue

/-! Actual fixed-control inverse packed arithmetic from the original runtime
q/b/count headers. All fourteen private tapes are blank at both endpoints. -/
namespace IntegerMultBounds.Machine.CountedPackedInverse
noncomputable section
variable {a : ℕ}
open PackedInverse
open ColumnTransducer (Rule addRule subRule)
abbrev bank (payload : Tapes 9 a) (hs : Fin 3 → List Bool) : Tapes 26 a :=
  CountedPackedArith.bank payload hs
abbrev line := @CountedPackedArith.line

def program (a : ℕ) := seq (seq (seq (seq
  (line 1 (fun x z => xor x z) addRule I1 a)
  (line 2 (fun _ z => z) subRule I2a a))
  (line 0 (fun x z => x && z) addRule I2b a))
  (line 1 (fun x _ => x) subRule I3 a))
  (line 0 (fun x z => x && z) subRule I4 a)

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
    f g h p0 p1 p2 p3 p4 hs hv hc hxs hacc hf hg hh hh') (CountedPackedArith.placement L) extra
  rw [CountedPackedArith.placed_bank,CountedPackedArith.placed_bank] at hh
  exact hh

variable (q b : ℕ) (hb : 1 ≤ b) (hbq : b+1 ≤ q)
variable (V2 W2 Z : List Bool) (f g z : ℤ → Fin (a+4)) (p0 p1 p2 p3 p4 p5 p6 p7 p8 : ℤ)
variable (hs : Fin 3 → List Bool)

theorem inverse_hoare (hV : V2.length = Z.length * q) (hW : W2.length = Z.length * b)
    (hf : f (p0 - 1) = blank) (hf' : f (p0 + V2.length) = blank) (hg : g (p1 - 1) = blank)
    (hg' : g (p1 + W2.length) = blank) (hz : z (p2 - 1) = blank)
    (hv : ∀ i, Counter.value (hs i) = CountedPackedShapeHeaders.originalValues q b Z.length i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    HoareTime (program a)
      (fun x => x = bank (PackedInverse.input V2 W2 Z f g z p0 p1 p2 p3 p4 p5 p6 p7 p8) hs)
      (fun x => x = bank (PackedInverse.output q b hb hbq V2 W2 Z f g z p0 p1 p2 p3 p4 p5 p6 p7 p8) hs)
      (2669*((Z.length+1)*(q+b+1))) := by
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10⟩ := lengths q b hb hbq V2 W2 Z hV hW
  set W1 := w1 q b hb hbq V2 W2 Z
  set T := t q b hb hbq V2 W2 Z
  set V1 := v1 q b hb hbq V2 W2 Z
  set Wd := w q b hb hbq V2 W2 Z
  set Vd := v q b hb hbq V2 W2 Z
  -- line 1: W₁ := W₂ + toggled parities of V₂
  have h1 := line_hoare 1 (fun x z => xor x z) addRule q b hb hbq V2 Z W2
    f z g p0 p2 p7 p1 p3 hs hv hc (by change Z.length*q ≤ V2.length; rw [hV]) (by change W2.length = Z.length*b; exact hW)
    hf hz hg hg' I1
    (⟨fun i => if i = 0 then p4 else if i = 1 then p5 else if i = 2 then p6 else p8,
      fun i => if i = 0 then (fun _ => blank) else if i = 1 then (fun _ => blank) else if i = 2 then (fun _ => blank) else (fun _ => blank)⟩ : Tapes 4 a)
  rw [I1_bank, I1_bank] at h1
  -- line 2a: T := V₂ − controls
  have h2 := line_hoare 2 (fun _ z => z) subRule q b hb hbq W2 Z V2
    g z f p1 p2 p7 p0 p4 hs hv hc
    (by change Z.length*1 ≤ W2.length; rw [mul_one,hW]; exact Nat.le_mul_of_pos_right _ hb)
    (by change V2.length = Z.length*q; exact hV) hg hz hf hf' I2a
    (⟨fun i => if i = 0 then p3 else if i = 1 then p5 else if i = 2 then p6 else p8,
      fun i => if i = 0 then putWord (fun _ => blank) p3 (W1.map bitSymbol) else if i = 1 then (fun _ => blank)
        else if i = 2 then (fun _ => blank) else (fun _ => blank)⟩ : Tapes 4 a)
  rw [I2a_bank, I2a_bank] at h2
  -- line 2b: V₁ := T + masked digits of W₁
  have h3 := line_hoare 0 (fun x z => x && z) addRule q b hb hbq W1 Z T
    (fun _ => blank) z (fun _ => blank) p3 p2 p7 p4 p5 hs hv hc (by change Z.length*b ≤ W1.length; rw [l2])
    (by change T.length = Z.length*q; exact l4) rfl hz rfl rfl I2b
    (⟨fun i => if i = 0 then p0 else if i = 1 then p1 else if i = 2 then p6 else p8,
      fun i => if i = 0 then putWord f p0 (V2.map bitSymbol)
        else if i = 1 then putWord g p1 (W2.map bitSymbol) else if i = 2 then (fun _ => blank) else (fun _ => blank)⟩ : Tapes 4 a)
  rw [I2b_bank, I2b_bank] at h3
  -- line 3: W := W₁ − parities of V₁
  have h4 := line_hoare 1 (fun x _ => x) subRule q b hb hbq V1 Z W1
    (fun _ => blank) z (fun _ => blank) p5 p2 p7 p3 p6 hs hv hc (by change Z.length*q ≤ V1.length; rw [l6])
    (by change W1.length = Z.length*b; exact l2) rfl hz rfl rfl I3
    (⟨fun i => if i = 0 then p0 else if i = 1 then p1 else if i = 2 then p4 else p8,
      fun i => if i = 0 then putWord f p0 (V2.map bitSymbol)
        else if i = 1 then putWord g p1 (W2.map bitSymbol)
        else if i = 2 then putWord (fun _ => blank) p4 (T.map bitSymbol) else (fun _ => blank)⟩ : Tapes 4 a)
  rw [I3_bank, I3_bank] at h4
  -- line 4: V := V₁ − masked digits of W
  have h5 := line_hoare 0 (fun x z => x && z) subRule q b hb hbq Wd Z V1
    (fun _ => blank) z (fun _ => blank) p6 p2 p7 p5 p8 hs hv hc (by change Z.length*b ≤ Wd.length; rw [l8])
    (by change V1.length = Z.length*q; exact l6) rfl hz rfl rfl I4
    (⟨fun i => if i = 0 then p0 else if i = 1 then p1 else if i = 2 then p3 else p4,
      fun i => if i = 0 then putWord f p0 (V2.map bitSymbol)
        else if i = 1 then putWord g p1 (W2.map bitSymbol)
        else if i = 2 then putWord (fun _ => blank) p3 (W1.map bitSymbol)
        else putWord (fun _ => blank) p4 (T.map bitSymbol)⟩ : Tapes 4 a)
  rw [I4_bank, I4_bank] at h5
  have hall := (((h1.seq h2).seq h3).seq h4).seq h5
  refine hall.consequence (fun x hx => by rw [hx]; rfl) (fun x hx => by rw [hx]; rfl) ?_
  simp only [hV, hW, l2, l4, l6]
  have hnq : Z.length*q ≤ (Z.length+1)*(q+b+1) := by nlinarith
  have hnb : Z.length*b ≤ (Z.length+1)*(q+b+1) := by nlinarith
  have hp : 1 ≤ (Z.length+1)*(q+b+1) := by nlinarith
  omega


/-- The recovered words are a genuine preimage of the compact arithmetic map. -/
theorem inverse_hoare_value (hV : V2.length = Z.length*q) (hW : W2.length = Z.length*b)
    (hf : f (p0-1) = blank) (hf' : f (p0+V2.length) = blank)
    (hg : g (p1-1) = blank) (hg' : g (p1+W2.length) = blank) (hz : z (p2-1) = blank)
    (hv : ∀ i, Counter.value (hs i) = CountedPackedShapeHeaders.originalValues q b Z.length i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    HoareTime (program a)
      (fun x => x = bank (PackedInverse.input V2 W2 Z f g z p0 p1 p2 p3 p4 p5 p6 p7 p8) hs)
      (fun x => x = bank (PackedInverse.output q b hb hbq V2 W2 Z f g z p0 p1 p2 p3 p4 p5 p6 p7 p8) hs ∧
        Compact.packedEarly ((2 : ℤ)^q) ((2 : ℤ)^b) (Z.map Compact.PowerTwo.ctrl)
          (Counter.value (v q b hb hbq V2 W2 Z)) (Counter.value (w q b hb hbq V2 W2 Z)) =
            ((Counter.value V2 : ℤ), (Counter.value W2 : ℤ)))
      (2669*((Z.length+1)*(q+b+1))) := by
  refine (inverse_hoare q b hb hbq V2 W2 Z f g z p0 p1 p2 p3 p4 p5 p6 p7 p8 hs
    hV hW hf hf' hg hg' hz hv hc).consequence (fun _ h => h) ?_ (le_refl _)
  intro x h
  exact ⟨h, Compact.PowerTwo.inverse_value q b hb hbq V2 W2 Z hV hW⟩

end
end IntegerMultBounds.Machine.CountedPackedInverse
