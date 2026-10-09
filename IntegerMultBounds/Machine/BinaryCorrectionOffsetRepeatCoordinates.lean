import IntegerMultBounds.Machine.BinaryCorrectionOffsetRepeatBudget
import IntegerMultBounds.Machine.BinaryAddressOffsetRepeatCoordinates

/-! The correction offset for a complete physical rotation row is precisely
the packed controls minus packed 2*z*w modulo2^(n*q), where w is that row's regular temporary address and z is the
retained original control word. Dirty-back and spectator fields only repeat it. -/
namespace IntegerMultBounds.Machine.BinaryCorrectionOffsetRepeatCoordinates
open BinaryCorrectionOffsetRepeatData

def row (q b n H L p back h y l : ℕ) :=
  (p*2^(n*q)+back)*(H*2^(n*b)*L)+(h*2^(n*b)+y)*L+l

theorem row_eq (q b n H L p back h y l : ℕ) :
    row q b n H L p back h y l=((((p*2^(n*q)+back)*H+h)*2^(n*b)+y)*L+l) := by
  unfold row; ring

theorem row_lt (q b n P H L p back h y l : ℕ)
    (hp : p<P) (hback : back<2^(n*q)) (hh : h<H) (hy : y<2^(n*b)) (hl : l<L) :
    row q b n H L p back h y l<(P*2^(n*q))*(H*2^(n*b)*L) :=
  BinaryAddressOffsetRepeatCoordinates.row_lt b q n P H L p back h y l hp hback hh hy hl

theorem word_length (q b n P H L : ℕ) (Z : List Bool) (hb : 1≤b) (hbq : b+1≤q) (hZ : Z.length=n) :
    (destination q b n L ((P*H)*2^(n*q)) Z hb hbq).length=
      ((P*2^(n*q))*(H*2^(n*b)*L))*(n*q) := by
  rw [destination,BinaryAddressOffsetRepeatData.copies_length,BinaryAddressOffsetRepeatData.expanded_length _ (n*q) L
    (offsets_uniform q b n Z hb hbq hZ)]
  simp only [offsets,List.length_map,List.length_range]
  ring

theorem field_eq (q b n P H L p back h y l : ℕ) (Z : List Bool) (hb : 1≤b) (hbq : b+1≤q)
    (hp : p<P) (hback : back<2^(n*q)) (hh : h<H) (hy : y<2^(n*b)) (hl : l<L) (hZ : Z.length=n) :
    Gather.field (destination q b n L ((P*H)*2^(n*q)) Z hb hbq)
      (row q b n H L p back h y l*(n*q)) (n*q)=BinaryCorrectionOffsetValue.rowWord q b n y Z hb hbq := by
  have hpback : p*2^(n*q)+back<P*2^(n*q) := by nlinarith
  have hk : (p*2^(n*q)+back)*H+h<(P*H)*2^(n*q) := by nlinarith
  have he := BinaryAddressOffsetRepeatValue.repeated_field (offsets q b n Z hb hbq) (n*q) L ((P*H)*2^(n*q))
    ((p*2^(n*q)+back)*H+h) y l (offsets_uniform q b n Z hb hbq hZ)
    hk (by simpa [offsets] using hy) hl
  simpa only [row_eq,destination,offsets,List.length_map,List.length_range,List.getElem_map,List.getElem_range] using he

theorem field_value (q b n P H L p back h y l : ℕ) (Z : List Bool) (hb : 1≤b) (hbq : b+1≤q)
    (hp : p<P) (hback : back<2^(n*q)) (hh : h<H) (hy : y<2^(n*b)) (hl : l<L) (hZ : Z.length=n) :
    (Counter.value (Gather.field (destination q b n L ((P*H)*2^(n*q)) Z hb hbq)
      (row q b n H L p back h y l*(n*q)) (n*q)) : ℤ)=
      (Compact.Radix.pack ((2 : ℤ)^q) (Z.map Compact.PowerTwo.ctrl)-
        Compact.Radix.pack ((2 : ℤ)^q) (List.zipWith (fun z w => 2*z*w) (Z.map Compact.PowerTwo.ctrl)
          (Compact.Radix.digits ((2 : ℤ)^b) n y))) % (2 : ℤ)^(n*q) := by
  rw [field_eq q b n P H L p back h y l Z hb hbq hp hback hh hy hl hZ,
    ←BinaryCorrectionOffsetValue.field_eq q b n y Z hb hbq hZ hy]
  exact BinaryCorrectionOffsetValue.field_value q b n y Z hb hbq hZ hy


private theorem signed_pack (Q : ℤ) (C D : List ℤ) (hlen : C.length=D.length) :
    Compact.Radix.pack Q (List.zipWith (fun z w => z*(1-2*w)) C D)=
      Compact.Radix.pack Q C-Compact.Radix.pack Q (List.zipWith (fun z w => 2*z*w) C D) := by
  have he : ∀ (C D : List ℤ), List.zipWith (fun z w => z*(1-2*w)) C D=
      List.zipWith (fun x y => x-y) C (List.zipWith (fun z w => 2*z*w) C D) := by
    intro C
    induction C with
    | nil => intro D; simp
    | cons c C ih =>
      intro D
      cases D with
      | nil => simp
      | cons d D => simp only [List.zipWith_cons_cons,ih]; congr 1; ring
  rw [he,Compact.PowerTwo.pack_sub Q C _ (by simp [List.length_zipWith,hlen])]

theorem signed_field_value (q b n P H L p back h y l : ℕ) (Z : List Bool) (hb : 1≤b) (hbq : b+1≤q)
    (hp : p<P) (hback : back<2^(n*q)) (hh : h<H) (hy : y<2^(n*b)) (hl : l<L) (hZ : Z.length=n) :
    (Counter.value (Gather.field (destination q b n L ((P*H)*2^(n*q)) Z hb hbq)
      (row q b n H L p back h y l*(n*q)) (n*q)) : ℤ)=
      Compact.Radix.pack ((2 : ℤ)^q) (List.zipWith (fun z w => z*(1-2*w)) (Z.map Compact.PowerTwo.ctrl)
        (Compact.Radix.digits ((2 : ℤ)^b) n y)) % (2 : ℤ)^(n*q) := by
  rw [field_value q b n P H L p back h y l Z hb hbq hp hback hh hy hl hZ,
    signed_pack _ _ _ (by simp [hZ,Compact.Radix.digits_length])]

end IntegerMultBounds.Machine.BinaryCorrectionOffsetRepeatCoordinates
