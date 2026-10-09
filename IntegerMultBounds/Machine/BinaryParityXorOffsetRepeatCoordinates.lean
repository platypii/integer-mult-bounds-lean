import IntegerMultBounds.Machine.BinaryParityXorOffsetRepeatBudget
import IntegerMultBounds.Machine.BinaryAddressOffsetRepeatCoordinates

/-! Each complete physical row contains the modular negative of packed source
parity XOR original controls, independently of its dirty-back and spectator coordinates. -/
namespace IntegerMultBounds.Machine.BinaryParityXorOffsetRepeatCoordinates
open BinaryParityXorOffsetRepeatData

def row (q b n H L p back h y l : ℕ) :=
  (p*2^(n*b)+back)*(H*2^(n*q)*L)+(h*2^(n*q)+y)*L+l

theorem row_eq (q b n H L p back h y l : ℕ) :
    row q b n H L p back h y l=((((p*2^(n*b)+back)*H+h)*2^(n*q)+y)*L+l) := by
  unfold row; ring

theorem row_lt (q b n P H L p back h y l : ℕ)
    (hp : p<P) (hback : back<2^(n*b)) (hh : h<H) (hy : y<2^(n*q)) (hl : l<L) :
    row q b n H L p back h y l<(P*2^(n*b))*(H*2^(n*q)*L) :=
  BinaryAddressOffsetRepeatCoordinates.row_lt q b n P H L p back h y l hp hback hh hy hl

theorem word_length (q b n P H L : ℕ) (Z : List Bool) (hb : 1≤b) (hbq : b+1≤q) :
    (destination q b n L ((P*H)*2^(n*b)) Z hb hbq).length=
      ((P*2^(n*b))*(H*2^(n*q)*L))*(n*b) := by
  rw [destination,BinaryAddressOffsetRepeatData.copies_length,BinaryAddressOffsetRepeatData.expanded_length _ (n*b) L
    (offsets_uniform q b n Z hb hbq)]
  simp only [offsets,BinaryParityXorOffsetData.rows,List.length_map,List.length_range]
  ring

theorem field_eq (q b n P H L p back h y l : ℕ) (Z : List Bool) (hb : 1≤b) (hbq : b+1≤q)
    (hp : p<P) (hback : back<2^(n*b)) (hh : h<H) (hy : y<2^(n*q)) (hl : l<L) :
    Gather.field (destination q b n L ((P*H)*2^(n*b)) Z hb hbq)
      (row q b n H L p back h y l*(n*b)) (n*b)=TwosComplement.negWord (BinaryParityXorOffsetData.rowWord q b n y Z hb hbq) := by
  have hpback : p*2^(n*b)+back<P*2^(n*b) := by nlinarith
  have hk : (p*2^(n*b)+back)*H+h<(P*H)*2^(n*b) := by nlinarith
  have he := BinaryAddressOffsetRepeatValue.repeated_field (offsets q b n Z hb hbq) (n*b) L ((P*H)*2^(n*b))
    ((p*2^(n*b)+back)*H+h) y l (offsets_uniform q b n Z hb hbq)
    hk (by simpa [offsets,BinaryParityXorOffsetData.rows] using hy) hl
  simpa only [row_eq,destination,offsets,BinaryParityXorOffsetData.rows,List.length_map,List.length_range,List.getElem_map,List.getElem_range] using he

theorem field_value (q b n P H L p back h y l : ℕ) (Z : List Bool) (hb : 1≤b) (hbq : b+1≤q)
    (hp : p<P) (hback : back<2^(n*b)) (hh : h<H) (hy : y<2^(n*q)) (hl : l<L) (hZ : Z.length=n) :
    (Counter.value (Gather.field (destination q b n L ((P*H)*2^(n*b)) Z hb hbq)
      (row q b n H L p back h y l*(n*b)) (n*b)) : ℤ)=
      (-Compact.Radix.pack ((2 : ℤ)^b) (List.zipWith (fun v z => (v%2+z)%2)
        (Compact.Radix.digits ((2 : ℤ)^q) n y) (Z.map Compact.PowerTwo.ctrl))) % (2 : ℤ)^(n*b) := by
  rw [field_eq q b n P H L p back h y l Z hb hbq hp hback hh hy hl,
    ←BinaryParityXorOffsetValue.field_eq q b n y Z hb hbq hy]
  exact BinaryParityXorOffsetValue.field_value q b n y Z hb hbq hZ hy

end IntegerMultBounds.Machine.BinaryParityXorOffsetRepeatCoordinates
