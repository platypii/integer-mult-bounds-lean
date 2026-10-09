import IntegerMultBounds.Machine.BinaryAddressOffsetRepeatConstructBudget

/-! Coordinate alignment with the actual swap--rotate--swap source order.
After swapping, the dirty-back field is before G=H*2^(n*q)*L. Every physical
rotation row receives the parity offset of its own selected source address. -/
namespace IntegerMultBounds.Machine.BinaryAddressOffsetRepeatCoordinates
open BinaryAddressOffsetRepeatData

def row (q b n H L p back h y l : ℕ) :=
  (p*2^(n*b)+back)*(H*2^(n*q)*L)+(h*2^(n*q)+y)*L+l

theorem row_eq (q b n H L p back h y l : ℕ) :
    row q b n H L p back h y l=((((p*2^(n*b)+back)*H+h)*2^(n*q)+y)*L+l) := by
  unfold row; ring

theorem row_lt (q b n P H L p back h y l : ℕ)
    (hp : p<P) (hb : back<2^(n*b)) (hh : h<H) (hy : y<2^(n*q)) (hl : l<L) :
    row q b n H L p back h y l<(P*2^(n*b))*(H*2^(n*q)*L) := by
  have hpback : p*2^(n*b)+back<P*2^(n*b) := by nlinarith
  have hk : (p*2^(n*b)+back)*H+h<(P*2^(n*b))*H := by nlinarith
  have hky : ((p*2^(n*b)+back)*H+h)*2^(n*q)+y<((P*2^(n*b))*H)*2^(n*q) := by nlinarith
  rw [row_eq]
  nlinarith

theorem word_length (q b n P H L : ℕ) (hb : 1≤b) (hbq : b+1≤q) :
    (destination q b n L ((P*H)*2^(n*b)) hb hbq).length=
      ((P*2^(n*b))*(H*2^(n*q)*L))*(n*b) := by
  rw [destination,copies_length,expanded_length _ (n*b) L
    (BinaryAddressOffsetRepeatValue.offsets_uniform q b n hb hbq)]
  simp only [offsets,List.length_map,List.length_range]
  ring

theorem field_eq (q b n P H L p back h y l : ℕ) (hb : 1≤b) (hbq : b+1≤q)
    (hp : p<P) (hback : back<2^(n*b)) (hh : h<H) (hy : y<2^(n*q)) (hl : l<L) :
    Gather.field (destination q b n L ((P*H)*2^(n*b)) hb hbq)
      (row q b n H L p back h y l*(n*b)) (n*b)=BinaryAddressOffsetValue.rowWord q b n y hb hbq := by
  have hpback : p*2^(n*b)+back<P*2^(n*b) := by nlinarith
  have hk : (p*2^(n*b)+back)*H+h<(P*H)*2^(n*b) := by nlinarith
  have he := BinaryAddressOffsetRepeatValue.repeated_field (offsets q b n hb hbq) (n*b) L ((P*H)*2^(n*b))
    ((p*2^(n*b)+back)*H+h) y l (BinaryAddressOffsetRepeatValue.offsets_uniform q b n hb hbq)
    hk (by simpa [offsets] using hy) hl
  simpa only [row_eq,destination,offsets,List.length_map,List.length_range,List.getElem_map,List.getElem_range] using he

theorem field_value (q b n P H L p back h y l : ℕ) (hb : 1≤b) (hbq : b+1≤q)
    (hp : p<P) (hback : back<2^(n*b)) (hh : h<H) (hy : y<2^(n*q)) (hl : l<L) :
    (Counter.value (Gather.field (destination q b n L ((P*H)*2^(n*b)) hb hbq)
      (row q b n H L p back h y l*(n*b)) (n*b)) : ℤ)=
      Compact.Radix.pack ((2 : ℤ)^b) ((Compact.Radix.digits ((2 : ℤ)^q) n y).map (·%2)) := by
  rw [field_eq q b n P H L p back h y l hb hbq hp hback hh hy hl,
    ←BinaryAddressOffsetValue.field_eq q b n y hb hbq hy]
  exact BinaryAddressOffsetValue.field_value q b n y hb hbq hy

end IntegerMultBounds.Machine.BinaryAddressOffsetRepeatCoordinates
