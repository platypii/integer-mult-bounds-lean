import IntegerMultBounds.Machine.BinaryPackedEarlyData
import IntegerMultBounds.Machine.CompactGadgetReservationHeadersCarvedData

/-! One unchanged serialized reservation for all four early updates. The target
occupies the leading n*q bits of temp; its dirty temporary occupies the leading
n*b bits of control. All remaining reserved/back/active/payload bits stay literal. -/
namespace IntegerMultBounds.Machine.BinaryPackedEarlyLayout
open CompactGadgetReservationShape
open RecursiveInterchangeRows (pack pack_val)
open BinaryPackedEarlyData

structure Spectators (s : Shape) (q b n rows : ℕ) where
  row : Fin rows
  targetTail : Fin (2^(s.H-n*q))
  tempTail : Fin (2^(s.H-n*b))
  middle : Fin (2^(s.F+s.active*s.chunk))
  back : Fin (2^(s.H+s.B))
  payload : Fin s.payload

abbrev Address (s : Shape) (q b n rows : ℕ) := State q b n (Spectators s q b n rows)

def size (s : Shape) (q b n rows : ℕ) :=
  ((((((rows*2^(n*q))*2^(s.H-n*q))*2^(n*b))*2^(s.H-n*b))*2^(s.F+s.active*s.chunk))*2^(s.H+s.B))*s.payload

theorem size_eq (s : Shape) (q b n rows : ℕ) (hq : n*q≤s.H) (hb : n*b≤s.H) :
    size s q b n rows=rows*s.recordWidth := by
  have he : n*q+(s.H-n*q)+n*b+(s.H-n*b)+(s.F+s.active*s.chunk)+(s.H+s.B)=s.bits := by
    unfold Shape.bits; omega
  unfold size Shape.recordWidth
  calc
    _ = rows*2^(n*q+(s.H-n*q)+n*b+(s.H-n*b)+(s.F+s.active*s.chunk)+(s.H+s.B))*s.payload := by
      simp only [pow_add]; ring
    _ = _ := by rw [he]; ring

def rawIndex (s : Shape) (q b n rows : ℕ) (x : Address s q b n rows) : Fin (size s q b n rows) :=
  pack (pack (pack (pack (pack (pack (pack x.2.2.row x.1) x.2.2.targetTail) x.2.1)
    x.2.2.tempTail) x.2.2.middle) x.2.2.back) x.2.2.payload

def index (s : Shape) (q b n rows : ℕ) (hq : n*q≤s.H) (hb : n*b≤s.H)
    (x : Address s q b n rows) : Fin (rows*s.recordWidth) :=
  Fin.cast (size_eq s q b n rows hq hb) (rawIndex s q b n rows x)

/-- No permutations or resizings are hidden in this map: this is the literal
mixed-radix ordinal of the original temp/control/back reservation. -/
theorem index_val (s : Shape) (q b n rows : ℕ) (hq : n*q≤s.H) (hb : n*b≤s.H)
    (x : Address s q b n rows) :
    (index s q b n rows hq hb x).val=
      (((((((x.2.2.row.val*2^(n*q)+x.1.val)*2^(s.H-n*q)+x.2.2.targetTail.val)*2^(n*b)+x.2.1.val)*
        2^(s.H-n*b)+x.2.2.tempTail.val)*2^(s.F+s.active*s.chunk)+x.2.2.middle.val)*
        2^(s.H+s.B)+x.2.2.back.val)*s.payload+x.2.2.payload.val) := by
  change (rawIndex s q b n rows x).val=_
  simp only [rawIndex,pack_val]

theorem preserved (s : Shape) (q b n rows : ℕ) (Z : List Bool) (hb : 1≤b) (hbq : b+1≤q)
    (x : Address s q b n rows) : (BinaryPackedEarlyData.run q b n Z hb hbq x).2.2=x.2.2 := rfl

end IntegerMultBounds.Machine.BinaryPackedEarlyLayout
