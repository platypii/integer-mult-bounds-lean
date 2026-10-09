import IntegerMultBounds.Machine.BinaryPackedEarlyLayout

/-! Every cell of the unchanged complete role word has exactly one full early
address, including arbitrary unused, dirty back, active and payload coordinates. -/
namespace IntegerMultBounds.Machine.BinaryPackedEarlyAddress
open CompactGadgetReservationShape
open BinaryPackedEarlyLayout
open RecursiveInterchangeRows (pack)

 def decode (s : Shape) (q b n rows : ℕ) (i : Fin (size s q b n rows)) : Address s q b n rows :=
  let d7 := finProdFinEquiv.symm i
  let d6 := finProdFinEquiv.symm d7.1
  let d5 := finProdFinEquiv.symm d6.1
  let d4 := finProdFinEquiv.symm d5.1
  let d3 := finProdFinEquiv.symm d4.1
  let d2 := finProdFinEquiv.symm d3.1
  let d1 := finProdFinEquiv.symm d2.1
  (d1.2,d3.2,⟨d1.1,d2.2,d4.2,d5.2,d6.2,d7.2⟩)

 theorem decode_index (s : Shape) (q b n rows : ℕ) (x : Address s q b n rows) :
    decode s q b n rows (rawIndex s q b n rows x)=x := by
  rcases x with ⟨v,w,⟨r,tv,tw,m,bk,p⟩⟩
  simp only [decode,rawIndex,pack,Equiv.symm_apply_apply]

 theorem index_decode (s : Shape) (q b n rows : ℕ) (i : Fin (size s q b n rows)) :
    rawIndex s q b n rows (decode s q b n rows i)=i := by
  simp only [decode,rawIndex,pack,Prod.mk.eta,Equiv.apply_symm_apply]
  exact finProdFinEquiv.apply_symm_apply i

 def rawEquiv (s : Shape) (q b n rows : ℕ) : Address s q b n rows ≃ Fin (size s q b n rows) where
  toFun := rawIndex s q b n rows
  invFun := decode s q b n rows
  left_inv := decode_index s q b n rows
  right_inv := index_decode s q b n rows

 def equiv (s : Shape) (q b n rows : ℕ) (hq : n*q≤s.H) (hb : n*b≤s.H) :
    Address s q b n rows ≃ Fin (rows*s.recordWidth) :=
  (rawEquiv s q b n rows).trans (finCongr (size_eq s q b n rows hq hb))

 theorem equiv_index (s : Shape) (q b n rows : ℕ) (hq : n*q≤s.H) (hb : n*b≤s.H) (x : Address s q b n rows) :
    equiv s q b n rows hq hb x=index s q b n rows hq hb x := rfl

 theorem index_bijective (s : Shape) (q b n rows : ℕ) (hq : n*q≤s.H) (hb : n*b≤s.H) :
    Function.Bijective (index s q b n rows hq hb) := (equiv s q b n rows hq hb).bijective

end IntegerMultBounds.Machine.BinaryPackedEarlyAddress
