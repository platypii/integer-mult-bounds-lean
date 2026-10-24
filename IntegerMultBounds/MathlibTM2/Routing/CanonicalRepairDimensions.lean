module

public import IntegerMultBounds.MathlibTM2.Routing.CanonicalRouterArithmetic

/-! Inner one-row repair uses the original physical dimension for its field
count and one extra key bit. These identities remove redundant dimension inputs. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactDigits IntegerMultBounds.MathlibTM2.Layer.CompactGadget
variable {A : ℕ}

theorem repair_fieldsLen (p : Par) : fieldsLen (selectiveLen p 0) = 3*p.wc+p.wy := by
  simp [fieldsLen,selectiveLen,Fin.sum_univ_succ]
  omega

theorem repair_keyLen (p : Par) (rb : ℕ) :
    fieldsLen (selectiveKeyLen p 0 rb) = fieldsLen (selectiveLen p 0) + rb := by
  simp [fieldsLen,selectiveLen,selectiveKeyLen,Fin.sum_univ_succ]
  omega

theorem canonicalRepair_fieldsLen (n : ℕ) (hlarge : canonicalRouterStride n ≤ n)
    (r : Fin (canonicalRouterStride n)) :
    fieldsLen (selectiveLen (routerProfileParameters n (canonicalRouterStride n)
      (canonicalRouterGap n) r.val) 0) = n := by
  rw [repair_fieldsLen]
  exact routerProfileParameters_total n (canonicalRouterStride n) (canonicalRouterGap n) hlarge r

theorem canonicalRepair_keyLen (n : ℕ) (hlarge : canonicalRouterStride n ≤ n)
    (r : Fin (canonicalRouterStride n)) :
    fieldsLen (selectiveKeyLen (routerProfileParameters n (canonicalRouterStride n)
      (canonicalRouterGap n) r.val) 0 (canonicalScalarWidth 1)) = n+1 := by
  rw [repair_keyLen,canonicalRepair_fieldsLen n hlarge r]
  rfl

theorem canonicalRepair_countWord (n : ℕ) (hlarge : canonicalRouterStride n ≤ n)
    (r : Fin (canonicalRouterStride n)) (wb wp wk B : ℕ) :
    canonicalRepairPayload (A := A) (routerProfileParameters n (canonicalRouterStride n)
      (canonicalRouterGap n) r.val) 0 (canonicalScalarWidth 1) wb (n+1) wp wk 1 B (.inl .records) =
      binSyms (n+1) (2 ^ n) := by
  simp only [canonicalRepairPayload,one_mul]
  rw [canonicalRepair_fieldsLen n hlarge r]

theorem canonicalRepair_keyWord (n : ℕ) (hlarge : canonicalRouterStride n ≤ n)
    (r : Fin (canonicalRouterStride n)) (wb wm wp wk B : ℕ) :
    canonicalRepairPayload (A := A) (routerProfileParameters n (canonicalRouterStride n)
      (canonicalRouterGap n) r.val) 0 (canonicalScalarWidth 1) wb wm wp wk 1 B (.inr .keyLength) =
      binSyms wk (n+1) := by
  simp only [canonicalRepairPayload]
  rw [canonicalRepair_keyLen n hlarge r]

end IntegerMultBounds.MathlibTM2.Routing
