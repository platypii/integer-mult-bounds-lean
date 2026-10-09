import IntegerMultBounds.Machine.CompactComplexRecursiveGeometry
import IntegerMultBounds.Machine.ButterflySpectatorOriginal

/-! Recursive intervals select original immutable address positions. Arbitrary
role rows remain outer spectators and the serialized dimension stays Shape.bits. -/
namespace IntegerMultBounds.Machine.CompactSpectatorVisitGeometry
open CompactGadgetReservationShape (Shape)
open CompactComplexRecursiveGeometry

/-- Visit positions are numbered from the high end of the active field, while
physical butterfly bit positions count from the low end above the back field. -/
def selected (s : Shape) (rho left i : ℕ) :=
  s.H+s.B+(s.active-1-(left+i))*s.chunk+rho

theorem selected_lt {s : Shape} (rho : Fin s.chunk) {left k : ℕ}
    (visit : Visit s.active left k) (i : Fin (arity^k)) :
    selected s rho.val left i.val<s.bits := by
  have hf := visit.fits
  have hi := i.isLt
  have hr := rho.isLt
  have hp : 0<arity^k := pow_pos (by decide) _
  have he : s.active-1-(left+i.val)+1≤s.active := by omega
  have hm := Nat.mul_le_mul_right s.chunk he
  unfold selected Shape.bits
  nlinarith

theorem selected_injective {s : Shape} (rho : Fin s.chunk) {left k : ℕ}
    (visit : Visit s.active left k) :
    Function.Injective (fun i : Fin (arity^k) => selected s rho.val left i.val) := by
  intro i j he
  have hf := visit.fits
  have hi := i.isLt
  have hj := j.isLt
  have hK : 0<s.chunk := Nat.pos_of_ne_zero (by intro hz; simpa [hz] using rho.isLt)
  apply Fin.ext
  dsimp only at he
  unfold selected at he
  have hm : (s.active-1-(left+i.val))*s.chunk=(s.active-1-(left+j.val))*s.chunk := by omega
  have hs := Nat.eq_of_mul_eq_mul_right hK hm
  omega

theorem selected_succ {s : Shape} (rho : Fin s.chunk) {left k : ℕ}
    (visit : Visit s.active left k) (i : ℕ) (hi : i+1<arity^k) :
    selected s rho.val left (i+1)+s.chunk=selected s rho.val left i := by
  have hf := visit.fits
  have he : s.active-1-(left+i)=s.active-1-(left+(i+1))+1 := by omega
  unfold selected
  rw [he,Nat.add_mul,Nat.one_mul]
  omega

/-- All surrounding global bits remain present even for a one-coordinate leaf. -/
abbrev Array (s : Shape) (rows ell : ℕ) := ButterflySpectatorGeometry.Array rows s.bits (2^ell)

/-- Actual coefficient cardinality includes every unchanged role row and all
original compact/slack/spectator address bits. -/
theorem coefficient_count (s : Shape) (rows ell : ℕ) :
    ButterflySpectatorGeometry.Size rows s.bits (2^ell)=rows*2^s.bits*2^ell := by
  unfold ButterflySpectatorGeometry.Size
  ring

/-- Role subdivision changes only the outer row count. No global address bit
or polynomial coefficient is removed from a child representation. -/
theorem role_volume (c m d K j : ℕ) (s : Shape) (ell : ℕ) (hc : 0<c) (hK : 0<K)
    (hj : j<CompactGlobalRowPadding.depth m d) :
    ButterflySpectatorGeometry.Size (CompactGlobalRowPadding.rowsAt c m d K (j+1)) s.bits (2^ell)*c=
      ButterflySpectatorGeometry.Size (CompactGlobalRowPadding.rowsAt c m d K j) s.bits (2^ell) :=
  CompactGlobalRowPadding.role_volume c m d K j (2^s.bits*2^ell) hc hK hj

/-- One actual descendant butterfly executes over the entire immutable word,
including arbitrary outer rows, global address spectators and all polynomials. -/
theorem runs_visit (s : Shape) (rows ell p : ℕ) (hr : 0<rows)
    (rho : Fin s.chunk) {left k : ℕ} (visit : Visit s.active left k)
    (i : Fin (arity^k)) (f : Array s rows ell)
    (hw : ButterflySpectatorGeometry.Width rows s.bits (2^ell) p f) :
    HoareTime ButterflySpectatorOriginal.program
      (fun z => z=ButterflySpectatorOriginal.bank rows s.bits (selected s rho.val left i.val) (2^ell) p
        (ButterflyStreamData.full (fun _ => blank) 0 f))
      (fun z => z=ButterflySpectatorOriginal.bank rows s.bits (selected s rho.val left i.val+1) (2^ell) p
        (ButterflyStreamData.full (fun _ => blank) 0
          (ButterflySpectatorGeometry.applyAxis rows s.bits (selected s rho.val left i.val) (2^ell) p
            (selected_lt rho visit i) f)))
      (ButterflySpectatorOriginal.cost rows s.bits (selected s rho.val left i.val) (2^ell) p) :=
  ButterflySpectatorOriginal.runs rows s.bits _ (2^ell) p hr (selected_lt rho visit i)
    (pow_pos (by decide) ell) f hw

end IntegerMultBounds.Machine.CompactSpectatorVisitGeometry
