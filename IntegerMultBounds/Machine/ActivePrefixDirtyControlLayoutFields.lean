import IntegerMultBounds.Machine.ActivePrefixDirtyControlData
import IntegerMultBounds.Machine.ActivePrefixLayoutBack
import IntegerMultBounds.Machine.ActivePrefixDirtyControlLayoutAbsorption

/-! Compact U in the actual target and back prefixes, with no extra source
digit or fictitious wide source slot. -/
namespace IntegerMultBounds.Machine.ActivePrefixDirtyControlLayoutFields
open CompactGadgetReservationShape CompactActiveTargetGeometry
open ActivePrefixLayoutShapes ActivePrefixLayoutGeometry ActivePrefixLayoutFields
open RecursiveInterchangeRows (pack)
open BinaryAddressTableData (row)

def uStart (s : Shape) (w before : ℕ) := (s.H-w)+w+(s.H-w)+s.F+before

variable (s : Shape) (p : Parameters s) {rows : ℕ}

theorem u_fits : uStart s (p.n*p.b) p.before+p.n*p.b≤targetWidth s p.before := by
  have := p.compactFits
  unfold uStart targetWidth
  omega

theorem target_u (x : Address s p rows) :
    Gather.field (prefixWord (targetWidth s p.before) (targetRank s p x))
      (uStart s (p.n*p.b) p.before) (p.n*p.b)=row (p.n*p.b) x.u.val := by
  apply field_eq_row _ _ _ _ _ (u_fits s p) x.u.isLt
  have he := congrArg Fin.val (u_prefix_index s (p.n*p.b) (p.n*p.q) p.before p.after rows x)
  change targetRank s p x=(pack (pack x.row x.u)
    (uRestIndex s (p.n*p.b) (p.n*p.q) p.before p.after rows x)).val at he
  rw [he]
  have hp : 2^(uStart s (p.n*p.b) p.before)=uCopies s (p.n*p.b) p.before :=
    (ActiveRepairRankFieldsGeometry.u_copies_pow _ _ _).symm
  rw [hp,packed_high,packed_low]

theorem back_u (x : Address s p rows) :
    Gather.field (prefixWord (backWidth s (p.n*p.q) p.before p.after) (backRank s p x))
      (p.n*p.q+p.after+uStart s (p.n*p.b) p.before) (p.n*p.b)=row (p.n*p.b) x.u.val := by
  apply field_eq_row _ _ _ _ _ (by
    have := u_fits s p
    unfold backWidth
    omega) x.u.isLt
  rw [pow_add,←Nat.div_div_eq_div_mul,pow_add]
  change (pack (pack (targetPrefixIndex s (p.n*p.b) (p.n*p.q) p.before p.after rows x)
    x.target) x.activeAfter).val/(2^(p.n*p.q)*2^p.after)/2^(uStart s (p.n*p.b) p.before)%2^(p.n*p.b)=_
  rw [Nat.mul_comm (2^(p.n*p.q)),←Nat.div_div_eq_div_mul,packed_high,packed_high]
  have h := congrArg Counter.value (target_u s p x)
  rw [field_value _ _ _ _ (u_fits s p),BinaryAddressTableData.row_rank _ _ x.u.isLt] at h
  exact h

def targetShape : ActivePrefixDirtyControlData.Shape .selected where
  W := targetWidth s p.before
  startT := tStart s (p.n*p.b) p.before
  startU := uStart s (p.n*p.b) p.before
  q := p.q
  b := p.b
  n := p.n
  tempFits := target_t_fits s (p.n*p.b) p.before p.compactFits
  controlFits := u_fits s p
  hb := p.hb
  hbq := p.hbq

def compactShape : ActivePrefixDirtyControlData.Shape .parity where
  W := backWidth s (p.n*p.q) p.before p.after
  startT := p.after
  startU := p.n*p.q+p.after+uStart s (p.n*p.b) p.before
  q := p.q
  b := p.b
  n := p.n
  tempFits := by change p.after+p.n*p.q≤_; unfold backWidth; omega
  controlFits := by have := u_fits s p; unfold backWidth; omega
  hb := p.hb
  hbq := p.hbq

theorem target_absorbed (hn : 0<p.n) (hrecord : s.bits+1≤s.payload) :
    (targetShape s p).W+(targetShape s p).n*(targetShape s p).q+
      (targetShape s p).q+(targetShape s p).b+1≤
        2^(p.n*p.q)*targetSuffix s p.after :=
  ActivePrefixDirtyControlLayoutAbsorption.target s p hn hrecord

theorem compact_absorbed (hn : 0<p.n) (hb : 2≤p.b) (hrecord : s.bits+1≤s.payload) :
    (compactShape s p).W+(compactShape s p).n*(compactShape s p).q+
      (compactShape s p).q+(compactShape s p).b+1≤
        2^(p.n*p.b)*compactSuffix s (p.n*p.b) :=
  ActivePrefixDirtyControlLayoutAbsorption.compact s p hn hb hrecord

end IntegerMultBounds.Machine.ActivePrefixDirtyControlLayoutFields
