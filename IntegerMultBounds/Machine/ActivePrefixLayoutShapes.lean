import IntegerMultBounds.Machine.ActivePrefixLayoutGeometry
import IntegerMultBounds.Machine.ActivePrefixSelectedOffsetBank
import IntegerMultBounds.Machine.ActivePrefixParityOffsetBank

/-! Runtime producer shapes specialized to the unchanged active-target layout.
These are geometry identities only; physical synthesis is a separate duty. -/
namespace IntegerMultBounds.Machine.ActivePrefixLayoutShapes
open CompactGadgetReservationShape CompactActiveTargetLayout CompactActiveTargetGeometry
open ActivePrefixLayoutGeometry

structure Parameters (s : Shape) where
  q : ℕ
  b : ℕ
  n : ℕ
  rho : ℕ
  f : ℕ
  before : ℕ
  after : ℕ
  compactFits : n*b≤s.H
  activeSize : before+n*q+after=s.active*s.chunk
  hb : 1≤b
  hbq : b+1≤q
  hnf : n+1=f
  hr : rho<q

def targetShape (s : Shape) (p : Parameters s) (offset : ℕ) (hfit : offset+p.f*p.q≤p.before) :
    ActivePrefixSelectedOffsetBank.Shape where
  W := targetWidth s p.before
  startT := tStart s (p.n*p.b) p.before
  startX := offset
  q := p.q
  b := p.b
  n := p.n
  rho := p.rho
  f := p.f
  tempFits := target_t_fits s (p.n*p.b) p.before p.compactFits
  sourceFits := by unfold targetWidth; omega
  hb := p.hb
  hbq := p.hbq
  hnf := p.hnf
  hr := p.hr

def backBeforeShape (s : Shape) (p : Parameters s) (offset : ℕ) (hfit : offset+p.f*p.q≤p.before) :
    ActivePrefixParityOffsetBank.Shape where
  W := backWidth s (p.n*p.q) p.before p.after
  startT := p.after
  startX := p.n*p.q+p.after+offset
  q := p.q
  b := p.b
  n := p.n
  rho := p.rho
  f := p.f
  tempFits := by unfold backWidth; omega
  sourceFits := by unfold backWidth targetWidth; omega
  hb := p.hb
  hbq := p.hbq
  hnf := p.hnf
  hr := p.hr

def backAfterShape (s : Shape) (p : Parameters s) (offset : ℕ) (hfit : offset+p.f*p.q≤p.after) :
    ActivePrefixParityOffsetBank.Shape where
  W := backWidth s (p.n*p.q) p.before p.after
  startT := p.after
  startX := offset
  q := p.q
  b := p.b
  n := p.n
  rho := p.rho
  f := p.f
  tempFits := by unfold backWidth; omega
  sourceFits := by unfold backWidth; omega
  hb := p.hb
  hbq := p.hbq
  hnf := p.hnf
  hr := p.hr

abbrev Address (s : Shape) (p : Parameters s) (rows : ℕ) :=
  CompactActiveTargetLayout.Address s (p.n*p.b) (p.n*p.q) p.before p.after rows

def targetRank (s : Shape) (p : Parameters s) {rows : ℕ} (x : Address s p rows) :=
  (targetPrefixIndex s (p.n*p.b) (p.n*p.q) p.before p.after rows x).val
def backRank (s : Shape) (p : Parameters s) {rows : ℕ} (x : Address s p rows) :=
  (backPrefixIndex s (p.n*p.b) (p.n*p.q) p.before p.after rows x).val

theorem target_rank_lt (s : Shape) (p : Parameters s) {rows : ℕ} (x : Address s p rows) :
    targetRank s p x<rows*2^(targetWidth s p.before) := by
  have h := (targetPrefixIndex s (p.n*p.b) (p.n*p.q) p.before p.after rows x).isLt
  change targetRank s p x < _ at h
  rwa [target_count s (p.n*p.b) p.before rows p.compactFits] at h

theorem back_rank_lt (s : Shape) (p : Parameters s) {rows : ℕ} (x : Address s p rows) :
    backRank s p x<rows*2^(backWidth s (p.n*p.q) p.before p.after) := by
  have h := (backPrefixIndex s (p.n*p.b) (p.n*p.q) p.before p.after rows x).isLt
  change backRank s p x < _ at h
  rwa [back_count s (p.n*p.b) (p.n*p.q) p.before p.after rows p.compactFits] at h

theorem back_width (s : Shape) (p : Parameters s) :
    backWidth s (p.n*p.q) p.before p.after=2*s.H+s.F+s.active*s.chunk := by
  have := p.activeSize
  unfold backWidth targetWidth
  omega

end IntegerMultBounds.Machine.ActivePrefixLayoutShapes
