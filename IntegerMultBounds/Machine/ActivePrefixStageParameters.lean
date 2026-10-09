import IntegerMultBounds.Machine.ActivePrefixLayoutShapes
import IntegerMultBounds.Machine.ActiveTargetHighestPairLayoutGeometry

/-! Original consecutive stage slots determine the active-target geometry.
A node consists of M equal f-axis slots between unchanged active spectators;
source and target are distinct original slots, numbered from left to right.
All Parameters proof fields are derived from this actual decomposition. -/
namespace IntegerMultBounds.Machine.ActivePrefixStageParameters
open CompactGadgetReservationShape (Shape)
open ActivePrefixLayoutShapes (Parameters)

structure Stage (s : Shape) where
  slots : ℕ
  f : ℕ
  left : ℕ
  right : ℕ
  rho : ℕ
  source : Fin slots
  target : Fin slots
  distinct : source≠target
  activeAxes : left+slots*f+right=s.active
  positiveWidth : 0<f
  widthFits : f≤s.axes
  selectedFits : rho<s.chunk

variable {s : Shape}

def highAxes (v : Stage s) (i : Fin v.slots) := v.left+i.val*v.f
def lowAxes (v : Stage s) (i : Fin v.slots) := (v.slots-i.val-1)*v.f+v.right
def before (v : Stage s) := highAxes v v.target*s.chunk+(s.chunk-v.rho)
def after (v : Stage s) := lowAxes v v.target*s.chunk+v.rho

theorem axes_split (v : Stage s) (i : Fin v.slots) : highAxes v i+v.f+lowAxes v i=s.active := by
  have hi := i.isLt
  have hcount : i.val+1+(v.slots-i.val-1)=v.slots := by omega
  have hm := congrArg (fun a => a*v.f) hcount
  simp only [Nat.add_mul,Nat.one_mul] at hm
  have ha := v.activeAxes
  unfold highAxes lowAxes
  omega

theorem width_split (v : Stage s) : s.chunk-v.rho+(v.f-1)*s.chunk+v.rho=v.f*s.chunk := by
  have hr := v.selectedFits
  have hf := v.positiveWidth
  have hn : v.f-1+1=v.f := by omega
  have hm := congrArg (fun a => a*s.chunk) hn
  simp only [Nat.add_mul,Nat.one_mul] at hm
  omega

theorem active_size (v : Stage s) : before v+(v.f-1)*s.chunk+after v=s.active*s.chunk := by
  have ha := congrArg (fun a => a*s.chunk) (axes_split v v.target)
  have hw := width_split v
  simp only [Nat.add_mul] at ha
  unfold before after
  omega

theorem compact_fits (v : Stage s) : (v.f-1)*s.guard≤s.H := by
  change (v.f-1)*s.guard≤s.axes*s.guard
  exact Nat.mul_le_mul_right s.guard (by have := v.widthFits; omega)

def parameters (v : Stage s) (hG : 1≤s.guard) (hGK : s.guard+1≤s.chunk) : Parameters s where
  q := s.chunk
  b := s.guard
  n := v.f-1
  rho := v.rho
  f := v.f
  before := before v
  after := after v
  compactFits := compact_fits v
  activeSize := active_size v
  hb := hG
  hbq := hGK
  hnf := by have := v.positiveWidth; omega
  hr := v.selectedFits

theorem positive_before (v : Stage s) : 1≤before v := by
  have := v.selectedFits
  unfold before
  omega

theorem positive_axes (v : Stage s) : 0<s.axes := by
  have := v.positiveWidth
  have := v.widthFits
  omega

theorem positive_H (v : Stage s) (hG : 1≤s.guard) : 1≤s.H := by
  change 1≤s.axes*s.guard
  exact Nat.mul_pos (positive_axes v) hG

theorem nontrivial (v : Stage s) (hG : 1≤s.guard) (hGK : s.guard+1≤s.chunk) (hf : 2≤v.f) :
    0<(parameters v hG hGK).n := by
  change 0<v.f-1
  omega

theorem dyadic_guard (ell : ℕ) (hG : s.guard=4*ell+6) (hK : 8*ell+16≤s.chunk) :
    2≤s.guard ∧ s.guard+3≤s.chunk := by omega

/-- The manuscript's compact radix fixes every guard-side condition. -/
def dyadicParameters (v : Stage s) (ell : ℕ) (hG : s.guard=4*ell+6)
    (hK : 8*ell+16≤s.chunk) : Parameters s := parameters v (by omega) (by omega)

theorem dyadic_ready (v : Stage s) (ell : ℕ) (hG : s.guard=4*ell+6)
    (hK : 8*ell+16≤s.chunk) (hf : 2≤v.f) :
    0<(dyadicParameters v ell hG hK).n ∧
    2≤(dyadicParameters v ell hG hK).b ∧
    (dyadicParameters v ell hG hK).b+3≤(dyadicParameters v ell hG hK).q ∧
    1≤s.H ∧ 1≤(dyadicParameters v ell hG hK).before := by
  obtain ⟨hb,hbq⟩ := dyadic_guard ell hG hK
  exact ⟨nontrivial v (by omega) (by omega) hf,hb,hbq,positive_H v (by omega),positive_before v⟩

end IntegerMultBounds.Machine.ActivePrefixStageParameters
