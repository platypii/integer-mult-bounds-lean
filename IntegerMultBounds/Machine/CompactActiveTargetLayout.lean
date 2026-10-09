import IntegerMultBounds.Machine.CompactGadgetReservationShape
import IntegerMultBounds.Machine.RecursiveInterchangeRows

/-! Literal unchanged compact reservation with its target in the active block.
Only the two compact front fields fit in H; the target need not fit there.
Every unused front bit, slack bit, active spectator, dirty back bit and payload
coordinate remains an independent complete range. -/
namespace IntegerMultBounds.Machine.CompactActiveTargetLayout
open CompactGadgetReservationShape
open RecursiveInterchangeRows (pack pack_val)

structure Address (s : Shape) (w m before after rows : ℕ) where
  row : Fin rows
  u : Fin (2^w)
  uTail : Fin (2^(s.H-w))
  t : Fin (2^w)
  tTail : Fin (2^(s.H-w))
  frontSlack : Fin (2^s.F)
  activeBefore : Fin (2^before)
  target : Fin (2^m)
  activeAfter : Fin (2^after)
  back : Fin (2^(s.H+s.B))
  payload : Fin s.payload

abbrev Fields (s : Shape) (w m before after rows : ℕ) :=
  Fin rows × Fin (2^w) × Fin (2^(s.H-w)) × Fin (2^w) × Fin (2^(s.H-w)) ×
    Fin (2^s.F) × Fin (2^before) × Fin (2^m) × Fin (2^after) × Fin (2^(s.H+s.B)) × Fin s.payload

def fieldsEquiv (s : Shape) (w m before after rows : ℕ) :
    Address s w m before after rows ≃ Fields s w m before after rows where
  toFun x := (x.row,x.u,x.uTail,x.t,x.tTail,x.frontSlack,x.activeBefore,x.target,x.activeAfter,x.back,x.payload)
  invFun x := ⟨x.1,x.2.1,x.2.2.1,x.2.2.2.1,x.2.2.2.2.1,x.2.2.2.2.2.1,
    x.2.2.2.2.2.2.1,x.2.2.2.2.2.2.2.1,x.2.2.2.2.2.2.2.2.1,
    x.2.2.2.2.2.2.2.2.2.1,x.2.2.2.2.2.2.2.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

def size (s : Shape) (w m before after rows : ℕ) :=
  rows*(2^w*(2^(s.H-w)*(2^w*(2^(s.H-w)*(2^s.F*(2^before*(2^m*(2^after*(2^(s.H+s.B)*s.payload)))))))))

theorem size_eq (s : Shape) (w m before after rows : ℕ) (hw : w≤s.H)
    (hactive : before+m+after=s.active*s.chunk) :
    size s w m before after rows=rows*s.recordWidth := by
  have he : w+(s.H-w)+w+(s.H-w)+s.F+before+m+after+(s.H+s.B)=s.bits := by
    unfold Shape.bits; omega
  unfold size Shape.recordWidth
  calc
    _ = rows*2^(w+(s.H-w)+w+(s.H-w)+s.F+before+m+after+(s.H+s.B))*s.payload := by
      simp only [pow_add]; ring
    _ = _ := by rw [he]; ring

private def join {A B : Type*} {a b : ℕ} (e : A ≃ Fin a) (f : B ≃ Fin b) : A × B ≃ Fin (a*b) :=
  (e.prodCongr f).trans finProdFinEquiv

private def rawEquiv (s : Shape) (w m before after rows : ℕ) :
    Fields s w m before after rows ≃ Fin (size s w m before after rows) :=
  join (Equiv.refl _) (join (Equiv.refl _) (join (Equiv.refl _) (join (Equiv.refl _)
    (join (Equiv.refl _) (join (Equiv.refl _) (join (Equiv.refl _) (join (Equiv.refl _)
      (join (Equiv.refl _) (join (Equiv.refl _) (Equiv.refl _))))))))))

def indexEquiv (s : Shape) (w m before after rows : ℕ) (hw : w≤s.H)
    (hactive : before+m+after=s.active*s.chunk) :
    Address s w m before after rows ≃ Fin (rows*s.recordWidth) :=
  ((fieldsEquiv s w m before after rows).trans (rawEquiv s w m before after rows)).trans
    (finCongr (size_eq s w m before after rows hw hactive))

def index (s : Shape) (w m before after rows : ℕ) (hw : w≤s.H)
    (hactive : before+m+after=s.active*s.chunk) (x : Address s w m before after rows) :=
  indexEquiv s w m before after rows hw hactive x

theorem index_bijective (s : Shape) (w m before after rows : ℕ) (hw : w≤s.H)
    (hactive : before+m+after=s.active*s.chunk) :
    Function.Bijective (index s w m before after rows hw hactive) :=
  (indexEquiv s w m before after rows hw hactive).bijective

/-- The original row-major ordinal, with the target still inside the active
block rather than in any compact reservation. -/
theorem index_val (s : Shape) (w m before after rows : ℕ) (hw : w≤s.H)
    (hactive : before+m+after=s.active*s.chunk) (x : Address s w m before after rows) :
    (index s w m before after rows hw hactive x).val=
      ((((((((((x.row.val*2^w+x.u.val)*2^(s.H-w)+x.uTail.val)*2^w+x.t.val)*
        2^(s.H-w)+x.tTail.val)*2^s.F+x.frontSlack.val)*2^before+x.activeBefore.val)*
        2^m+x.target.val)*2^after+x.activeAfter.val)*2^(s.H+s.B)+x.back.val)*s.payload+x.payload.val) := by
  change (pack x.row (pack x.u (pack x.uTail (pack x.t (pack x.tTail
    (pack x.frontSlack (pack x.activeBefore (pack x.target (pack x.activeAfter
      (pack x.back x.payload)))))))))).val=_
  simp only [pack_val]
  ring

end IntegerMultBounds.Machine.CompactActiveTargetLayout
