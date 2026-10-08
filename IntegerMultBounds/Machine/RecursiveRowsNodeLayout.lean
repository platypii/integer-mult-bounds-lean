import IntegerMultBounds.Machine.RecursiveInterchangeLayout

/-! A network runs on the already cyclically divided row descriptor. Recursive
child regrouping therefore divides rows by one, never by the role count again. -/
namespace IntegerMultBounds.Machine.RecursiveRowsNodeLayout
open RecursiveInterchangeLayout

theorem child_role (q roles b : ℕ) (parent : Descriptor) {m : ℕ} (i j : Fin m) :
    child q 1 b (role parent roles) i j = child q roles b parent i j := by
  simp [child,role]

theorem role_positive (roles : ℕ) (parent : Descriptor) (hr : 0 < roles)
    (hp : parent.Positive) (hd : roles ∣ parent.rows) : (role parent roles).Positive :=
  ⟨hp.1,Nat.div_pos (Nat.le_of_dvd hp.2.1 hd) hr,hp.2.2.1,hp.2.2.2.1,hp.2.2.2.2⟩

end IntegerMultBounds.Machine.RecursiveRowsNodeLayout
