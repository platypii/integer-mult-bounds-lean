module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHaloPreparationWorkspaceBound
import Mathlib.Tactic.Linarith

/-! Geometry-controller space is quadratic only in encoded header widths. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds.MathlibTM2.Fast.TableVM

theorem weightWorkspaceWidth_eq (P q w t u : ℕ) :
    weightWorkspaceWidth P q w t u = w+q+13*P+3*t.size+u.size+18 := by
  unfold weightWorkspaceWidth coefficientWorkspaceWidth
  simp only [Nat.size_zero]
  omega

theorem geometryWidths_le (P q w t u : ℕ) :
    let D := P+q+w+t.size+u.size+w.size+1
    haloGeometryWidth t w ≤ 20*D ∧ weightWorkspaceWidth P q w t u ≤ 20*D := by
  rw [weightWorkspaceWidth_eq]
  unfold haloGeometryWidth
  dsimp only
  constructor <;> omega

theorem tblC_le_header_square (V D : ℕ) (hV : V ≤ 20*D) (hD : 1 ≤ D) :
    tblC V V ≤ 20000*D^2 := by
  calc
    _ ≤ tblC (20*D) (20*D) := by unfold tblC; gcongr
    _ ≤ _ := by
      unfold tblC
      nlinarith [Nat.le_mul_self D]

theorem geometryControllers_le (P q w t u : ℕ) :
    let D := P+q+w+t.size+u.size+w.size+1
    tblC (haloGeometryWidth t w) (haloGeometryWidth t w) ≤ 20000*D^2 ∧
      tblC (weightWorkspaceWidth P q w t u) (weightWorkspaceWidth P q w t u) ≤ 20000*D^2 := by
  obtain ⟨hG,hW⟩ := geometryWidths_le P q w t u
  exact ⟨tblC_le_header_square _ _ hG (by omega),tblC_le_header_square _ _ hW (by omega)⟩

theorem ScalarPlacement.haloPreparationWorkspace_le_headers
    (P N q l s t u band a b L : ℕ) (ha : a ≤ s) (hb : b ≤ s) (hL : L ≤ s) :
    let D := P+q+(2*q+8)+t.size+u.size+(2*q+8).size+1
    let F := P+N+q+l+s+t+u+band+1
    ScalarPlacement.conditionalHaloGroupPreparationWorkspace P N q l s t u band a b L ≤
      180000*D^2+2050000*F*D := by
  dsimp only
  let D := P+q+(2*q+8)+t.size+u.size+(2*q+8).size+1
  let F := P+N+q+l+s+t+u+band+1
  obtain ⟨hG,hW⟩ := geometryWidths_le P q (2*q+8) t u
  have htable := (geometryControllers_le P q (2*q+8) t u).1
  have hsum : haloGeometryWidth t (2*q+8)+weightWorkspaceWidth P q (2*q+8) t u+q+1 ≤ 41*D := by
    dsimp only [D]
    omega
  calc
    _ ≤ 9*tblC (haloGeometryWidth t (2*q+8)) (haloGeometryWidth t (2*q+8))+
        50000*F*(haloGeometryWidth t (2*q+8)+weightWorkspaceWidth P q (2*q+8) t u+q+1) :=
      ScalarPlacement.conditionalHaloGroupPreparationWorkspace_le_uniform P N q l s t u band a b L ha hb hL
    _ ≤ 9*(20000*D^2)+50000*F*(41*D) :=
      Nat.add_le_add (Nat.mul_le_mul_left 9 htable) (Nat.mul_le_mul_left (50000*F) hsum)
    _ = _ := by dsimp only [D,F]; ring

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
