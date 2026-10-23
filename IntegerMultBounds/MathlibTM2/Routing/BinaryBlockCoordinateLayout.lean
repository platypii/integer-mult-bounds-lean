module

public import IntegerMultBounds.MathlibTM2.Routing.BinaryCoordinateTranslate
public import IntegerMultBounds.MathlibTM2.Routing.SourceRegionDispatch
public import IntegerMultBounds.MathlibTM2.Routing.BlockExchange
public import Mathlib.Tactic.FinCases

/-! Fixed scalar workspaces for the coordinate action of an interval exchange. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
variable {T Q A : ℕ} {P U : Type}
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host

def binaryBlockRegion (rg : Fin 11 → Fin T) (high : Bool) : Fin 7 → Fin T :=
  ![rg 0, rg (if high then 3 else 1), rg (if high then 4 else 2), rg 7, rg 8, rg 9, rg 10]

def binaryBlockTranslate (rg : Fin 11 → Fin T) (high : Bool) : Fin 9 → Fin T :=
  ![rg 0, rg (if high then 3 else 1), rg (if high then 1 else 3), rg 6, rg 5, rg 7, rg 8, rg 9, rg 10]

theorem binaryBlockRegion_injective (rg : Fin 11 → Fin T) (hrg : Function.Injective rg) (high : Bool) :
    Function.Injective (binaryBlockRegion rg high) := by
  intro i j h
  cases high <;> fin_cases i <;> fin_cases j <;> simp_all [binaryBlockRegion, hrg.eq_iff]

theorem binaryBlockTranslate_injective (rg : Fin 11 → Fin T) (hrg : Function.Injective rg) (high : Bool) :
    Function.Injective (binaryBlockTranslate rg high) := by
  intro i j h
  cases high <;> fin_cases i <;> fin_cases j <;> simp_all [binaryBlockTranslate, hrg.eq_iff]

def binaryBlockCoordinateCopy (rg : Fin 11 → Fin T) : Pr P T Q A U := bcopy (rg 0) (rg 5) (rg 7) (rg 8)

def binaryBlockCoordinateBranch (rg : Fin 11 → Fin T) (high : Bool) (r : Fin 3) : Pr P T Q A U :=
  if r = 1 then binaryCoordinateTranslateProgram (binaryBlockTranslate rg high) else binaryBlockCoordinateCopy rg

def binaryBlockCoordinateProgram (rg : Fin 11 → Fin T) : Pr P T Q A U :=
  sourceRegionDispatchProgram (binaryBlockRegion rg false)
    (fun r => if r = 2 then sourceRegionDispatchProgram (binaryBlockRegion rg true) (binaryBlockCoordinateBranch rg true)
      else binaryBlockCoordinateBranch rg false r)

/-- The scalar coordinate permutation uses four live comparisons and one
translation or copy, restoring every tape except its output. -/
theorem binaryBlockCoordinate_exec (body : P → Pr P T Q A U)
    (rg : Fin 11 → Fin T) (hrg : Function.Injective rg) (L n a b w q : ℕ)
    (hab : a + w ≤ b) (hb : b + w ≤ n) (hn : n < 2 ^ L) (hq : q < n)
    (v : HS T Q A U) (S : Stacks T A)
    (hcoordinate : S.R (rg 0) = binSyms L q)
    (haInput : S.R (rg 1) = binSyms L a) (haEnd : S.R (rg 2) = binSyms L (a + w))
    (hbInput : S.R (rg 3) = binSyms L b) (hbEnd : S.R (rg 4) = binSyms L (b + w))
    (hblank : ∀ j : Fin 11, j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 → S.R (rg j) = []) :
    ∃ (v' : HS T Q A U) (steps : ℕ), v'.user = v.user ∧ steps ≤ 50 * L + 54 ∧
      Exec body (binaryBlockCoordinateProgram rg) (mk v S) steps
        (mk v' { S with R := Function.update S.R (rg 5) (binSyms L (blockExchange a b w q) ++ S.R (rg 5)) }) := by
  let O : Stacks T A := { S with R := Function.update S.R (rg 5) (binSyms L (blockExchange a b w q) ++ S.R (rg 5)) }
  have hcopy (hvalue : blockExchange a b w q = q) (u : HS T Q A U) :
      ∃ (u' : HS T Q A U) (steps : ℕ), u'.user = u.user ∧ steps ≤ 18 * L + 18 ∧
        Exec body (binaryBlockCoordinateCopy rg) (mk u S) steps (mk u' O) := by
    obtain ⟨u', hu, he⟩ := bcopy_exec body
      (a := rg 0) (c := rg 5) (t₁ := rg 7) (t₂ := rg 8)
      (by simp [List.nodup_cons, hrg.eq_iff]) u S (hblank 7 (by simp)) (hblank 8 (by simp))
    rw [hcoordinate, length_binSyms] at he
    exact ⟨u', 6 * L + 6, hu, by omega, by simpa only [O, binaryBlockCoordinateCopy, hvalue] using he⟩
  have hmove (high : Bool) (hbase : (if high then b else a) ≤ q)
      (hresult : q - (if high then b else a) + (if high then a else b) < 2 ^ L)
      (hvalue : blockExchange a b w q = q - (if high then b else a) + (if high then a else b))
      (u : HS T Q A U) :
      ∃ (u' : HS T Q A U) (steps : ℕ), u'.user = u.user ∧ steps ≤ 18 * L + 18 ∧
        Exec body (binaryBlockCoordinateBranch rg high 1) (mk u S) steps (mk u' O) := by
    obtain ⟨u', hu, he⟩ := binaryCoordinateTranslate_exec body (binaryBlockTranslate rg high)
      (binaryBlockTranslate_injective rg hrg high) L q (if high then b else a) (if high then a else b)
      (hq.trans hn) hbase hresult u S (by simpa [binaryBlockTranslate] using hcoordinate)
      (by cases high <;> simp [binaryBlockTranslate, haInput, hbInput])
      (by cases high <;> simp [binaryBlockTranslate, haInput, hbInput])
      (by intro j hj; rcases hj with rfl | rfl | rfl | rfl <;>
          simpa [binaryBlockTranslate] using hblank _ (by simp))
    exact ⟨u', 18 * L + 18, hu, le_rfl,
      by simpa only [O, hvalue, binaryBlockCoordinateBranch, ite_true,
        show binaryBlockTranslate rg high 4 = rg 5 from by simp [binaryBlockTranslate]] using he⟩
  have hregion (high : Bool) (j : Fin 7) (hj : j = 3 ∨ j = 4 ∨ j = 5) :
      S.R (binaryBlockRegion rg high j) = [] := by
    rcases hj with rfl | rfl | rfl <;> simpa [binaryBlockRegion] using hblank _ (by simp)
  have hbound : 50 * L + 54 = 16 * L + 18 + (34 * L + 36) := by omega
  rw [hbound]
  apply sourceRegionDispatch_exec body (binaryBlockRegion rg false) (binaryBlockRegion_injective rg hrg false)
    _ L q a (a + w) (34 * L + 36) (hq.trans hn) (by omega) (by omega) v S O
    (by simpa [binaryBlockRegion] using hcoordinate)
    (by simpa [binaryBlockRegion] using haInput) (by simpa [binaryBlockRegion] using haEnd) (hregion false)
  intro u
  by_cases hlo : q < a
  · have hv : blockExchange a b w q = q := blockExchange_outside a b w q (by omega) (by omega)
    obtain ⟨u', steps, hu, hm, he⟩ := hcopy hv u
    exact ⟨u', steps, hu, by omega, by simpa [sourceRegionIndex, hlo, binaryBlockCoordinateBranch] using he⟩
  by_cases hleft : q < a + w
  · have hv : blockExchange a b w q = q - a + b := by
      rw [show q = a + (q - a) by omega, blockExchange_left a b w (q - a) hab (by omega)]
      omega
    obtain ⟨u', steps, hu, hm, he⟩ := hmove false (by simpa using Nat.le_of_not_gt hlo) (by simp only [Bool.false_eq_true, ite_false]; rw [← hv]; exact (blockExchange_lt n a b w q hab hb hq).trans hn) (by simpa using hv) u
    exact ⟨u', steps, hu, by omega, by simpa [sourceRegionIndex, hlo, hleft] using he⟩
  · have hc : 34 * L + 36 = 16 * L + 18 + (18 * L + 18) := by omega
    simp only [sourceRegionIndex, ite_eq_right hlo, ite_eq_right hleft, ite_true]
    rw [hc]
    apply sourceRegionDispatch_exec body (binaryBlockRegion rg true) (binaryBlockRegion_injective rg hrg true)
      _ L q b (b + w) (18 * L + 18) (hq.trans hn) (by omega) (by omega) u S O
      (by simpa [binaryBlockRegion] using hcoordinate)
      (by simpa [binaryBlockRegion] using hbInput) (by simpa [binaryBlockRegion] using hbEnd) (hregion true)
    intro u'
    by_cases hgap : q < b
    · have hv : blockExchange a b w q = q := blockExchange_outside a b w q (by omega) (by omega)
      simpa [sourceRegionIndex, hgap, binaryBlockCoordinateBranch] using hcopy hv u'
    by_cases hright : q < b + w
    · have hv : blockExchange a b w q = q - b + a := by
        rw [show q = b + (q - b) by omega, blockExchange_right a b w (q - b) hab (by omega)]
        omega
      simpa [sourceRegionIndex, hgap, hright] using hmove true (by simpa using Nat.le_of_not_gt hgap)
        (by simp only [ite_true]; rw [← hv]; exact (blockExchange_lt n a b w q hab hb hq).trans hn)
        (by simpa using hv) u'
    · have hv : blockExchange a b w q = q := blockExchange_outside a b w q (by omega) (by omega)
      simpa [sourceRegionIndex, hgap, hright, binaryBlockCoordinateBranch] using hcopy hv u'

end IntegerMultBounds.MathlibTM2.Routing
