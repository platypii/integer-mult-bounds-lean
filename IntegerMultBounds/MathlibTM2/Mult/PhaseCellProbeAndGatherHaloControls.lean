module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGenerateHaloGatherControls
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellProbePreparedHaloOrigins
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeometryHaloGatherCost

/-! Runtime selection after one origin scan. Empty classes release the width
headers; nonempty classes continue from the same retained origins and count. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

-- The coefficient-width controller can be restored from commit `3aae59ce`.
def probeAndGatherHaloControls : Pr P₀ 117 Q A U := probeGeometryHaloGather

def probedHaloGatherR (A P q s t u band a b L : ℕ) (R : Fin 117 → List (Fin (A+4))) :=
  if 0 < (haloLengthGroup s t band a b L).length then
    haloOriginAndGatherControlsR A (weightWorkspaceWidth P q (2*q+8) t u) s t band a b L (2*q+8) R else R

def probeAndGatherHaloControlsCost (P q s t u band a b L : ℕ) : ℕ :=
  probeGeometryHaloGatherCost P q s t u band a b L

theorem probeAndGatherHaloControls_exec (P q s t u band a b L : ℕ)
    (hP : 13 ≤ P) (hs : 0 < s) (hst : s < t) (hu : 1 ≤ u)
    (hband : band ≤ s) (has : a ≤ s) (hbs : b ≤ s) (hL : 0 < L) (hLs : L ≤ s) (hA : 4 ≤ A)
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hPSrc : (S.R 114).length = P) (hq : (S.R 112).length = q)
    (hsSrc : (S.R 97).length = s) (htSrc : (S.R 98).length = t)
    (huSrc : (S.R 99).length = u) (hbSrc : (S.R 100).length = band)
    (haSrc : (S.R 111).length = a) (hbEndSrc : (S.R 113).length = b) (hLSrc : (S.R 102).length = L)
    (hblank : ∀ k : Fin 117, k.val < 31 → S.R k = [])
    (hfresh : ∀ k ∈ [(94 : Fin 117), 104, 106, 115, 116, 88, 89, 90], S.R k = []) :
    ∃ v' m, v'.user = v.user ∧ v'.flag = decide (0 < (haloLengthGroup s t band a b L).length) ∧ m ≤ probeAndGatherHaloControlsCost P q s t u band a b L ∧
      Exec body probeAndGatherHaloControls (mk v S) m
        (mk v' { S with R := probedHaloGatherR A P q s t u band a b L S.R }) := by
  simpa only [probeAndGatherHaloControls,probeAndGatherHaloControlsCost,probedHaloGatherR,probedGeometryHaloGatherR] using
    probeGeometryHaloGather_exec (body := body) P q s t u band a b L
      hs hst hband has hbs hL hLs hA v S hPSrc hq hsSrc htSrc huSrc hbSrc haSrc hbEndSrc hLSrc hblank hfresh

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
