module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedLocalRowSelection
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicRowSelection

/-! Local nearest-row selection from ordinary retained scalar headers and an
owned target window. No table, origin queue or sweep controller is supplied. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellRationalArgs
variable {Q A s : ℕ} [NeZero s] {P U : Type} {body : P → Pr P 117 Q A U}

theorem preparedCyclicLocalRowSelection_exec {W V t a origin span w n : ℕ}
    (hn : 0 < n)
    (hwide : a+n+2*t*(a+n)+3*s < 2^W)
    (hwindow : ∀ j < n, origin ≤ nearestNatural s t (a+j) ∧ nearestNatural s t (a+j) < origin+span)
    (hwV : w < 2^V) (hspan : span < 2^V) (hvol : span*w < 2^V)
    (hVW : V ≤ W) (hA : 4 ≤ A) (hVpos : 0 < V)
    (F : ZMod t → GaussianInt) (v : HS 117 Q A U) (S : Stacks 117 A)
    (hW : (S.R 114).length = W) (hV : (S.R 115).length = V)
    (hs : S.R 32 = binSyms W s) (ht : S.R 33 = binSyms W t)
    (ha : S.R 34 = binSyms W a) (ho : S.R 35 = binSyms W origin)
    (hc : S.R 36 = binSyms W n) (hz : S.R 37 = [])
    (hblank : ∀ k : Fin 117, k.val < 31 → S.R k = [])
    (hw : (S.R 94).length = w) (h104 : S.R 104 = []) (h106 : S.R 106 = []) (h116 : S.R 116 = [])
    (hfresh : ∀ k ∈ [(88 : Fin 117),89,90], S.R k = [])
    (hsrc : S.R 110 = cstream A w (cyclicInterval origin span F))
    (hrow : (S.R 103).length = 1) (hcontrol : S.R 91 = [])
    (hclean : ∀ k ∈ [(92 : Fin 117),93,95,96,97,98,99,100,101,102], S.R k = []) :
    ∃ v' B m, v'.user = v.user ∧
      m ≤ (110*W+4*V+137)+(localRowControlsCost W V span w n+n*(14*w+25)+12*(span*w)+6*w+38) ∧
      Exec body preparedLocalRowSelection (mk v S) m (mk v' B) ∧
      B.inp = S.inp ∧ B.out = S.out ∧ B.L = S.L ∧
      B.R 108 = cstream A w (cyclicInterval a n (fun j => F (rowIndex s t j)))++S.R 108 ∧
      B.R 91 = localRowControls A s t a n origin w ∧
      B.R 109 = (localRowOrigins s t a n origin 1).flatMap (binSyms V)++S.R 109 ∧
      B.R 116 = List.replicate n tick ∧
      ∀ k, k ≠ 108 → k ≠ 91 → k ≠ 109 → k ≠ 116 → B.R k = S.R k := by
  exact preparedLocalRowSelection_exec_of_payload hn hwide hwindow hwV hspan hvol hVW hA hVpos
    (cstream A w (cyclicInterval origin span F))
    (cstream A w (cyclicInterval a n (fun j => F (rowIndex s t j))))
    (by rw [length_cstream,cyclicInterval_length])
    (cyclicRowOrigins_payload A w a n origin span F hwindow)
    v S hW hV hs ht ha ho hc hz hblank hw h104 h106 h116 hfresh hsrc hrow hcontrol hclean

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
