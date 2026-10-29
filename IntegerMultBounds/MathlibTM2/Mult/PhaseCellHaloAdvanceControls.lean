module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedOriginAdvanceControls
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHaloAdvanceSchedule
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellAdvanceBank
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHaloOriginPackets
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellWeightWidth

/-! Generate delimited natural-group advances from its computed binary origin
packets. The small table is constructed from unary width sources and released;
origins, count and all borrowed suffixes are restored. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {U P₀ : Type} {body : P₀ → Pr P₀ 117 Q A U}

def preparedHaloAdvanceCost (V s t band a b L w : ℕ) : ℕ :=
  (32*V+41) + (w*(4*V+10)+6*V+10) +
    ((haloLengthGroup s t band a b L).length*(3*tblC V V+29*V+30)+8*s*w+11) + (38*V+39)

theorem preparedHaloAdvanceControls_bounds_exec (V w s t band a b L : ℕ)
    (hwV : w < 2^V) (hsW : s < 2^V) (hsV : s*w < 2^V)
    (hgroup : 0 < (haloLengthGroup s t band a b L).length)
    (v : HS 117 Q A U) (S : Stacks 117 A) (suffix : List (Fin (A+4)))
    (hV : (S.R 115).length = V) (hw : (S.R 94).length = w)
    (hsrc : S.R 109 = haloOriginPackets A (V) s t band a b L ++ suffix)
    (hcount : S.R 116 = List.replicate (haloLengthGroup s t band a b L).length tick)
    (hblank : ∀ k : Fin 117, k.val < 19 → S.R k = [])
    (hfresh : ∀ k ∈ [(88 : Fin 117), 89, 90, 106], S.R k = []) :
    ∃ v' S' n, v'.user = v.user ∧
      n ≤ preparedHaloAdvanceCost (V) s t band a b L w ∧
      Exec body preparedNaturalAdvanceControls (mk v S) n (mk v' S') ∧
      S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧
      S'.R = Function.update S.R 91 (haloGatherControls A s t band a b L w ++ S.R 91) := by
  have hle : ∀ origin ∈ haloOrigins s t band a b L, origin ≤ s := by
    intro origin ho
    have hfit := haloOrigins_fit s t band a b L origin ho
    omega
  have hsrc' : S.R 109 = (haloOrigins s t band a b L).flatMap (binSyms V) ++ suffix := by
    simpa only [haloOrigins, List.flatMap_map, haloOriginPackets] using hsrc
  simpa only [preparedOriginAdvanceCost, preparedHaloAdvanceCost, haloOrigins_length,
    originAdvances_haloControls A s t band a b L w hgroup] using
    preparedOriginAdvanceControls_exec V w s (haloOrigins s t band a b L)
      hwV hsW hsV (haloOrigins_ordered s t band a b L) hle v S suffix hV hw
      hsrc' (by simpa only [haloOrigins_length] using hcount) hblank hfresh

theorem preparedHaloAdvanceControls_exec (P q w s t u band a b L : ℕ)
    (hst : s ≤ t) (hgroup : 0 < (haloLengthGroup s t band a b L).length)
    (v : HS 117 Q A U) (S : Stacks 117 A) (suffix : List (Fin (A+4)))
    (hV : (S.R 115).length = weightWorkspaceWidth P q w t u) (hw : (S.R 94).length = w)
    (hsrc : S.R 109 = haloOriginPackets A (weightWorkspaceWidth P q w t u) s t band a b L ++ suffix)
    (hcount : S.R 116 = List.replicate (haloLengthGroup s t band a b L).length tick)
    (hblank : ∀ k : Fin 117, k.val < 19 → S.R k = [])
    (hfresh : ∀ k ∈ [(88 : Fin 117), 89, 90, 106], S.R k = []) :
    ∃ v' S' n, v'.user = v.user ∧
      n ≤ preparedHaloAdvanceCost (weightWorkspaceWidth P q w t u) s t band a b L w ∧
      Exec body preparedNaturalAdvanceControls (mk v S) n (mk v' S') ∧
      S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧
      S'.R = Function.update S.R 91 (haloGatherControls A s t band a b L w ++ S.R 91) := by
  have hvolume := weightWorkspaceWidth_symbolVolume P q w s t u hst
  have hsW := (coefficientWorkspaceWidth_bound P (w+q+2) s t u 0 t hst).2.2.1
  exact preparedHaloAdvanceControls_bounds_exec (body := body)
    (weightWorkspaceWidth P q w t u) w s t band a b L hvolume.1 hsW hvolume.2
    hgroup v S suffix hV hw hsrc hcount hblank hfresh

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
