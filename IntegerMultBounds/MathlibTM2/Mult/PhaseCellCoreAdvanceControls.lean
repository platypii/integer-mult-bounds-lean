module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedOriginAdvanceControls
public import IntegerMultBounds.NLogN.PhaseCellCoreGather

/-! Forward controls for one restoring sweep of fitting core halos. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellMatrix

def coreGatherControls (A s width radius L w : ℕ) : List (Fin (A+4)) :=
  match coreGatherOrigins s width radius L w with
  | [] => []
  | a::as => gatherControls A (a::windowAdvances a as)

theorem originAdvances_coreControls (A s width radius L w : ℕ)
    (hgroup : 0 < (coreGatherIndices s width radius L).length) :
    gatherControls A (originAdvances w 0 (coreGatherOrigins s width radius L 1) ++ [0]) =
      coreGatherControls A s width radius L w := by
  rw [originAdvances_symbols]
  have hmap : (coreGatherOrigins s width radius L 1).map (·*w) =
      coreGatherOrigins s width radius L w := by
    simp only [coreGatherOrigins, List.map_map, Nat.mul_one, Function.comp_def]
  rw [hmap]
  have hn : 0 < (coreGatherOrigins s width radius L w).length := by
    simpa only [coreGatherOrigins, List.length_map] using hgroup
  cases he : coreGatherOrigins s width radius L w with
  | nil => simp [he] at hn
  | cons a as => simp [coreGatherControls, he, originAdvances, originAdvances_window]

theorem coreOriginAdvances_volume (s width radius L w : ℕ) :
    (originAdvances w 0 (coreGatherOrigins s width radius L 1)).sum ≤ s*w := by
  have ho : (0::coreGatherOrigins s width radius L 1).Pairwise (· ≤ ·) :=
    List.pairwise_cons.mpr ⟨by simp, coreGatherOrigins_ordered s width radius L 1⟩
  simpa using originAdvances_sum_le w 0 s (coreGatherOrigins s width radius L 1) ho (by omega)
    (fun origin horigin => by have hh := coreGatherOrigins_fit s width radius L 1 origin horigin; omega)

theorem coreGatherControls_length_le (A s width radius L w : ℕ)
    (hgroup : 0 < (coreGatherIndices s width radius L).length) :
    (coreGatherControls A s width radius L w).length ≤
      s*w+(coreGatherIndices s width radius L).length+1 := by
  rw [←originAdvances_coreControls A s width radius L w hgroup]
  simp only [length_gatherControls,List.sum_append,List.sum_singleton,Nat.add_zero,
    List.length_append,List.length_singleton,originAdvances_length,coreGatherOrigins,List.length_map]
  have hh := coreOriginAdvances_volume s width radius L w
  simpa only [coreGatherOrigins,Nat.add_assoc] using Nat.add_le_add_right hh
    ((coreGatherIndices s width radius L).length+1)

variable {Q A : ℕ} {U P : Type} {body : P → Pr P 117 Q A U}

/-- The binary origins emitted by the core controller suffice to build the
restoring sweep's controls. All registers except the control destination return
exactly to their input contents. -/
theorem preparedCoreAdvanceControls_exec (V w s width radius L : ℕ)
    (hwV : w < 2^V) (hsW : s < 2^V) (hsV : s*w < 2^V)
    (hgroup : 0 < (coreGatherIndices s width radius L).length)
    (v : HS 117 Q A U) (S : Stacks 117 A) (suffix : List (Fin (A+4)))
    (hV : (S.R 115).length = V) (hw : (S.R 94).length = w)
    (hsrc : S.R 109 = (coreGatherIndices s width radius L).flatMap
      (fun k => binSyms V (coreStart width k-radius)) ++ suffix)
    (hcount : S.R 116 = List.replicate (coreGatherIndices s width radius L).length tick)
    (hblank : ∀ k : Fin 117, k.val < 19 → S.R k = [])
    (hfresh : ∀ k ∈ [(88 : Fin 117), 89, 90, 106], S.R k = []) :
    ∃ v' S' n, v'.user = v.user ∧
      n ≤ preparedOriginAdvanceCost V s w (coreGatherIndices s width radius L).length ∧
      Exec body preparedNaturalAdvanceControls (mk v S) n (mk v' S') ∧
      S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧
      S'.R = Function.update S.R 91 (coreGatherControls A s width radius L w ++ S.R 91) := by
  have hle : ∀ origin ∈ coreGatherOrigins s width radius L 1, origin ≤ s := by
    intro origin ho
    have hfit := coreGatherOrigins_fit s width radius L 1 origin ho
    omega
  have hsrc' : S.R 109 = (coreGatherOrigins s width radius L 1).flatMap (binSyms V) ++ suffix := by
    simpa only [coreGatherOrigins, List.flatMap_map, Nat.mul_one] using hsrc
  have h := preparedOriginAdvanceControls_exec (body := body) V w s
    (coreGatherOrigins s width radius L 1)
    hwV hsW hsV (coreGatherOrigins_ordered s width radius L 1) hle
    v S suffix hV hw hsrc'
    (by simpa only [coreGatherOrigins, List.length_map] using hcount) hblank hfresh
  rw [originAdvances_coreControls A s width radius L w hgroup] at h
  simpa only [coreGatherOrigins, List.length_map] using h


end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
