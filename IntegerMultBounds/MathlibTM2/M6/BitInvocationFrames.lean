module

public import IntegerMultBounds.MathlibTM2.M6.BitInvocation

/-!
# The class runs in global frames

A class run of an invocation, on arbitrary dirty roles, in the parent's coordinates:
* `invoke_side_zero`: side zero of the active pair changes from `sourceFrame n` to
  `sourceFrame (n + 1)`, and in the reflected call also receives side one;
* `invoke_side_one`: side one changes from `targetFrame n` to `targetFrame (n + 1)`, and in the
  forward call also receives side zero;
* `invoke_host`: the role hosting a helper changes by the exchange on the helper's slot.

These combine `Invocation`'s window endpoints with the stage routes (`Stage`, `Charts`) and the
helper charts.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M6.BitNode

open IntegerMultBounds.Networks.Certificates.PR589
open IntegerMultBounds.Networks.Certificates.PR589.Nine
open IntegerMultBounds.MathlibTM2.M6.BitHosting
open Matrix

variable (n : Fin 9) (r : Fin 32) (d : Fin 5) (X : State)

/-- The source frame of port `t` after `k` stages. -/
noncomputable def sF (t : ℕ) (k : ℕ) : Matrix Axis Axis ℚ := (port t).sourceFrame k

/-- The target frame of port `t` after `k` stages. -/
noncomputable def tF (t : ℕ) (k : ℕ) : Matrix Axis Axis ℚ := (port t).targetFrame k

theorem chart_port (t : Fin 111) : chart n t.val = (port t.val).stageRoute n ∧
    chart n (111 + t.val) = (port t.val).stageRoute n := by
  refine ⟨?_, ?_⟩
  · rw [chart_data n t.val (by omega), Nat.mod_eq_of_lt t.isLt]
  · rw [chart_data n (111 + t.val) (by omega), show (111 + t.val) % 111 = t.val by omega]

/-- Reading a data register through its route, changing window frames, and writing back. -/
theorem data_frames (t : Fin 111) (U V : Matrix (Fin 8) (Fin 8) ℚ) (f : Stream) :
    along (bar ((port t.val).stageRoute n)ᵀ)
        (along (exchange (windowProj n U) * exchange (windowProj n V))
          (along (bar ((port t.val).stageRoute n)) f)) =
      along (exchange ((port t.val).stageLift n U) * exchange ((port t.val).stageLift n V)) f := by
  rw [PortCertificate.stageRoute_transpose, along_route _
    (PortCertificate.stageRoute_mul_self (port_checked t.val t.isLt) n),
    PortCertificate.stageLift_eq, PortCertificate.stageLift_eq]

theorem registers_data (j : ℕ) (hj : j < 661) :
    registers n r d X j = along (bar (chart n j)) (X (owner n r d j)) := by
  simp [registers, hj]

theorem lift_frames (t : Fin 111) :
    (port t.val).stageLift n (port t.val).lineProj = sF t.val n.val ∧
      (port t.val).stageLift n 1 = sF t.val (n.val + 1) ∧
      (port t.val).stageLift n 0 = tF t.val n.val ∧
      (port t.val).stageLift n (1 - (port t.val).lineProj) = tF t.val (n.val + 1) := by
  have hc := port_checked t.val t.isLt
  exact ⟨PortCertificate.stage_source hc n, PortCertificate.stage_source_exit hc n,
    PortCertificate.stage_target hc n, PortCertificate.stage_target_exit hc n⟩

/-- Side zero of the active pair in a class run. -/
theorem invoke_side_zero (t : Fin 111) :
    invoke n r d X (sideRole n r d 0 t) =
      along (exchange (sF t.val n.val) * exchange (sF t.val (n.val + 1))) (X (sideRole n r d 0 t)) +
        (if n.val % 2 = 1 then
          along (exchange (tF t.val n.val) * exchange (sF t.val (n.val + 1))) (X (sideRole n r d 1 t))
        else 0) := by
  have hz := registers_high n r d X
  obtain ⟨hc1, hc2⟩ := chart_port n t
  obtain ⟨hl1, hl2, hl3, hl4⟩ := lift_frames n t
  by_cases hrev : n.val % 2 = 1
  · have ho : sideRole n r d 0 t = owner n r d (111 + t.val) := by
      rw [owner_target]; congr 1; omega
    have ho' : sideRole n r d 1 t = owner n r d t.val := by
      rw [owner_source, hrev]
    rw [if_pos hrev, ho, ho', invoke_owner n r d X _ (by omega), runWord, if_pos hrev,
      reverse_target n _ t.val t.isLt, map_add, registers_data n r d X _ (by omega),
      registers_data n r d X _ (by omega), hc1, hc2, data_frames, data_frames, hl1, hl2, hl3]
  · have ho : sideRole n r d 0 t = owner n r d t.val := by
      rw [owner_source]; congr 1; omega
    rw [if_neg hrev, add_zero, ho, invoke_owner n r d X _ (by omega), runWord, if_neg hrev,
      forward_source n _ hz t.val t.isLt, registers_data n r d X _ (by omega), hc1, data_frames,
      hl1, hl2]

/-- Side one of the active pair in a class run. -/
theorem invoke_side_one (t : Fin 111) :
    invoke n r d X (sideRole n r d 1 t) =
      along (exchange (tF t.val n.val) * exchange (tF t.val (n.val + 1))) (X (sideRole n r d 1 t)) +
        (if n.val % 2 = 1 then 0 else
          along (exchange (sF t.val n.val) * exchange (tF t.val (n.val + 1))) (X (sideRole n r d 0 t))) := by
  have hz := registers_high n r d X
  obtain ⟨hc1, hc2⟩ := chart_port n t
  obtain ⟨hl1, hl2, hl3, hl4⟩ := lift_frames n t
  by_cases hrev : n.val % 2 = 1
  · have ho : sideRole n r d 1 t = owner n r d t.val := by
      rw [owner_source, hrev]
    rw [if_pos hrev, add_zero, ho, invoke_owner n r d X _ (by omega), runWord, if_pos hrev,
      reverse_source n _ t.val t.isLt, registers_data n r d X _ (by omega), hc1, data_frames,
      hl3, hl4]
  · have ho : sideRole n r d 1 t = owner n r d (111 + t.val) := by
      rw [owner_target]; congr 1; omega
    have ho' : sideRole n r d 0 t = owner n r d t.val := by
      rw [owner_source]; congr 1; omega
    rw [if_neg hrev, ho, ho', invoke_owner n r d X _ (by omega), runWord, if_neg hrev,
      forward_target n _ hz t.val t.isLt, map_add, registers_data n r d X _ (by omega),
      registers_data n r d X _ (by omega), hc1, hc2, data_frames, data_frames, hl1, hl3, hl4]

/-- The full local exchange, in window frames. -/
theorem window_helper_change :
    exchange (windowProj n 0) * exchange (windowProj n 1) =
      exchange (fromBlocks (1 : Matrix (Fin 8) (Fin 8) ℚ) 0 0 0) := by
  rw [exchange_change (windowProj_mul_self n (Matrix.mul_zero 0))]
  · congr 1
    simp only [windowProj]
    ext (i | i) (j | j) <;> simp
  · simp [windowProj, fromBlocks_multiply, lower_mul_self]

/-- The role hosting helper `h` changes by the exchange on the helper's slot. -/
theorem invoke_host (h : ℕ) (hh : h < 439) :
    invoke n r d X (hostRole n r d h) =
      along (exchange ((port ((slotOf n h).copy % 111)).span (slotPos (slotOf n h))
        (slotPos (slotOf n h) + 8))) (X (hostRole n r d h)) := by
  have hz := registers_high n r d X
  have hx := slotPos_le n.val n.isLt h hh
  have ho : hostRole n r d h = owner n r d (222 + h) := by
    simp [owner, show (222 + h) - 222 = h by omega]
  have hchart : chart n (222 + h) =
      (port ((slotOf n h).copy % 111)).helperChart (slotPos (slotOf n h)) hx := by
    simp only [chart, show ¬222 + h < 222 by omega, ite_false]
    generalize hk : 222 + h - 222 = k
    obtain rfl : k = h := by omega
    rw [dif_pos hx]
  have hword : runWord n (registers n r d X) (222 + h) =
      along (exchange (windowProj n 0) * exchange (windowProj n 1)) (registers n r d X (222 + h)) := by
    rw [runWord_forward n _ hz,forward_helper n _ hz h hh]
  have hc := port_checked ((slotOf n h).copy % 111) (Nat.mod_lt _ (by norm_num))
  rw [ho, invoke_owner n r d X _ (by omega), hword, registers_data n r d X _ (by omega), hchart,
    window_helper_change, along_chart _ (PortCertificate.helperChart_mul_transpose hc _ hx),
    PortCertificate.helperChart_slot]

end IntegerMultBounds.MathlibTM2.M6.BitNode
