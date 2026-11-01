module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpUnaryCopies
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellScalarPlacement

/-! Count actual symbols on an arbitrary owned register list. Updates and
header-copy schedules are bounded structurally, independently of bank size. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds.MathlibTM2.Node IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv

theorem sum_wordLengths_update_le {ι Γ : Type} [DecidableEq ι]
    (rs : List ι) (hnd : rs.Nodup) (R : ι → List Γ) (k : ι) (words : List Γ) (d : ℕ)
    (hlen : words.length ≤ (R k).length+d) :
    (rs.map (fun i => (Function.update R k words i).length)).sum ≤
      (rs.map (fun i => (R i).length)).sum+d := by
  induction rs with
  | nil => simp
  | cons i rs ih =>
    obtain ⟨hnot,hnd⟩ := List.nodup_cons.mp hnd
    by_cases hi : i = k
    · subst i
      have htail : rs.map (fun i => (Function.update R k words i).length) = rs.map (fun i => (R i).length) := by
        apply List.map_congr_left
        intro i hi
        have hn : i ≠ k := by intro he; subst i; exact hnot hi
        rw [Function.update_of_ne hn]
      simp only [List.map_cons,List.sum_cons,Function.update_self,htail]
      omega
    · have hh := ih hnd
      simp only [List.map_cons,List.sum_cons,Function.update_of_ne hi]
      omega

theorem sum_wordLengths_unaryCopies_le {T A n : ℕ} (rs : List (Fin T)) (hnd : rs.Nodup)
    (σ : Fin n → ℕ) (copies : List (Fin n × Fin T)) (R : Regs T A) :
    (rs.map (fun k => (unaryCopiesR σ R copies k).length)).sum ≤
      (rs.map (fun k => (R k).length)).sum+(copies.map (fun r => σ r.1)).sum := by
  induction copies generalizing R with
  | nil => simp [unaryCopiesR]
  | cons r copies ih =>
    have hs := sum_wordLengths_update_le rs hnd R r.2 (List.replicate (σ r.1) Node.tick++R r.2) (σ r.1)
      (by simp; omega)
    have hh := ih (Function.update R r.2 (List.replicate (σ r.1) Node.tick++R r.2))
    simp only [unaryCopiesR,List.map_cons,List.sum_cons]
    omega

theorem sum_wordLengths_counterR_le {A : ℕ} (rs : List (Fin 117)) (hnd : rs.Nodup)
    (q w : ℕ) (R : Regs 117 A) :
    (rs.map (fun k => (counterR q w R k).length)).sum ≤
      (rs.map (fun k => (R k).length)).sum+w+q+Schoenhage.Schedule.topN w := by
  have h₁ := sum_wordLengths_update_le rs hnd R (cr .wn) (List.replicate w Node.tick) w (by simp)
  have h₂ := sum_wordLengths_update_le rs hnd (Function.update R (cr .wn) (List.replicate w Node.tick))
    (cr .pn) (List.replicate q Node.tick) q (by simp)
  have h₃ := sum_wordLengths_update_le rs hnd
    (Function.update (Function.update R (cr .wn) (List.replicate w Node.tick)) (cr .pn) (List.replicate q Node.tick))
    (cr .nn) (List.replicate (Schoenhage.Schedule.topN w) Node.tick) (Schoenhage.Schedule.topN w) (by simp)
  unfold counterR
  omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
