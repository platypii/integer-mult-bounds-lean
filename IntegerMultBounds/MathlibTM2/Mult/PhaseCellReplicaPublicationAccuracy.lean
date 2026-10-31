module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaPublicationData
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellWindowPublicationAccuracy

/-! Numerical certificates refer to the same concatenated bytes returned by
the replica executor. Following lines and the borrowed suffix cannot affect a
reader inside the selected line. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

theorem fixedLines_word {α : Type} (W w : ℕ) (lines : List (List α))
    (hlen : ∀ line ∈ lines, line.length = W) (tail : List α)
    (j offset : ℕ) (hj : j < lines.length) (hoffset : offset+w ≤ W) :
    (((lines.flatten++tail).drop (j*W)).drop offset).take w =
      (lines[j].drop offset).take w := by
  have hline := hlen _ (List.getElem_mem hj)
  have hprefix : j*W ≤ lines.flatten.length := by
    rw [length_flatten_const lines hlen]
    exact Nat.mul_le_mul_right W hj.le
  rw [List.drop_append_of_le_length hprefix,archiveRows_flatten_drop W j lines hlen,
    List.drop_eq_getElem_cons hj,List.flatten_cons,List.append_assoc,
    List.drop_append_of_le_length (by omega),List.take_append_of_le_length]
  simp only [List.length_drop,hline]
  omega

theorem replicaPublication_errorOn {A s L : ℕ} [NeZero s]
    (windows : PublicationWindows s L) (q w missing : ℕ)
    (replicas : List (PublicationReplica A))
    (hvalid : ∀ r ∈ replicas, r.Valid windows w missing)
    (tail raw : List (Fin (A+4)))
    (hraw : raw = replicas.flatMap (PublicationReplica.output windows w)++tail)
    (j : ℕ) (hj : j < replicas.length) (n : ℕ) (hn : n < windows.origins.length)
    (x : ZMod s → ℂ) (error : ℝ)
    (hgood : PhaseCellInterface.ErrorOn
      (haloVertices s windows.origins[n] (windows.origins[n]+L))
      (packedIntervalRead q w windows.origins[n]
        (cstream A w (replicas[j].rows[n]'(by
          rw [(hvalid _ (List.getElem_mem hj)).rowCount]; exact hn)))) x error) :
    PhaseCellInterface.ErrorOn (haloVertices s windows.origins[n] (windows.origins[n]+L))
      (pairedCellRead q w (raw.drop (j*(s*w)))) x error := by
  have hr := hvalid _ (List.getElem_mem hj)
  have he := windowPublication_errorOn windows q w replicas[j].rows hr.rowCount hr.rowLength
    replicas[j].ambient (by rw [hr.ambientLength]) x error n hn hgood
  let lines := replicas.map (PublicationReplica.output windows w)
  have hlength : ∀ line ∈ lines, line.length = s*w := by
    intro line hline
    obtain ⟨r,hrmem,he⟩ := List.mem_map.mp hline
    subst line
    exact (hvalid r hrmem).output_length
  intro i hi
  have hword := fixedLines_word (s*w) w lines hlength tail j (i.val*w)
    (by simpa [lines] using hj) (by
      have hm := Nat.mul_le_mul_right w (Nat.succ_le_of_lt i.val_lt)
      simpa only [Nat.succ_mul] using hm)
  have hg := he i hi
  rw [hraw]
  change ‖value q (decodeWord ((((lines.flatten++tail).drop (j*(s*w))).drop (i.val*w)).take w))-x i‖ ≤ error
  rw [hword]
  simpa only [lines,List.getElem_map,PublicationReplica.output,PublicationReplica.words,pairedCellRead] using hg

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
