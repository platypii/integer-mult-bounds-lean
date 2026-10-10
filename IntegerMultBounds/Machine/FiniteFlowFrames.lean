import IntegerMultBounds.Machine.FiniteFlowPath

/-! Literal frame preservation for complete cyclic controller paths. Enlarging
or relabeling the fixed bank retains every original state-dependent edge and
all transition counts, including recursive-call and return joins. -/
namespace IntegerMultBounds.Machine.FiniteFlowFrames
noncomputable section
open FiniteFlow FiniteFlowPath
variable {N t a s u : ℕ} {states : Fin N → ℕ}
variable {family : ∀ pc,Program t (states pc) a} {next : Next states}

theorem path_extend {pc last : Fin N} {v w : Tapes t a} {n : ℕ}
    (h : Path family next pc v n last w) (extra : Tapes s a) :
    Path (fun i => extend (family i) s) next pc (v.append extra) n last (w.append extra) := by
  induction h with
  | nil pc v => exact Path.nil _ _
  | join pc pc' last v w n m c hr hh he tail ih =>
    exact Path.join pc pc' last (v.append extra) (w.append extra) n m (c.extend extra)
      (extend_run (family pc) extra hr) (extend_halt (family pc) extra hh) he ih

theorem path_reindex {pc last : Fin N} {v w : Tapes t a} {n : ℕ}
    (h : Path family next pc v n last w) (e : Fin t ≃ Fin u) :
    Path (fun i => reindex (family i) e) next pc (v.reindex e) n last (w.reindex e) := by
  induction h with
  | nil pc v => exact Path.nil _ _
  | join pc pc' last v w n m c hr hh he tail ih =>
    exact Path.join pc pc' last (v.reindex e) (w.reindex e) n m (c.reindex e)
      (reindex_run (family pc) e hr) (reindex_halt (family pc) e hh) he ih

theorem trace_extend {pc last : Fin N} {v : Tapes t a} {n : ℕ}
    {c : Config t (states last) a} (h : Trace family next pc v n last c)
    (extra : Tapes s a) :
    Trace (fun i => extend (family i) s) next pc (v.append extra) n last (c.extend extra) := by
  induction h with
  | stop pc v n c hr hh he =>
    exact Trace.stop pc (v.append extra) n (c.extend extra)
      (extend_run (family pc) extra hr) (extend_halt (family pc) extra hh) he
  | join pc pc' last v n m d c hr hh he tail ih =>
    exact Trace.join pc pc' last (v.append extra) n m (d.extend extra) (c.extend extra)
      (extend_run (family pc) extra hr) (extend_halt (family pc) extra hh) he ih

theorem trace_reindex {pc last : Fin N} {v : Tapes t a} {n : ℕ}
    {c : Config t (states last) a} (h : Trace family next pc v n last c)
    (e : Fin t ≃ Fin u) :
    Trace (fun i => reindex (family i) e) next pc (v.reindex e) n last (c.reindex e) := by
  induction h with
  | stop pc v n c hr hh he =>
    exact Trace.stop pc (v.reindex e) n (c.reindex e)
      (reindex_run (family pc) e hr) (reindex_halt (family pc) e hh) he
  | join pc pc' last v n m d c hr hh he tail ih =>
    exact Trace.join pc pc' last (v.reindex e) n m (d.reindex e) (c.reindex e)
      (reindex_run (family pc) e hr) (reindex_halt (family pc) e hh) he ih

end
end IntegerMultBounds.Machine.FiniteFlowFrames
