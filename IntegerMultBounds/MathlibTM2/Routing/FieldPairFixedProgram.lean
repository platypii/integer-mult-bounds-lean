module

public import IntegerMultBounds.MathlibTM2.Routing.BinaryFieldPair

/-! Widths and values annotate field-generation proofs; code uses fixed registers.
Zero annotations select a canonical presentation of that same program. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.MathlibTM2.Host
variable {N Q A : ℕ} {P U : Type}

def fieldPairFixedProgram (row mask : Fin N) : Pr P (N + 6) Q A U :=
  binaryFieldBatch (fieldPairJobs row mask 0 0 0 0)

theorem fieldPairJobs_program (row mask : Fin N) (Lr Lm nr nm : ℕ) :
    (binaryFieldBatch (fieldPairJobs row mask Lr Lm nr nm) : Pr P (N + 6) Q A U) =
      fieldPairFixedProgram row mask := rfl

end IntegerMultBounds.MathlibTM2.Routing
