module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpBankFamily
public import IntegerMultBounds.MathlibTM2.Mult.ChirpForwardCallerParameters

/-! # The five forward consumer banks and their exact source assignments -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds.MathlibTM2.Fast.TableVM

namespace ForwardParameters

def gather : Fin 10 → Fin 16 := ![14, 15, 5, 11, 13, 13, 13, 13, 13, 13]
def convolution : Fin 10 → Fin 16 := ![10, 15, 5, 11, 8, 13, 13, 13, 13, 13]
def multiplier : Fin 5 → Fin 16 := ![10, 11, 13, 13, 13]
def coefficient (i : Fin 48) : Fin 16 :=
  if i = 19 then 10 else if i = 34 then 14 else if i = 35 then 15 else
  if i = 36 then 1 else if i = 43 then 7 else if i = 45 then 5 else if i = 46 then 9 else 13

end ForwardParameters

/-- One installation list scopes all dimension and coefficient banks once. -/
def chirpForwardConsumers {T : ℕ} (gather convolution : TblR 10 → Fin T)
    (output : TblR 14 → Fin T) (coefficient : TblR 48 → Fin T) (multiplier : TblR 5 → Fin T) :
    List (ChirpBankTarget 16 T) :=
  [⟨10, gather, ForwardParameters.gather⟩, ⟨10, convolution, ForwardParameters.convolution⟩,
    ⟨14, output, ForwardParameters.output⟩, ⟨48, coefficient, ForwardParameters.coefficient⟩,
    ⟨5, multiplier, ForwardParameters.multiplier⟩]

/-- Assignments for window gathering include exactly six initially zero workspace words. -/
theorem chirpForwardGather_values (v : Fin 16 → ℕ) :
    (fun i => v (ForwardParameters.gather i)) = ![v 14, v 15, v 5, v 11, v 13, v 13, v 13, v 13, v 13, v 13] := by
  funext i
  fin_cases i <;> rfl

/-- Assignments for S1 include its ring logarithm and five zero workspace words. -/
theorem chirpForwardConvolution_values (v : Fin 16 → ℕ) :
    (fun i => v (ForwardParameters.convolution i)) = ![v 10, v 15, v 5, v 11, v 8, v 13, v 13, v 13, v 13, v 13] := by
  funext i
  fin_cases i <;> rfl

/-- The coefficient evaluator receives the generated block count as well as E's growth bound. -/
theorem chirpForwardCoefficient_values (v : Fin 16 → ℕ) (i : Fin 48) :
    v (ForwardParameters.coefficient i) =
      if i = 19 then v 10 else if i = 34 then v 14 else if i = 35 then v 15 else
      if i = 36 then v 1 else if i = 43 then v 7 else if i = 45 then v 5 else if i = 46 then v 9 else v 13 := by
  unfold ForwardParameters.coefficient
  split_ifs <;> rfl

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
