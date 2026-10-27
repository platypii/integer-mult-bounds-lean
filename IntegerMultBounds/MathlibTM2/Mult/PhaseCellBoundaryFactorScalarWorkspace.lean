module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryFactorWorkspace
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellScalarPrepare

/-! Reuse the proved scalar counter generator in the fresh factor bank. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast

def boundaryFactorScalarIndex (n : ℕ) : ℕ :=
  match n with
  | 84 => 154
  | 85 => 155
  | 86 => 156
  | 87 => 157
  | 88 => 158
  | 89 => 159
  | 90 => 160
  | 91 => 161
  | 92 => 162
  | 95 => 163
  | 64 => 164
  | 65 => 165
  | 66 => 166
  | 67 => 167
  | 68 => 168
  | 69 => 169
  | 70 => 170
  | 71 => 171
  | 72 => 172
  | 73 => 173
  | 74 => 174
  | 75 => 175
  | 76 => 176
  | 77 => 177
  | 78 => 178
  | 79 => 179
  | 80 => 180
  | 81 => 181
  | 82 => 182
  | 83 => 183
  | 94 => 223
  | 100 => 119
  | _ => n

def boundaryFactorScalarReg (i : Fin 117) : Fin 224 :=
  ⟨boundaryFactorScalarIndex i.val,by unfold boundaryFactorScalarIndex; split <;> omega⟩

private def factorScalarDecode (k : Fin 224) : Fin 117 :=
  match k.val with
  | 154 => 84
  | 155 => 85
  | 156 => 86
  | 157 => 87
  | 158 => 88
  | 159 => 89
  | 160 => 90
  | 161 => 91
  | 162 => 92
  | 163 => 95
  | 164 => 64
  | 165 => 65
  | 166 => 66
  | 167 => 67
  | 168 => 68
  | 169 => 69
  | 170 => 70
  | 171 => 71
  | 172 => 72
  | 173 => 73
  | 174 => 74
  | 175 => 75
  | 176 => 76
  | 177 => 77
  | 178 => 78
  | 179 => 79
  | 180 => 80
  | 181 => 81
  | 182 => 82
  | 183 => 83
  | 223 => 94
  | 119 => 100
  | _ => Fin.ofNat 117 k.val

private theorem factorScalarDecode_reg (i : Fin 117) :
    factorScalarDecode (boundaryFactorScalarReg i) = i := by
  fin_cases i <;> rfl

theorem boundaryFactorScalarReg_injective : Function.Injective boundaryFactorScalarReg :=
  Function.LeftInverse.injective factorScalarDecode_reg

theorem boundaryFactorScalarReg_cm (r : CR) :
    boundaryFactorScalarReg (ScalarPlacement.cr r) = boundaryFactorReg (.cm r) := by
  cases r <;> rfl

theorem boundaryFactorScalarReg_low (i : Fin 117) (hi : i.val < 26) :
    (boundaryFactorScalarReg i).val = i.val := by
  fin_cases i <;> first | rfl | (simp at hi)

theorem boundaryFactorScalarReg_width : boundaryFactorScalarReg 94 = 223 := rfl

theorem boundaryFactorScalarReg_precision : boundaryFactorScalarReg 100 = 119 := rfl

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
