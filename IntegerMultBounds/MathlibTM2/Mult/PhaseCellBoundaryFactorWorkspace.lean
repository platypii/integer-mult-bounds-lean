module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryFactorRuns
public import IntegerMultBounds.MathlibTM2.Host.Embed

/-! A fresh fixed factor bank protects all retained boundary data except its owned source port. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast

def boundaryFactorLegacyReg (i : Fin 154) : Fin 224 := ⟨i.val,by omega⟩

theorem boundaryFactorLegacyReg_injective : Function.Injective boundaryFactorLegacyReg := by
  intro i j h
  apply Fin.ext
  exact congrArg (fun k : Fin 224 => k.val) h

def boundaryFactorReg : RsbR → Fin 224
  | .cm .xs => 154
  | .cm .ys => 155
  | .cm .xsv => 156
  | .cm .ysv => 157
  | .cm .acc => 158
  | .cm .out => 159
  | .cm .wn => 160
  | .cm .pn => 161
  | .cm .nn => 162
  | .cm .tmp => 163
  | .cm .u0 => 164
  | .cm .u1 => 165
  | .cm .u2 => 166
  | .cm .u3 => 167
  | .cm .ma => 168
  | .cm .mb => 169
  | .cm .mc => 170
  | .cm .md => 171
  | .cm .sa => 172
  | .cm .sb => 173
  | .cm .sc => 174
  | .cm .sd => 175
  | .cm .p1 => 176
  | .cm .p2 => 177
  | .cm .p3 => 178
  | .cm .p4 => 179
  | .cm .qr => 180
  | .cm .qi => 181
  | .cm .sr => 182
  | .cm .si => 183
  | .src => 140
  | .dst => 185
  | .msk => 186
  | .ms => 187
  | .mwn => 188
  | .m2wn => 189
  | .m2n => 190
  | .kn => 191
  | .sn => 192
  | .smwn => 193
  | .tswn => 194
  | .ef => 195
  | .df => 196
  | .hf => 197
  | .tK => 198
  | .tL => 199
  | .tJ => 200
  | .tC => 201
  | .tA => 202
  | .sr => 203
  | .sel => 204
  | .hv => 205
  | .vk => 206
  | .b1 => 207
  | .ya => 208
  | .tb => 209
  | .xa => 210
  | .xs => 211
  | .pr => 212
  | .hc => 213
  | .ac => 214
  | .ac2 => 215
  | .nv => 216
  | .dout => 217
  | .bx => 218
  | .bo => 219
  | .dtab => 220
  | .padc => 221
  | .prm => 222

private def boundaryFactorDecode (k : Fin 224) : RsbR :=
  match k.val with
  | 154 => .cm .xs
  | 155 => .cm .ys
  | 156 => .cm .xsv
  | 157 => .cm .ysv
  | 158 => .cm .acc
  | 159 => .cm .out
  | 160 => .cm .wn
  | 161 => .cm .pn
  | 162 => .cm .nn
  | 163 => .cm .tmp
  | 164 => .cm .u0
  | 165 => .cm .u1
  | 166 => .cm .u2
  | 167 => .cm .u3
  | 168 => .cm .ma
  | 169 => .cm .mb
  | 170 => .cm .mc
  | 171 => .cm .md
  | 172 => .cm .sa
  | 173 => .cm .sb
  | 174 => .cm .sc
  | 175 => .cm .sd
  | 176 => .cm .p1
  | 177 => .cm .p2
  | 178 => .cm .p3
  | 179 => .cm .p4
  | 180 => .cm .qr
  | 181 => .cm .qi
  | 182 => .cm .sr
  | 183 => .cm .si
  | 140 => .src
  | 185 => .dst
  | 186 => .msk
  | 187 => .ms
  | 188 => .mwn
  | 189 => .m2wn
  | 190 => .m2n
  | 191 => .kn
  | 192 => .sn
  | 193 => .smwn
  | 194 => .tswn
  | 195 => .ef
  | 196 => .df
  | 197 => .hf
  | 198 => .tK
  | 199 => .tL
  | 200 => .tJ
  | 201 => .tC
  | 202 => .tA
  | 203 => .sr
  | 204 => .sel
  | 205 => .hv
  | 206 => .vk
  | 207 => .b1
  | 208 => .ya
  | 209 => .tb
  | 210 => .xa
  | 211 => .xs
  | 212 => .pr
  | 213 => .hc
  | 214 => .ac
  | 215 => .ac2
  | 216 => .nv
  | 217 => .dout
  | 218 => .bx
  | 219 => .bo
  | 220 => .dtab
  | 221 => .padc
  | 222 => .prm
  | _ => .src

private theorem boundaryFactorDecode_reg (r : RsbR) : boundaryFactorDecode (boundaryFactorReg r) = r := by
  cases r with
  | cm c => cases c <;> rfl
  | src => rfl
  | dst => rfl
  | msk => rfl
  | ms => rfl
  | mwn => rfl
  | m2wn => rfl
  | m2n => rfl
  | kn => rfl
  | sn => rfl
  | smwn => rfl
  | tswn => rfl
  | ef => rfl
  | df => rfl
  | hf => rfl
  | tK => rfl
  | tL => rfl
  | tJ => rfl
  | tC => rfl
  | tA => rfl
  | sr => rfl
  | sel => rfl
  | hv => rfl
  | vk => rfl
  | b1 => rfl
  | ya => rfl
  | tb => rfl
  | xa => rfl
  | xs => rfl
  | pr => rfl
  | hc => rfl
  | ac => rfl
  | ac2 => rfl
  | nv => rfl
  | dout => rfl
  | bx => rfl
  | bo => rfl
  | dtab => rfl
  | padc => rfl
  | prm => rfl

theorem boundaryFactorReg_injective : Function.Injective boundaryFactorReg :=
  Function.LeftInverse.injective boundaryFactorDecode_reg

def boundaryFactorMulReg (i : Fin 64) : Fin 224 := ⟨i.val,by omega⟩

theorem boundaryFactorMulReg_injective : Function.Injective boundaryFactorMulReg := by
  intro i j h
  apply Fin.ext
  exact congrArg (fun k : Fin 224 => k.val) h

theorem boundaryFactorReg_range (r : RsbR) :
    boundaryFactorReg r = 140 ∨ 154 ≤ (boundaryFactorReg r).val := by
  cases r with
  | cm c => cases c <;> decide
  | src => decide
  | dst => decide
  | msk => decide
  | ms => decide
  | mwn => decide
  | m2wn => decide
  | m2n => decide
  | kn => decide
  | sn => decide
  | smwn => decide
  | tswn => decide
  | ef => decide
  | df => decide
  | hf => decide
  | tK => decide
  | tL => decide
  | tJ => decide
  | tC => decide
  | tA => decide
  | sr => decide
  | sel => decide
  | hv => decide
  | vk => decide
  | b1 => decide
  | ya => decide
  | tb => decide
  | xa => decide
  | xs => decide
  | pr => decide
  | hc => decide
  | ac => decide
  | ac2 => decide
  | nv => decide
  | dout => decide
  | bx => decide
  | bo => decide
  | dtab => decide
  | padc => decide
  | prm => decide

/-- Every owned factor-bank tape is a register image or one of the two private tapes. -/
theorem boundaryFactorReg_cover (i : Fin 224) (hi : 154 ≤ i.val) (h184 : i ≠ 184) (h223 : i ≠ 223) :
    ∃ r, boundaryFactorReg r = i := by
  refine ⟨boundaryFactorDecode i,?_⟩
  fin_cases i <;> first | (simp_all; done) | rfl

theorem boundaryFactorReg_disjoint (r : RsbR) (i : Fin 64) : boundaryFactorReg r ≠ boundaryFactorMulReg i := by
  intro h
  have hi := i.isLt
  have hh := congrArg Fin.val h
  change (boundaryFactorReg r).val = i.val at hh
  rcases boundaryFactorReg_range r with hr | hr
  · rw [hr] at hh; norm_num at hh; omega
  · omega

theorem boundaryFactorReg_private (r : RsbR) :
    boundaryFactorReg r ≠ 184 ∧ boundaryFactorReg r ≠ 223 := by
  cases r <;> first | decide | (rename_i c; cases c <;> decide)

theorem boundaryFactorReg_off (r : RsbR) (i : Fin 154) (hi : i ≠ 140) :
    boundaryFactorReg r ≠ boundaryFactorLegacyReg i := by
  intro h
  have hh := congrArg Fin.val h
  change (boundaryFactorReg r).val = i.val at hh
  rcases boundaryFactorReg_range r with hr | hr
  · rw [hr] at hh
    exact hi (Fin.ext hh.symm)
  · have := i.isLt; omega

def boundaryFactorState {A : ℕ} (S : Stacks 224 A) : RsbR → List (Fin (A+4)) :=
  fun r => S.R (boundaryFactorReg r)

theorem boundaryFactorFr_legacy {A : ℕ} {S S' : Stacks 224 A}
    (h : RsbFr boundaryFactorReg S S') :
    S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧
      ∀ i : Fin 154, i ≠ 140 → S'.R (boundaryFactorLegacyReg i) = S.R (boundaryFactorLegacyReg i) := by
  exact ⟨h.1,h.2.1,h.2.2.1,fun i hi => h.2.2.2 _ (fun r => boundaryFactorReg_off r i hi)⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
