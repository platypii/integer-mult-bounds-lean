module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryFoldExecution
public import IntegerMultBounds.MathlibTM2.Mult.ChirpOutputRoleCode

/-! Place the existing fold in the retained bank without disturbing its spectator streams. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.BoundaryFoldPlacement

open IntegerMultBounds.MathlibTM2.Fast

def code : RsbR → Fin 69
  | .cm c => ⟨39+(IntegerMultBounds.MathlibTM2.Mult.ShortConv.OutputPlacement.code c).val, by omega⟩
  | .src => 0
  | .dst => 1
  | .msk => 2
  | .ms => 3
  | .mwn => 4
  | .m2wn => 5
  | .m2n => 6
  | .kn => 7
  | .sn => 8
  | .smwn => 9
  | .tswn => 10
  | .ef => 11
  | .df => 12
  | .hf => 13
  | .tK => 14
  | .tL => 15
  | .tJ => 16
  | .tC => 17
  | .tA => 18
  | .sr => 19
  | .sel => 20
  | .hv => 21
  | .vk => 22
  | .b1 => 23
  | .ya => 24
  | .tb => 25
  | .xa => 26
  | .xs => 27
  | .pr => 28
  | .hc => 29
  | .ac => 30
  | .ac2 => 31
  | .nv => 32
  | .dout => 33
  | .bx => 34
  | .bo => 35
  | .dtab => 36
  | .padc => 37
  | .prm => 38

private def decodeCR : ℕ → CR
  | 0 => .xs
  | 1 => .ys
  | 2 => .xsv
  | 3 => .ysv
  | 4 => .acc
  | 5 => .out
  | 6 => .wn
  | 7 => .pn
  | 8 => .nn
  | 9 => .tmp
  | 10 => .u0
  | 11 => .u1
  | 12 => .u2
  | 13 => .u3
  | 14 => .ma
  | 15 => .mb
  | 16 => .mc
  | 17 => .md
  | 18 => .sa
  | 19 => .sb
  | 20 => .sc
  | 21 => .sd
  | 22 => .p1
  | 23 => .p2
  | 24 => .p3
  | 25 => .p4
  | 26 => .qr
  | 27 => .qi
  | 28 => .sr
  | 29 => .si
  | _ => .xs

private def decode : ℕ → RsbR
  | 0 => .src
  | 1 => .dst
  | 2 => .msk
  | 3 => .ms
  | 4 => .mwn
  | 5 => .m2wn
  | 6 => .m2n
  | 7 => .kn
  | 8 => .sn
  | 9 => .smwn
  | 10 => .tswn
  | 11 => .ef
  | 12 => .df
  | 13 => .hf
  | 14 => .tK
  | 15 => .tL
  | 16 => .tJ
  | 17 => .tC
  | 18 => .tA
  | 19 => .sr
  | 20 => .sel
  | 21 => .hv
  | 22 => .vk
  | 23 => .b1
  | 24 => .ya
  | 25 => .tb
  | 26 => .xa
  | 27 => .xs
  | 28 => .pr
  | 29 => .hc
  | 30 => .ac
  | 31 => .ac2
  | 32 => .nv
  | 33 => .dout
  | 34 => .bx
  | 35 => .bo
  | 36 => .dtab
  | 37 => .padc
  | 38 => .prm
  | n => .cm (decodeCR (n-39))

private theorem decode_code (r : RsbR) : decode (code r).val = r := by
  cases r <;> first | rfl | (rename_i c; cases c <;> rfl)

theorem code_injective : Function.Injective code := by
  intro r s h
  have hh := congrArg (fun i : Fin 69 => decode i.val) h
  simpa only [decode_code] using hh

def base (r : RsbR) : Fin 148 := ⟨77+(code r).val, by have := (code r).isLt; omega⟩

theorem base_injective : Function.Injective base := by
  intro r s h
  apply code_injective
  apply Fin.ext
  have hh := congrArg Fin.val h
  simpa [base] using hh

def place0 (r : RsbR) : Fin 148 := Equiv.swap (base (.m2wn)) 0 (base r)

def place1 (r : RsbR) : Fin 148 := Equiv.swap (place0 (.kn)) 2 (place0 r)

def place2 (r : RsbR) : Fin 148 := Equiv.swap (place1 (.tswn)) 3 (place1 r)

def place3 (r : RsbR) : Fin 148 := Equiv.swap (place2 (.vk)) 6 (place2 r)

def place4 (r : RsbR) : Fin 148 := Equiv.swap (place3 (.ya)) 7 (place3 r)

def place5 (r : RsbR) : Fin 148 := Equiv.swap (place4 (.xs)) 8 (place4 r)

def place6 (r : RsbR) : Fin 148 := Equiv.swap (place5 (.nv)) 9 (place5 r)

def place7 (r : RsbR) : Fin 148 := Equiv.swap (place6 (.tK)) 10 (place6 r)

def place8 (r : RsbR) : Fin 148 := Equiv.swap (place7 (.tC)) 11 (place7 r)

def place9 (r : RsbR) : Fin 148 := Equiv.swap (place8 (.ac2)) 12 (place8 r)

def place10 (r : RsbR) : Fin 148 := Equiv.swap (place9 (.sel)) 109 (place9 r)

def place11 (r : RsbR) : Fin 148 := Equiv.swap (place10 (.sn)) 116 (place10 r)

def place12 (r : RsbR) : Fin 148 := Equiv.swap (place11 (.cm .wn)) 115 (place11 r)

def reg : RsbR → Fin 148 := place12

theorem reg_injective : Function.Injective reg :=
  (Equiv.injective _).comp ((Equiv.injective _).comp ((Equiv.injective _).comp ((Equiv.injective _).comp ((Equiv.injective _).comp ((Equiv.injective _).comp ((Equiv.injective _).comp ((Equiv.injective _).comp ((Equiv.injective _).comp ((Equiv.injective _).comp ((Equiv.injective _).comp ((Equiv.injective _).comp ((Equiv.injective _).comp (base_injective)))))))))))))

@[simp] theorem reg_m2wn : reg (.m2wn) = 0 := by decide

@[simp] theorem reg_kn : reg (.kn) = 2 := by decide

@[simp] theorem reg_tswn : reg (.tswn) = 3 := by decide

@[simp] theorem reg_vk : reg (.vk) = 6 := by decide

@[simp] theorem reg_ya : reg (.ya) = 7 := by decide

@[simp] theorem reg_xs : reg (.xs) = 8 := by decide

@[simp] theorem reg_nv : reg (.nv) = 9 := by decide

@[simp] theorem reg_tK : reg (.tK) = 10 := by decide

@[simp] theorem reg_tC : reg (.tC) = 11 := by decide

@[simp] theorem reg_ac2 : reg (.ac2) = 12 := by decide

@[simp] theorem reg_sel : reg (.sel) = 109 := by decide

@[simp] theorem reg_sn : reg (.sn) = 116 := by decide

@[simp] theorem reg_width : reg (.cm .wn) = 115 := by decide

def mul (i : Fin 64) : Fin 148 := ⟨13+i.val, by omega⟩

theorem swap_off {f : RsbR → Fin 148} (hf : ∀ r i, f r ≠ mul i)
    (r : RsbR) (k : Fin 148) (hk : k.val < 13 ∨ 77 ≤ k.val) :
    ∀ s i, Equiv.swap (f r) k (f s) ≠ mul i := by
  intro s i he
  have hi : k ≠ mul i := by
    intro hh
    have hv := congrArg Fin.val hh
    simp only [mul] at hv
    rcases hk with hk | hk <;> omega
  have hs := hf s i
  have hr := hf r i
  simp only [Equiv.swap_apply_def] at he
  split_ifs at he <;> simp_all

theorem reg_mul (r : RsbR) (i : Fin 64) : reg r ≠ mul i := by
  have hb : ∀ r i, base r ≠ mul i := by
    intro r i he
    have hh := congrArg Fin.val he
    simp only [base,mul] at hh
    omega
  have h0 := swap_off hb (.m2wn) 0 (by decide)
  have h1 := swap_off h0 (.kn) 2 (by decide)
  have h2 := swap_off h1 (.tswn) 3 (by decide)
  have h3 := swap_off h2 (.vk) 6 (by decide)
  have h4 := swap_off h3 (.ya) 7 (by decide)
  have h5 := swap_off h4 (.xs) 8 (by decide)
  have h6 := swap_off h5 (.nv) 9 (by decide)
  have h7 := swap_off h6 (.tK) 10 (by decide)
  have h8 := swap_off h7 (.tC) 11 (by decide)
  have h9 := swap_off h8 (.ac2) 12 (by decide)
  have h10 := swap_off h9 (.sel) 109 (by decide)
  have h11 := swap_off h10 (.sn) 116 (by decide)
  have h12 := swap_off h11 (.cm .wn) 115 (by decide)
  exact h12 r i

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.BoundaryFoldPlacement
