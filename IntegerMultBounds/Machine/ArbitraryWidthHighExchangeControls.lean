import IntegerMultBounds.Machine.ArbitrarySliceRepeat
import IntegerMultBounds.Machine.BinaryDescriptorInstall

/-! Physical controls for high-prefix exchange. Only rho is supplied; offset0,
width1 and depth0 are written, rho is copied into the consumed digit, and every
created descriptor is erased after the counted slice calls. -/
namespace IntegerMultBounds.Machine.ArbitraryWidthHighExchangeControls
noncomputable section
variable {a : ℕ}
open RecursiveChildQuotientsConstant (bits)
open SharedPlacementAlphabet (setTape)

private def hd : Option (List Bool) → ℤ | none => 0 | some _ => 1
private def tp : Option (List Bool) → ℤ → Fin (a+4)
  | none => fun _ => blank
  | some xs => BinaryDescriptorStack.descriptor xs

/-- Slice offset/width0–1; work/frame2–11; loop clock12,digit13;
retained rho14, depth15. Absent descriptors are genuinely blank at head0. -/
def bank (rs : List Bool) (ts bs ds js : Option (List Bool)) : Tapes 16 a :=
  ⟨(fun i => match i.val with
    | 0 => hd ts
    | 1 => hd bs
    | 13 => hd ds
    | 14 => 1
    | 15 => hd js
    | _ => 0),
   (fun i => match i.val with
    | 0 => tp ts
    | 1 => tp bs
    | 13 => tp ds
    | 14 => BinaryDescriptorStack.descriptor rs
    | 15 => tp js
    | _ => fun _ => blank)⟩

def input (rs : List Bool) : Tapes 16 a := bank rs none none none none
def prepared (rs : List Bool) : Tapes 16 a := bank rs (some (bits 0)) (some (bits 1)) (some rs) (some (bits 0))
def returned (rs ts : List Bool) : Tapes 16 a := bank rs (some ts) (some (bits 1)) none (some (bits 0))

def constantProgram (i : Fin 16) (n : ℕ) := Placement.placed (RecursiveChildQuotientsConstant.program (a := a) n)
  (FiniteReturnStackAt.placement i)
def copyProgram : Program 16 5 a := BinaryDescriptorInstall.program a 14 13 (by decide)
def program := seq (seq (seq (constantProgram (a := a) 0 0) (constantProgram 1 1)) (constantProgram 15 0)) copyProgram
def cleanupProgram : Program 16 12 a := seq (seq (BinaryDescriptorCleanupList.oneProgram 0)
  (BinaryDescriptorCleanupList.oneProgram 1)) (BinaryDescriptorCleanupList.oneProgram 15)

private theorem constant_hoare (i : Fin 16) (n : ℕ) (v : Tapes 16 a)
    (ht : v.tape i = fun _ => blank) (hh : v.head i = 0) :
    HoareTime (constantProgram i n) (fun w => w = v)
      (fun w => w = setTape v i (BinaryDescriptorStack.descriptor (bits n)) 1)
      (RecursiveChildQuotientsConstant.cost n) := by
  have h := Placement.hoare_at (RecursiveChildQuotientsConstant.initialize_hoare (a := a) n)
    (FiniteReturnStackAt.placement i) v (by rw [FiniteReturnStackAt.active_bank]; simp [ht,hh])
  apply h.consequence (fun _ h => h) _ le_rfl
  rintro w ⟨small,rfl,rfl⟩
  exact FiniteReturnStackAt.replace_bank i v _ _

theorem initializes (rs : List Bool) :
    HoareTime (program (a := a)) (fun v => v = input rs) (fun v => v = prepared rs) (2*rs.length+29) := by
  let v1 : Tapes 16 a := bank rs (some (bits 0)) none none none
  let v2 : Tapes 16 a := bank rs (some (bits 0)) (some (bits 1)) none none
  let v3 : Tapes 16 a := bank rs (some (bits 0)) (some (bits 1)) none (some (bits 0))
  have h1 := constant_hoare 0 0 (input (a := a) rs) rfl rfl
  have e1 : setTape (input (a := a) rs) 0 (BinaryDescriptorStack.descriptor (bits 0)) 1 = v1 := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  rw [e1] at h1
  have h2 := constant_hoare 1 1 v1 rfl rfl
  have e2 : setTape v1 1 (BinaryDescriptorStack.descriptor (bits 1)) 1 = v2 := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  rw [e2] at h2
  have h3 := constant_hoare 15 0 v2 rfl rfl
  have e3 : setTape v2 15 (BinaryDescriptorStack.descriptor (bits 0)) 1 = v3 := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  rw [e3] at h3
  have h4 := BinaryDescriptorInstall.install_hoare (14 : Fin 16) 13 (by decide) v3 rs
    (BinaryDescriptorStackRoundtrip.descriptor_encoded rs) rfl rfl rfl
  have e4 : setTape v3 13 (RadixZeroFill.encodedBinary rs) 1 = prepared rs := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> try rfl
    exact (BinaryDescriptorStackRoundtrip.descriptor_encoded rs).symm
  rw [e4] at h4
  exact (((h1.seq h2).seq h3).seq h4).consequence (fun _ h => h) (fun _ h => h) (by
    change 6+1+9+1+6+1+(2*rs.length+5) ≤ 2*rs.length+29
    omega)

theorem cleans (rs ts : List Bool) :
    HoareTime (cleanupProgram (a := a)) (fun v => v = returned rs ts) (fun v => v = input rs)
      (2*ts.length+16) := by
  let v1 : Tapes 16 a := bank rs none (some (bits 1)) none (some (bits 0))
  let v2 : Tapes 16 a := bank rs none none none (some (bits 0))
  have h1 := BinaryDescriptorCleanupList.one_hoare (0 : Fin 16) (returned (a := a) rs ts) ts rfl rfl
  have e1 : setTape (returned (a := a) rs ts) 0 (fun _ => blank) 0 = v1 := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  rw [e1] at h1
  have h2 := BinaryDescriptorCleanupList.one_hoare (1 : Fin 16) v1 (bits 1) rfl rfl
  have e2 : setTape v1 1 (fun _ => blank) 0 = v2 := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  rw [e2] at h2
  have h3 := BinaryDescriptorCleanupList.one_hoare (15 : Fin 16) v2 (bits 0) rfl rfl
  have e3 : setTape v2 15 (fun _ => blank) 0 = input rs := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  rw [e3] at h3
  exact ((h1.seq h2).seq h3).consequence (fun _ h => h) (fun _ h => h) (by
    change 2*ts.length+4+1+(2*1+4)+1+(2*0+4) ≤ 2*ts.length+16
    omega)

end
end IntegerMultBounds.Machine.ArbitraryWidthHighExchangeControls
