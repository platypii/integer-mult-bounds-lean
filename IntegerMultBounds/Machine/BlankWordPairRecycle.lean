import IntegerMultBounds.Machine.BlankWordReturnAt
import IntegerMultBounds.Machine.WordBankCleanup

/-! Recycle one computed blank-backed word into its original equal-width source
port. Both EOF heads are physically rewound, output is copied back, and the
private output tape is erased. Empty words are covered by the same program. -/
namespace IntegerMultBounds.Machine.BlankWordPairRecycle
noncomputable section
open SharedPlacementAlphabet (setTape)
variable {a : ℕ}

def input (xs ys : List (Fin (a+4))) : Tapes 2 a :=
  Copy.tapes (putWord (fun _ => blank) 0 xs) (putWord (fun _ => blank) 0 ys) xs.length ys.length

def output (ys : List (Fin (a+4))) : Tapes 2 a :=
  Copy.tapes (putWord (fun _ => blank) 0 ys) (fun _ => blank) 0 0

def program (a : ℕ) :=
  seq (seq (seq (BlankWordReturnAt.program (a:=a) (0 : Fin 2))
    (BlankWordReturnAt.program (a:=a) (1 : Fin 2)))
    (WordBankCleanup.replaceProgram (1 : Fin 2) 0 (by decide) (by decide) a))
    (WordBankCleanup.clearProgram (1 : Fin 2) (by decide) a)

theorem runs (xs ys : List (Fin (a+4))) (hlen : xs.length=ys.length)
    (hx : ∀ x∈xs,x≠blank) (hy : ∀ y∈ys,y≠blank) :
    HoareTime (program a) (fun v => v=input xs ys) (fun v => v=output ys) (7*ys.length+16) := by
  let v0 := input xs ys
  let v1 := setTape v0 (0 : Fin 2) (putWord (fun _ => blank) 0 xs) 0
  let v2 := setTape v1 (1 : Fin 2) (putWord (fun _ => blank) 0 ys) 0
  let v3 := WordBankCleanup.write v2 (0 : Fin 2) (putWord (fun _ => blank) 0 ys)
  have h0 := BlankWordReturnAt.runs v0 (0 : Fin 2) xs hx rfl rfl
  have h1 := BlankWordReturnAt.runs v1 (1 : Fin 2) ys hy (by rfl) (by rfl)
  have h2 := WordBankCleanup.replace_hoare v2 (1 : Fin 2) 0 (by decide) (by decide)
    (fun _ => blank) (fun _ => blank) ys xs hlen.symm (by rfl) (by rfl) hy rfl rfl rfl
  have h3 := WordBankCleanup.clear_hoare v3 (1 : Fin 2) (by decide) ys hy (by rfl)
  have he : WordBankCleanup.write v3 (1 : Fin 2) (fun _ => blank)=output ys := by
    apply Placement.Tapes.ext'
    all_goals intro i; fin_cases i <;> rfl
  exact (((h0.seq h1).seq h2).seq h3).consequence (fun _ h => h)
    (fun _ h => h.trans he) (by omega)

end
end IntegerMultBounds.Machine.BlankWordPairRecycle
