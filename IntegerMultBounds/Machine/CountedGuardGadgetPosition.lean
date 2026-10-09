import IntegerMultBounds.Machine.CountedPosition
import IntegerMultBounds.Machine.BinaryDescriptorCleanupList
import IntegerMultBounds.Machine.RecursiveChildQuotientsConstant

/-! Real runtime-distance replay inside a guard record. One is not compiled
per width: the canonical count is read by the reusable countdown, with physical
clock initialization and erasure from wholly blank private storage. -/
namespace IntegerMultBounds.Machine.CountedGuardGadgetPosition
noncomputable section
variable {a : ℕ}
open SharedPlacementAlphabet

def input (f : ℤ → Fin (a+4)) (p : ℤ) (ks : List Bool) : Tapes 3 a :=
  ⟨![p,0,1],![f,fun _ => blank,CountedLoopReuseAlphabet.binary ks]⟩
def output (f : ℤ → Fin (a+4)) (p : ℤ) (ks : List Bool) (n : ℕ) := input f (p-n) ks

def mark : Program 3 2 a where
  tapes_pos := by decide
  start := 0
  transition := fun s sy => if s=0 then some (1,fun i =>
    if i=1 then (separator,Move.right) else (sy i,Move.stay)) else none

def cleanup := BinaryDescriptorCleanupList.oneProgram (a := a) (1 : Fin 3)
def program := seq (seq (mark (a := a)) (CountedPosition.program Move.left)) cleanup

private theorem marks (f : ℤ → Fin (a+4)) (p : ℤ) (ks : List Bool) :
    HoareTime mark (fun v => v=input f p ks) (fun v => v=CountedPosition.bank f p ks) 1 := by
  intro v hv
  subst v
  refine ⟨1,⟨1,(CountedPosition.bank f p ks).head,(CountedPosition.bank f p ks).tape⟩,le_rfl,?_,?_,rfl⟩
  · rw [run_one]
    simp only [step,mark,Tapes.start,ite_true]
    congr 1
    congr 1
    · funext i; fin_cases i <;> simp [input,CountedPosition.bank,CountedPosition.one,
        CountedLoopReuseAlphabet.bank,CountedLoopReuseAlphabet.controls,Tapes.append,Fin.addCases,Move.offset]
    · funext i z; fin_cases i <;> simp [input,CountedPosition.bank,CountedPosition.one,
        CountedLoopReuseAlphabet.bank,CountedLoopReuseAlphabet.controls,Tapes.append,Fin.addCases,
        CountedLoopReuseAlphabet.empty] <;> aesop
  · simp [step,mark]

theorem positions (f : ℤ → Fin (a+4)) (p : ℤ) (ks : List Bool) (n : ℕ)
    (hk : Counter.value ks=n) :
    HoareTime program (fun v => v=input f p ks) (fun v => v=output f p ks n)
      (7*n+7*ks.length+23) := by
  have h1 := marks f p ks
  have h2 := CountedPosition.position_hoare Move.left f p ks n hk
  simp only [Move.offset,mul_neg_one] at h2
  have h3 := BinaryDescriptorCleanupList.one_hoare (1 : Fin 3)
    (CountedPosition.bank f (p-n) ks) [] rfl rfl
  have he : setTape (CountedPosition.bank f (p-n) ks) 1 (fun _ => blank) 0 = output f p ks n := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  rw [he] at h3
  exact ((h1.seq h2).seq h3).consequence (fun _ h => h) (fun _ h => h) (by simp; omega)

end
end IntegerMultBounds.Machine.CountedGuardGadgetPosition
