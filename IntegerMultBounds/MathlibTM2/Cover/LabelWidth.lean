module

public import IntegerMultBounds.MathlibTM2.Cover.LabelSchedule

/-! Convert the width header between atoms and columns while preserving the other headers. -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Cover.LabelWidth
noncomputable section

open IntegerMultBounds.Machine
open IntegerMultBounds.MathlibTM2.M8.RevMachine
open IntegerMultBounds.MathlibTM2.M8.Stage2Machine.Straight
open IntegerMultBounds.MathlibTM2.M8.Stage2Machine.Width (constAt const_step)
open IntegerMultBounds.Networks.Shared50ModularControl (prime prime_prime)
open RecursiveInterchangeLayout (Descriptor)
open LabelSchedule (base)

def widen : List Instr :=
  [.prod 7 8 6 (by decide), .erase 6, .copy 8 6 (by decide), .erase 8, .erase 7]

def narrow : List Instr :=
  [.div 6 7 8 9 (by decide), .erase 9, .erase 6, .copy 8 6 (by decide), .erase 8, .erase 7]

def input (v : Descriptor) (w m : ℕ) := Function.update (base v w) (7 : Fin 22) (some m)

def program (m : ℕ) (l : List Instr) :=
  seq (constAt (q := prime) m 7) (prog (q := prime) prime_prime.two_le l).2

def cost (v : Descriptor) (w m : ℕ) (l : List Instr) :=
  RecursiveChildQuotientsConstant.cost m + 1 + costs prime l (input v w m)

private theorem run (v : Descriptor) (w m c : ℕ) (l : List Instr)
    (hp : Pres prime l (input v w m)) (he : execs prime l (input v w m) = base v c) :
    HoareTime (program m l) (fun x => x = Headers.bank (words (base v w)))
      (fun x => x = Headers.bank (words (base v c))) (cost v w m l) := by
  have h := runs (q := prime) prime_prime.two_le l (input v w m) hp
  rw [he] at h
  exact (const_step (q := prime) (s := base v w) (j := 7) m rfl).seq h

theorem widen_runs (v : Descriptor) (w m : ℕ) (hm : 0 < m) :
    HoareTime (program m widen) (fun x => x = Headers.bank (words (base v w)))
      (fun x => x = Headers.bank (words (base v (w*m)))) (cost v w m widen) := by
  apply run
  · split_ands <;> first | exact hm | decide | rfl | trivial
  · funext i; fin_cases i <;> rfl

theorem narrow_runs (v : Descriptor) (w m : ℕ) (hm : 0 < m) :
    HoareTime (program m narrow) (fun x => x = Headers.bank (words (base v (w*m))))
      (fun x => x = Headers.bank (words (base v w))) (cost v (w*m) m narrow) := by
  apply run
  · split_ands <;> first | exact hm | decide | rfl | trivial
  · funext i; fin_cases i <;> first | rfl | exact congrArg some (Nat.mul_div_cancel w hm)

theorem widen_cost (v : Descriptor) (w m : ℕ) :
    cost v w m widen ≤ RecursiveChildQuotientsConstant.cost m + 1 +
      10001 * (3*(w*m) + w + m + 5) := by
  apply Nat.add_le_add_left
  apply (costs_le (q := prime) widen _).trans
  apply Nat.mul_le_mul_left
  change (w*m+1) + ((w+1) + ((w*m+1) + ((w*m+1) + ((m+1) + 0)))) ≤ _
  omega

theorem narrow_cost (v : Descriptor) (w m : ℕ) (hm : 0 < m) :
    cost v (w*m) m narrow ≤ RecursiveChildQuotientsConstant.cost m + 1 +
      10001 * (2*(w*m) + 2*w + 2*m + 6) := by
  apply Nat.add_le_add_left
  apply (costs_le (q := prime) narrow _).trans
  apply Nat.mul_le_mul_left
  change (w*m+m+1) + ((w*m%m+1) + ((w*m+1) + ((w*m/m+1) + ((w*m/m+1) + ((m+1) + 0))))) ≤ _
  rw [Nat.mul_div_cancel _ hm, Nat.mul_mod_left]
  omega

end
end IntegerMultBounds.MathlibTM2.Cover.LabelWidth
