import IntegerMultBounds.Machine.RecursiveWidthGuard
import IntegerMultBounds.Machine.FiniteFlow
import IntegerMultBounds.Machine.RecursiveChildQuotients

/-! Conditional three-block recursive entry controller. PC zero physically
tests width; PCs one and two are supplied base and recursive-entry machines.
Their exit tables are explicit and may include backedges. This does not supply
the recursive-entry implementation or assert that its execution terminates. -/
namespace IntegerMultBounds.Machine.RecursiveWidthBranch
variable {t a b r : ℕ}
noncomputable section

abbrev states (b r : ℕ) : Fin 3 → ℕ := ![4,b,r]

def family (width : Fin t) (base : Program t b a) (recur : Program t r a) :
    (pc : Fin 3) → Program t (states b r pc) a :=
  Fin.cases (RecursiveWidthGuard.program width) (Fin.cases base (Fin.cases recur (fun i => Fin.elim0 i)))

def next (baseExit : Fin b → Option (Fin 3)) (recurExit : Fin r → Option (Fin 3)) :
    FiniteFlow.Next (states b r) :=
  Fin.cases (fun (st : Fin 4) => if st = RecursiveWidthGuard.base then some 1
    else if st = RecursiveWidthGuard.recurse then some 2 else none)
    (Fin.cases baseExit (Fin.cases recurExit (fun i => Fin.elim0 i)))

def program (width : Fin t) (base : Program t b a) (recur : Program t r a)
    (baseExit : Fin b → Option (Fin 3)) (recurExit : Fin r → Option (Fin 3)) :=
  FiniteFlow.program (family width base recur) (next baseExit recurExit) 0

def branch (n : ℕ) : Fin 3 := if n = 1 then 1 else 2

/-- Physical guard and its one-step branch edge, with exact entered state.
The arbitrary supplied branch programs have not executed at this point. -/
theorem enter_exact (width : Fin t) (base : Program t b a) (recur : Program t r a)
    (baseExit : Fin b → Option (Fin 3)) (recurExit : Fin r → Option (Fin 3))
    (v : Tapes t a) (bs : List Bool) (hh : v.head width = 1)
    (ht : v.tape width = BinaryDescriptorStack.descriptor bs)
    (hc : GrowingCounterData.Canonical bs) :
    ∃ k ≤ 3, run (program width base recur baseExit recurExit) k
      (v.start (program width base recur baseExit recurExit)) =
      some ((v.start (family width base recur (branch (Counter.value bs)))).mapState
        (FiniteFlow.embed (states b r) (branch (Counter.value bs)))) := by
  obtain ⟨k,hk,hr,hh'⟩ := RecursiveWidthGuard.canonical_exact width v bs hh ht hc
  let st : Fin 4 := if Counter.value bs = 1 then RecursiveWidthGuard.base else RecursiveWidthGuard.recurse
  let c := RecursiveWidthGuard.cfg v st
  have hblock := FiniteFlow.block_run (family width base recur) (next baseExit recurExit) 0 0 k
    (v.start (RecursiveWidthGuard.program width)) c hr
  have hselect : next baseExit recurExit 0 c.state = some (branch (Counter.value bs)) := by
    change (if st = RecursiveWidthGuard.base then some 1 else
      if st = RecursiveWidthGuard.recurse then some 2 else none) = some (branch (Counter.value bs))
    dsimp only [st,branch]
    split_ifs <;> simp_all [RecursiveWidthGuard.base,RecursiveWidthGuard.recurse]
  have hjump := FiniteFlow.jump (family width base recur) (next baseExit recurExit) 0 0
    (branch (Counter.value bs)) c hh' hselect
  refine ⟨k+1,by omega,?_⟩
  change run (FiniteFlow.program (family width base recur) (next baseExit recurExit) 0) (k+1)
    ((v.start (RecursiveWidthGuard.program width)).mapState (FiniteFlow.embed (states b r) 0)) = _
  rw [run_add]
  erw [hblock]
  simp only [Option.bind_some,run_one]
  exact hjump

/-- The actual constructor-bank layout has width in slot six (header index three). -/
theorem headers_enter (base : Program 38 b a) (recur : Program 38 r a)
    (baseExit : Fin b → Option (Fin 3)) (recurExit : Fin r → Option (Fin 3))
    (d : RecursiveInterchangeLayout.Descriptor) (hs : Fin 6 → List Bool)
    (hh : RecursiveDimensionBank.Headers d hs) :
    ∃ k ≤ 3, run (program 6 base recur baseExit recurExit) k
      ((RecursiveChildQuotients.input hs).start (program 6 base recur baseExit recurExit)) =
      some (((RecursiveChildQuotients.input hs).start (family 6 base recur (branch d.width))).mapState
        (FiniteFlow.embed (states b r) (branch d.width))) := by
  have h := enter_exact 6 base recur baseExit recurExit (RecursiveChildQuotients.input hs) (hs 3)
    (by rfl) (by rfl) (hh.2 3)
  have hv : Counter.value (hs 3) = d.width := hh.1 3
  rw [hv] at h
  exact h

theorem branch_pow (m depth : ℕ) (hm : 2 ≤ m) :
    branch (m^depth) = if depth = 0 then 1 else 2 := by
  cases depth with
  | zero => simp [branch]
  | succ depth =>
    have hp : 0 < m^depth := pow_pos (by omega) _
    have hn : m^(depth+1) ≠ 1 := by rw [pow_succ]; nlinarith
    simp only [branch,hn,ite_false,Nat.succ_ne_zero]

/-- Depth zero reaches the supplied base block; positive depth reaches the
supplied recursive-entry block, with the same exact 38-tape bank. -/
theorem power_headers_enter (base : Program 38 b a) (recur : Program 38 r a)
    (baseExit : Fin b → Option (Fin 3)) (recurExit : Fin r → Option (Fin 3))
    (d : RecursiveInterchangeLayout.Descriptor) (hs : Fin 6 → List Bool)
    (hh : RecursiveDimensionBank.Headers d hs) (m depth : ℕ) (hm : 2 ≤ m)
    (hw : d.width = m^depth) :
    ∃ k ≤ 3, run (program 6 base recur baseExit recurExit) k
      ((RecursiveChildQuotients.input hs).start (program 6 base recur baseExit recurExit)) =
      some (((RecursiveChildQuotients.input hs).start
        (family 6 base recur (if depth = 0 then 1 else 2))).mapState
        (FiniteFlow.embed (states b r) (if depth = 0 then 1 else 2))) := by
  have h := headers_enter base recur baseExit recurExit d hs hh
  rw [hw,branch_pow m depth hm] at h
  exact h

end
end IntegerMultBounds.Machine.RecursiveWidthBranch
