import IntegerMultBounds.Machine.Dispatch

/-! Fixed one-hot residue control on a fixed finite bank of tapes. Only the
symbol under each current head encodes the residue. One literal transition
increments it modulo the fixed bank size while preserving every head and all
background cells. The finite decoder is a lookup over scanned symbols only. -/

namespace IntegerMultBounds.Machine.OneHot

variable {c a : ℕ}

def symbol (j i : Fin c) : Fin (a+4) := if i = j then bitSymbol true else bitSymbol false

def bank (v : Tapes c a) (j : Fin c) : Tapes c a :=
  ⟨v.head,fun i => Function.update (v.tape i) (v.head i) (symbol j i)⟩

@[simp] theorem bank_head (v : Tapes c a) (j i : Fin c) : (bank v j).head i = v.head i := rfl

@[simp] theorem bank_at (v : Tapes c a) (j i : Fin c) : (bank v j).tape i (v.head i) = symbol j i := by
  simp [bank]

theorem bank_outside (v : Tapes c a) (j i : Fin c) (p : ℤ) (hp : p ≠ v.head i) :
    (bank v j).tape i p = v.tape i p := by simp [bank,hp]

@[simp] theorem bank_reads (v : Tapes c a) (j : Fin c) : (bank v j).reads = symbol j := by
  funext i
  simp [Tapes.reads]

@[simp] theorem bank_bank (v : Tapes c a) (j k : Fin c) : bank (bank v j) k = bank v k := by
  simp [bank,Function.update_idem]

/-- A fixed finite table. On malformed symbols it still returns a valid index;
on a one-hot bank exactly one term contributes its selected residue. -/
def decode (hc : 0 < c) (symbols : Fin c → Fin (a+4)) : Fin c :=
  ⟨(∑ i : Fin c, if symbols i = bitSymbol true then i.val else 0)%c,Nat.mod_lt _ hc⟩

theorem decode_symbol (hc : 0 < c) (j : Fin c) : decode hc (symbol (a := a) j) = j := by
  have hs (i : Fin c) : (if symbol (a := a) j i = bitSymbol true then i.val else 0) =
      if i = j then i.val else 0 := by
    by_cases hi : i = j <;> simp [symbol,hi,bitSymbol]
  apply Fin.ext
  simp only [decode,hs]
  simp [Nat.mod_eq_of_lt j.isLt]

@[simp] theorem decode_bank (hc : 0 < c) (v : Tapes c a) (j : Fin c) :
    decode hc (bank v j).reads = j := by rw [bank_reads,decode_symbol]

def next (hc : 0 < c) (j : Fin c) : Fin c := ⟨(j.val+1)%c,Nat.mod_lt _ hc⟩

def residue (hc : 0 < c) (n : ℕ) : Fin c := ⟨n%c,Nat.mod_lt _ hc⟩

@[simp] theorem next_residue (hc : 0 < c) (n : ℕ) : next hc (residue hc n) = residue hc (n+1) := by
  apply Fin.ext
  exact Nat.mod_add_mod n c 1

/-- One transition updates all fixed control cells and moves no head. -/
def program (hc : 0 < c) : Program c 2 a where
  tapes_pos := hc
  start := 0
  transition := fun state symbols => if state = 0 then
    some (1,fun i => (symbol (next hc (decode hc symbols)) i,.stay)) else none

def cfg (v : Tapes c a) (state : Fin 2) : Config c 2 a := ⟨state,v.head,v.tape⟩

theorem step_exact (hc : 0 < c) (v : Tapes c a) (j : Fin c) :
    step (program hc) (cfg (bank v j) 0) = some (cfg (bank v (next hc j)) 1) := by
  have ht : (program hc).transition 0 (bank v j).reads =
      some (1,fun i => (symbol (next hc j) i,Move.stay)) := by
    simp only [program,ite_true,decode_bank]
  unfold step
  simp only [cfg]
  unfold Tapes.reads at ht
  rw [ht]
  simp only [Move.offset,add_zero]
  congr 1
  congr 1
  funext i p
  by_cases hp : p = v.head i <;> simp [bank,hp]

theorem halt (hc : 0 < c) (v : Tapes c a) : step (program hc) (cfg v 1) = none := by
  simp [step,program,cfg]

/-- Exact one-step execution and genuine halt, with the complete bank specified. -/
theorem advance_exact (hc : 0 < c) (v : Tapes c a) (j : Fin c) :
    run (program hc) 1 ((bank v j).start (program hc)) = some (cfg (bank v (next hc j)) 1) ∧
    step (program hc) (cfg (bank v (next hc j)) 1) = none := by
  refine ⟨?_,halt hc _⟩
  exact (run_one _ _).trans (step_exact hc v j)

theorem advance_hoare (hc : 0 < c) (v : Tapes c a) (j : Fin c) :
    HoareTime (program hc) (fun input => input = bank v j)
      (fun output => output = bank v (next hc j)) 1 := by
  rintro input rfl
  obtain ⟨hr,hh⟩ := advance_exact hc v j
  exact ⟨1,_,le_rfl,hr,hh,rfl⟩

end IntegerMultBounds.Machine.OneHot
