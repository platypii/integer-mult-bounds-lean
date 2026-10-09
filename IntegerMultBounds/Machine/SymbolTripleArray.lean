import IntegerMultBounds.Machine.SymbolTripleDecodeStream
import Mathlib.Data.List.OfFn

/-! Literal Boolean arrays for native symbol records. Three bits per symbol
are followed by arbitrary spectator bits; permutations move the entire record,
so decoding recovers each native symbol and every spectator without a supplied
codec assumption. Physical encoder and decoder contracts use these same words. -/
namespace IntegerMultBounds.Machine.SymbolTripleArray
noncomputable section
variable {H B K : ℕ}

def triple (xs : Fin B → Fin 6) (i : Fin (B*3)) : Bool :=
  let ji := finProdFinEquiv.symm i
  SymbolTripleEncode.bit (xs ji.1) ji.2

theorem triple_at (xs : Fin B → Fin 6) (j : Fin B) (i : Fin 3) :
    triple xs (finProdFinEquiv (j,i))=SymbolTripleEncode.bit (xs j) i := by
  simp [triple]

def decode (bs : Fin (B*3) → Bool) (j : Fin B) : Fin 6 :=
  SymbolTripleDecode.value (bs (finProdFinEquiv (j,0)))
    (bs (finProdFinEquiv (j,1))) (bs (finProdFinEquiv (j,2)))

theorem decode_triple (xs : Fin B → Fin 6) : decode (triple xs)=xs := by
  funext j
  simp only [decode,triple_at]
  exact SymbolTripleDecode.value_code (xs j)

theorem triple_word (xs : Fin B → Fin 6) :
    (List.ofFn (triple xs)).map (bitSymbol (a:=2))=
      SymbolTripleStream.word (List.ofFn xs) := by
  rw [List.map_ofFn,List.ofFn_mul]
  unfold SymbolTripleStream.word
  rw [List.map_ofFn]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext j
  simp only [Function.comp_apply,SymbolTripleEncode.encoded,SymbolTripleEncode.code,List.map_ofFn]
  apply congrArg List.ofFn
  funext i
  congr 1
  have he : (⟨j.val*3+i.val,by omega⟩ : Fin (B*3))=finProdFinEquiv (j,i) := by
    apply Fin.ext
    simp [finProdFinEquiv,Nat.mul_comm,Nat.add_comm]
  rw [he,triple_at]

def record (xs : Fin B → Fin 6) (tail : Fin K → Bool) : Fin (B*3+K) → Bool :=
  Fin.addCases (triple xs) tail

theorem record_symbol (xs : Fin B → Fin 6) (tail : Fin K → Bool) (i : Fin (B*3)) :
    record xs tail (Fin.castAdd K i)=triple xs i := by simp [record]

theorem record_spectator (xs : Fin B → Fin 6) (tail : Fin K → Bool) (i : Fin K) :
    record xs tail (Fin.natAdd (B*3) i)=tail i := by simp [record]

def array (xs : Fin H → Fin B → Fin 6) (tail : Fin H → Fin K → Bool)
    (i : Fin (H*(B*3+K))) : Bool :=
  let jr := finProdFinEquiv.symm i
  record (xs jr.1) (tail jr.1) jr.2

theorem array_at (xs : Fin H → Fin B → Fin 6) (tail : Fin H → Fin K → Bool)
    (j : Fin H) (r : Fin (B*3+K)) :
    array xs tail (finProdFinEquiv (j,r))=record (xs j) (tail j) r := by simp [array]

/-- Whole-record address transport preserves each native symbol and every
spectator. No assumption that spectator bits are zero is used. -/
theorem transport (P : Equiv.Perm (Fin H))
    (xs : Fin H → Fin B → Fin 6) (tail : Fin H → Fin K → Bool)
    (ys : Fin (H*(B*3+K)) → Bool)
    (hy : ∀ j r,ys (finProdFinEquiv (P j,r))=array xs tail (finProdFinEquiv (j,r))) :
    ys=array (xs ∘ P.symm) (tail ∘ P.symm) := by
  funext i
  cases he : finProdFinEquiv.symm i with
  | mk j r =>
    have hi : finProdFinEquiv (j,r)=i := by
      simpa only [he] using finProdFinEquiv.apply_symm_apply i
    rw [←hi]
    simpa only [P.apply_symm_apply,array_at,Function.comp_apply] using hy (P.symm j) r

/-- The physical decoder consumes the exact literal Boolean row generated
above, rather than an existentially specified representation. -/
theorem decoder_runs (f g : ℤ → Fin 6) (p r : ℤ) (xs : Fin B → Fin 6)
    (hblank : f (p+3*B)=blank) :
    HoareTime SymbolTripleDecodeStream.program
      (fun v => v=Copy.tapes (putWord f p ((List.ofFn (triple xs)).map bitSymbol)) g p r)
      (fun v => v=Copy.tapes (putWord f p ((List.ofFn (triple xs)).map bitSymbol))
        (putWord g r (List.ofFn xs)) (p+3*B) (r+B)) (9*B) := by
  rw [triple_word]
  exact SymbolTripleDecodeStream.runs f g p r xs hblank

/-- Actual encoding has the same literal Boolean row and retains the native
source. The nonblank source condition is the physical loop delimiter rule. -/
theorem encoder_runs (f g : ℤ → Fin 6) (p r : ℤ) (xs : Fin B → Fin 6)
    (hblank : f (p+B)=blank) (hn : ∀ j,xs j≠blank) :
    HoareTime SymbolTripleStream.program
      (fun v => v=Copy.tapes (putWord f p (List.ofFn xs)) g p r)
      (fun v => v=Copy.tapes (putWord f p (List.ofFn xs))
        (putWord g r ((List.ofFn (triple xs)).map bitSymbol)) (p+B) (r+3*B)) (7*B) := by
  rw [triple_word]
  have h := SymbolTripleStream.runs f g p r (List.ofFn xs) (by simpa using hblank)
    (by
      intro s hs
      obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hs
      exact hn j)
  simpa only [List.length_ofFn] using h

end
end IntegerMultBounds.Machine.SymbolTripleArray
