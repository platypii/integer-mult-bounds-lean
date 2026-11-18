module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackCompleteSwap
public import IntegerMultBounds.MathlibTM2.Cover.FallbackShearReady

/-! The physical swap realizes coordinate exchange on the original indexed binary payload. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host M8.RevMachine FlatCoordinateLayout
open IntegerMultBounds.Networks.Shared50ModularControl (prime prime_prime)
open RecursiveInterchangeLayout (volume)
open M8.Machine.ArbitraryWidthHighExchangeShared (sourceWord)
variable [M8.Machine.Net] {P U : Type}
local notation "N" => rowSwapBlock.tapes
local notation "Q" => rowSwapBlock.states
local instance (w : ℕ) : NeZero (prime^(w+1)) := ⟨(pow_pos prime_prime.pos _).ne'⟩

omit [M8.Machine.Net] in
private theorem ofFn_cast {a b : ℕ} {α : Type*} (h : a = b) (f : Fin b → α) :
    List.ofFn (fun i => f (Fin.cast h i)) = List.ofFn f := by subst b; rfl

theorem columnReady_swap [Fintype P] {d w W : ℕ} (i j : Fin d) (lt : i < j) (H J : ℕ)
    (hm : prime^(w+1) < 2^H) (hw : W < 2^J) (hW : 0 < W)
    (body : P → Pr P (N+35) Q prime U) (v : HS (N+35) Q prime U) (S : Stacks (N+35) prime)
    (matrix : Matrix (Fin d) (Fin d) (ZMod (prime^(w+1)))) (tail : List (Fin (prime+4)))
    (dest : ℤ → Fin 4) (q : ℤ) (original : Fin ((prime^(w+1))^d*W) → ZMod 2)
    (addr : (Fin d → ZMod (prime^(w+1))) → Fin d → ZMod (prime^(w+1))) :
    let bank : Fin 35 ↪ Fin (N+35) := (Fin.castLEEmb (by decide : 35 ≤ 59)).trans (Fin.castLEEmb swapHostFits)
    let ready := ColumnReady bank H J matrix tail SparseRoleCircuit.encode (fun _ => blank) dest 0 q original
    ready addr S → (∀ k : Fin (N+35), 35 ≤ k.val → S.L k = [] ∧ S.R k = []) →
    ∃ z F n, z.user = v.user ∧ n ≤ completeSwapTime body d i j w W H J ∧
      Exec body (completeSwap d i j) (mk v S) n (mk z F) ∧
      ready (fun x => addr x ∘ Equiv.swap i j) F ∧
      ∀ k : Fin (N+35), 35 ≤ k.val → F.L k = [] ∧ F.R k = [] := by
  intro bank ready ⟨a,layout,placed⟩ empty
  let view := payloadView prime d (w+1) W
  have size : volume prime view = (prime^(w+1))^d*W := by simp [view,payloadView,volume,← pow_mul,Nat.mul_comm d]
  let x := fun k => a (Fin.cast size k)
  have word : List.ofFn (SparseRoleCircuit.encode (a := 0) ∘ x) = List.ofFn (SparseRoleCircuit.encode (a := 0) ∘ a) :=
    ofFn_cast size (SparseRoleCircuit.encode (a := 0) ∘ a)
  obtain ⟨y,z,F,n,hz,hn,run,clean,frame,tape,effect⟩ := completeSwap_exec i j lt H J hm hw hW body v S x
    (by funext pos; rw [swap_source_word,word]; change readAt blank (S.L (bank 24)) (S.R (bank 24)) pos = _; simpa only [sub_zero] using layout.src pos)
    layout.modulus layout.one layout.width layout.clock
    (by intro k lo hi; fin_cases k <;> first | contradiction | exact (layout.scratch 3 (by decide)).2 | exact (layout.scratch 4 (by decide)).2 | exact (layout.scratch 5 (by decide)).2 | exact (layout.scratch 6 (by decide)).2 | exact (layout.scratch 7 (by decide)).2 | exact (layout.scratch 8 (by decide)).2) empty
  let out := fun k => y (Fin.cast size.symm k)
  have outWord : List.ofFn (SparseRoleCircuit.encode (a := 0) ∘ out) = List.ofFn (SparseRoleCircuit.encode (a := 0) ∘ y) :=
    ofFn_cast size.symm (SparseRoleCircuit.encode (a := 0) ∘ y)
  have kept (k : Fin 35) (ne : k ≠ 24) : F.L (bank k) = S.L (bank k) ∧ F.R (bank k) = S.R (bank k) := frame k ne
  refine ⟨z,F,n,hz,hn,run,⟨out,?_,?_⟩,clean⟩
  · constructor
    · exact (kept 2 (by decide)).2.trans layout.modulus
    · exact (kept 27 (by decide)).2.trans layout.width
    · exact (kept 28 (by decide)).2.trans layout.one
    · exact (kept 32 (by decide)).2.trans layout.padded
    · exact (congrArg List.length (kept 33 (by decide)).2).trans layout.clock
    · exact (kept 34 (by decide)).2.trans layout.archive
    · intro k hk
      have ne : k ≠ 24 := fun e => (by decide : (24 : Fin 35) ∉ shearWork) (e ▸ hk)
      rw [(kept k ne).1,(kept k ne).2]; exact layout.scratch k hk
    · intro pos; rw [outWord,sub_zero]; exact tape pos
    · intro pos; rw [(kept 25 (by decide)).1,(kept 25 (by decide)).2]; exact layout.dst pos
  · intro coords k
    have e := effect (addr coords) k
    have inside (a : Fin d → ZMod (prime^(w+1))) : (index a k).val < volume prime view := by rw [size]; exact (index a k).isLt
    change ext y _ = ext (V := volume prime view) x _ at e
    rw [ext,dite_eq_left (inside _),ext,dite_eq_left (inside _)] at e
    exact e.trans (placed coords k)

end IntegerMultBounds.MathlibTM2.Cover.Fallback
