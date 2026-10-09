import IntegerMultBounds.Machine.ActiveRepairEarlyKeyPlacement
import IntegerMultBounds.Machine.WordBankCleanup
import IntegerMultBounds.Machine.ExactFrame

/-! Actual word erasure for the generated later-key fields, including the
full destination and guard. The original counter and descriptors are framed. -/
namespace IntegerMultBounds.Machine.ActiveRepairLateKeyCleanup
noncomputable section

def compile : List (Fin 33) → Σ q, Program 33 q 1
  | [] => ⟨1,skip 33 1 (by decide)⟩
  | i::is => ⟨_,seq (WordBankCleanup.clearProgram i (by decide) 1) (compile is).2⟩

def execute : List (Fin 33) → Tapes 33 1 → Tapes 33 1
  | [],v => v
  | i::is,v => execute is (WordBankCleanup.write v i (fun _ => blank))

def cost (is : List (Fin 33)) (ws : Fin 33 → List Bool) :=
  ((is.map (fun i => 2*(ws i).length+4)).sum)

theorem runs (is : List (Fin 33)) (hn : is.Nodup) (v : Tapes 33 1)
    (ws : Fin 33 → List Bool)
    (ht : ∀ i ∈ is, v.tape i=CountedGuardGadgetRecord.word (ws i))
    (hp : ∀ i ∈ is, v.head i=0) :
    HoareTime (compile is).2 (fun x => x=v) (fun x => x=execute is v) (cost is ws) := by
  induction is generalizing v with
  | nil => exact skip_hoare (by decide) v
  | cons i is ih =>
    obtain ⟨hi,hn⟩ := List.nodup_cons.mp hn
    have h0 := WordBankCleanup.clear_hoare v i (by decide)
      ((ws i).map bitSymbol) (ReturnOrigin.bits_nonblank _) (by
        rw [ht i (by simp),hp i (by simp)]; rfl)
    have h1 := ih hn (WordBankCleanup.write v i (fun _ => blank))
      (by intro j hj
          have hji : j≠i := by rintro rfl; exact hi hj
          simpa [WordBankCleanup.write,hji] using ht j (by simp [hj]))
      (by intro j hj; exact hp j (by simp [hj]))
    exact (h0.seq h1).consequence (fun _ h => h) (fun _ h => h)
      (by simp [cost,List.length_map])

def slots : List (Fin 33) := [1,2,3,4,5,19,20,21,22,30]
theorem slots_nodup : slots.Nodup := by decide
def program := extend (compile slots).2 58

theorem runs_shared (v : Tapes 33 1) (ws : Fin 33 → List Bool)
    (ht : ∀ i ∈ slots, v.tape i=CountedGuardGadgetRecord.word (ws i))
    (hp : ∀ i ∈ slots, v.head i=0) :
    HoareTime program (fun x => x=CleanSubbank.bank (s := 58) v)
      (fun x => x=CleanSubbank.bank (s := 58) (execute slots v)) (cost slots ws) :=
  hoare_extend_eq (runs slots slots_nodup v ws ht hp) (SharedBank.empty 58 1)

end
end IntegerMultBounds.Machine.ActiveRepairLateKeyCleanup
