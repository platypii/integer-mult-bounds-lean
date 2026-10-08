import IntegerMultBounds.Machine.CyclicRowRewind
import IntegerMultBounds.Machine.CyclicRowMerge

/-! Origin-normalized physical cyclic row split and merge. Each transfer is
followed by a charged nested row/group rewind preserving arbitrary symbols.
The same two descriptors are reused, with no synthesized product count. -/
namespace IntegerMultBounds.Machine.CyclicRowNormalized
open CyclicRowSplit (bank sourceWord roleWord)
variable {a c n : ℕ}

def splitProgram (c a : ℕ) := seq (CyclicRowSplit.program c a) (CyclicRowRewind.program c a)
def mergeProgram (c a : ℕ) := seq (CyclicRowMerge.program c a) (CyclicRowRewind.program c a)

def cost (c n B : ℕ) (bs gs : List Bool) :=
  2*(n*(7*(c*B)+c*(7*bs.length+17))+6*n+7*gs.length+16)+1

/-- Literal split into role streams, with source and every role head restored
to its own original position and both descriptor workspaces restored. -/
theorem split_hoare (source : ℤ → Fin (a+4))
    (outputs : Fin c → ℤ → Fin (a+4)) (p : ℤ) (origins : Fin c → ℤ)
    (rows : Fin n → Fin c → List (Fin (a+4))) (B : ℕ)
    (hw : ∀ i j, (rows i j).length = B) (bs gs : List Bool)
    (hb : Counter.value bs = B) (hg : Counter.value gs = n) :
    HoareTime (splitProgram c a)
      (fun v => v = bank (CyclicRowCopy.bank (putWord source p (sourceWord rows))
        outputs p origins bs) gs)
      (fun v => v = bank (CyclicRowCopy.bank (putWord source p (sourceWord rows))
        (fun j => putWord (outputs j) (origins j) (roleWord rows j)) p origins bs) gs)
      (cost c n B bs gs) := by
  have hs := CyclicRowSplit.split_hoare source outputs p origins rows B hw bs gs hb hg
  have hr := CyclicRowRewind.rewind_hoare (putWord source p (sourceWord rows))
    (fun j => putWord (outputs j) (origins j) (roleWord rows j)) p origins n B bs gs hb hg
  exact (hs.seq hr).consequence (fun _ h => h) (fun _ h => h) (le_of_eq (by unfold cost; ring))

/-- Literal inverse merge, preserving every role stream and returning both
the common output and all role heads to their respective original positions. -/
theorem merge_hoare (dest : ℤ → Fin (a+4))
    (sources : Fin c → ℤ → Fin (a+4)) (p : ℤ) (origins : Fin c → ℤ)
    (rows : Fin n → Fin c → List (Fin (a+4))) (B : ℕ)
    (hw : ∀ i j, (rows i j).length = B) (bs gs : List Bool)
    (hb : Counter.value bs = B) (hg : Counter.value gs = n) :
    HoareTime (mergeProgram c a)
      (fun v => v = bank (CyclicRowCopy.bank dest
        (fun j => putWord (sources j) (origins j) (roleWord rows j)) p origins bs) gs)
      (fun v => v = bank (CyclicRowCopy.bank (putWord dest p (sourceWord rows))
        (fun j => putWord (sources j) (origins j) (roleWord rows j)) p origins bs) gs)
      (cost c n B bs gs) := by
  have hm := CyclicRowMerge.merge_hoare dest sources p origins rows B hw bs gs hb hg
  have hr := CyclicRowRewind.rewind_hoare (putWord dest p (sourceWord rows))
    (fun j => putWord (sources j) (origins j) (roleWord rows j)) p origins n B bs gs hb hg
  exact (hm.seq hr).consequence (fun _ h => h) (fun _ h => h) (le_of_eq (by unfold cost; ring))

/-- Normalization is fully charged and still linear in total payload volume. -/
theorem cost_linear (B : ℕ) (bs gs : List Bool)
    (hc : 0 < c) (hn : 0 < n) (hB : 0 < B)
    (hb : Counter.value bs = B) (hg : Counter.value gs = n)
    (cb : GrowingCounterData.Canonical bs) (cg : GrowingCounterData.Canonical gs) :
    cost c n B bs gs ≤ 149*(n*(c*B)) := by
  have hh := CyclicRowSplit.cost_linear B bs gs hc hn hB hb hg cb cg
  have hv := Nat.mul_pos hn (Nat.mul_pos hc hB)
  unfold cost
  omega

end IntegerMultBounds.Machine.CyclicRowNormalized
