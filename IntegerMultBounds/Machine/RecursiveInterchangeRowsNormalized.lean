import IntegerMultBounds.Machine.RecursiveInterchangeRows
import IntegerMultBounds.Machine.CyclicRowNormalized

/-! Seven-factor recursive row split/merge with physically normalized payload
heads. Only canonical row/group descriptors remain explicit caller inputs. -/
namespace IntegerMultBounds.Machine.RecursiveInterchangeRowsNormalized
open RecursiveInterchangeLayout (Descriptor volume role)
open RecursiveInterchangeRows (rowLength groups rows rows_length roleArray source_word role_word volume_split)
variable {a : ℕ}

theorem split_hoare (q c : ℕ) (v : Descriptor) (hdiv : c ∣ v.rows)
    (input : Fin (volume q v) → Fin (a+4))
    (source : ℤ → Fin (a+4)) (outputs : Fin c → ℤ → Fin (a+4))
    (p : ℤ) (origins : Fin c → ℤ) (bs gs : List Bool)
    (hb : Counter.value bs = rowLength q v) (hg : Counter.value gs = groups c v) :
    HoareTime (CyclicRowNormalized.splitProgram c a)
      (fun w => w = CyclicRowSplit.bank (CyclicRowCopy.bank (putWord source p (List.ofFn input))
        outputs p origins bs) gs)
      (fun w => w = CyclicRowSplit.bank (CyclicRowCopy.bank (putWord source p (List.ofFn input))
        (fun j => putWord (outputs j) (origins j) (List.ofFn (roleArray q c v hdiv input j)))
        p origins bs) gs)
      (CyclicRowNormalized.cost c (groups c v) (rowLength q v) bs gs) := by
  have hh := CyclicRowNormalized.split_hoare source outputs p origins (rows q c v hdiv input)
    (rowLength q v) (rows_length q c v hdiv input) bs gs hb hg
  simpa only [source_word,role_word] using hh

theorem merge_hoare (q c : ℕ) (v : Descriptor) (hdiv : c ∣ v.rows)
    (input : Fin (volume q v) → Fin (a+4))
    (dest : ℤ → Fin (a+4)) (sources : Fin c → ℤ → Fin (a+4))
    (p : ℤ) (origins : Fin c → ℤ) (bs gs : List Bool)
    (hb : Counter.value bs = rowLength q v) (hg : Counter.value gs = groups c v) :
    HoareTime (CyclicRowNormalized.mergeProgram c a)
      (fun w => w = CyclicRowSplit.bank (CyclicRowCopy.bank dest
        (fun j => putWord (sources j) (origins j) (List.ofFn (roleArray q c v hdiv input j)))
        p origins bs) gs)
      (fun w => w = CyclicRowSplit.bank (CyclicRowCopy.bank (putWord dest p (List.ofFn input))
        (fun j => putWord (sources j) (origins j) (List.ofFn (roleArray q c v hdiv input j)))
        p origins bs) gs)
      (CyclicRowNormalized.cost c (groups c v) (rowLength q v) bs gs) := by
  have hh := CyclicRowNormalized.merge_hoare dest sources p origins (rows q c v hdiv input)
    (rowLength q v) (rows_length q c v hdiv input) bs gs hb hg
  simpa only [source_word,role_word] using hh

theorem cost_linear (q c : ℕ) (v : Descriptor) (hdiv : c ∣ v.rows)
    (hq : 0 < q) (hc : 0 < c) (hv : v.Positive) (bs gs : List Bool)
    (hb : Counter.value bs = rowLength q v) (hg : Counter.value gs = groups c v)
    (cb : GrowingCounterData.Canonical bs) (cg : GrowingCounterData.Canonical gs) :
    CyclicRowNormalized.cost c (groups c v) (rowLength q v) bs gs ≤ 149*volume q v := by
  rcases hv with ⟨ha,hr,hb',hm,he⟩
  have hrow : 0 < rowLength q v := by unfold rowLength; positivity
  have hg' : 0 < groups c v :=
    Nat.mul_pos ha (Nat.div_pos (Nat.le_of_dvd hr hdiv) hc)
  rw [volume_split q c v hdiv]
  exact CyclicRowNormalized.cost_linear _ bs gs hc hg' hrow hb hg cb cg

end IntegerMultBounds.Machine.RecursiveInterchangeRowsNormalized
