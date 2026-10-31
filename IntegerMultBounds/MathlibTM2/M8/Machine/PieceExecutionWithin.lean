module

public import IntegerMultBounds.MathlibTM2.M8.Machine.PieceExecution
public import IntegerMultBounds.Machine.RunWithinChain

/-! Prefix workspace for the stage-1 literal schedule. Existing execution
contracts supply all nonrecursive pieces; recursive calls carry bounded runs.
The fixed head allowance is shared while the original time bounds still add. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Machine.PieceExecution
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.Networks
variable [Net]
noncomputable section
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open Implementation (commonCount implementation widthSlot pcStack)
open Control
open BaseExecution (entryConfig)
open SharedBankStageInput (raw)
open RecursiveInterchangeLayout (Descriptor volume)
open RecursiveViewedAction (Data)
open Transport (Child)
variable {k b : ℕ} {v : Descriptor}

private theorem noncall_bound (K k : ℕ) (callBound : Wire → Fin Machine.width → Fin Machine.width → ℕ)
    (p : Piece) (hcall : ∀ w i j, p ≠ .call w i j) (hK : overhead k p ≤ K)
    (hV : 0 < volume prime v) : pieceBound (v := v) callBound p ≤ K*volume prime v := by
  have hm := Nat.mul_le_mul_right (volume prime v) hK
  cases p with
  | segment s => simp only [pieceBound,overhead,Nat.add_mul,Nat.one_mul] at *; omega
  | gate g => simp only [pieceBound,overhead,Nat.add_mul,Nat.one_mul] at *; omega
  | reset r => simp only [pieceBound,overhead,Nat.add_mul,Nat.one_mul] at *; omega
  | call w i j => exact False.elim (hcall w i j rfl)

variable (capacity : Fintype.card PC ≤ 2^k) (hw : v.width=Machine.width*b)
  (child : Child v) (hp : v.Positive) (hs : Fin 6 → List Bool)
  (hv : RecursiveDimensionBank.Headers v hs) (f : ℤ → Fin (prime+4)) (p : ℤ)
  (node : Tapes 1 prime) (st : Tapes 2 prime)

/-- Changing the array changes no parked head, including after global padding. -/
theorem dataBank_head_eq (n : ℕ) (data data' : Data payloadCount v) :
    (raw (dataBank hs f p node st data) n).head = (raw (dataBank hs f p node st data') n).head := by
  rfl

include hp hv in
theorem piece_jump_within (Ready : Data payloadCount v → Prop)
    (callBound : Wire → Fin Machine.width → Fin Machine.width → ℕ) (K : ℕ)
    (hK : ∀ site : Site, overhead k pieces[site] ≤ K) (lo hi : ℤ)
    (hbank : ∀ data, Ready data → ∀ j,
      lo+(K*volume prime v : ℕ) ≤ (raw (dataBank hs f p node st data)
        (tapeCount capacity widthSlot pcStack (implementation k))).head j ∧
      (raw (dataBank hs f p node st data) (tapeCount capacity widthSlot pcStack (implementation k))).head j+
        (K*volume prime v : ℕ) ≤ hi)
    (calls : ∀ (site : Site) w i j, pieces[site] = .call w i j → ∀ data, Ready data →
      ∃ n ≤ callBound w i j, RunWithin (Control.program capacity widthSlot pcStack (implementation k))
        (fun z => ∀ j, lo ≤ z.head j ∧ z.head j ≤ hi) n
        (entryConfig capacity (.piece site) (dataBank hs f p node st data))
        (entryConfig capacity (successor site) (dataBank hs f p node st (child w i j data))))
    (site : Site) (data : Data payloadCount v) (hready : Ready data) :
    ∃ n ≤ pieceBound (v := v) callBound pieces[site],
      RunWithin (Control.program capacity widthSlot pcStack (implementation k))
        (fun z => ∀ j, lo ≤ z.head j ∧ z.head j ≤ hi) n
        (entryConfig capacity (.piece site) (dataBank hs f p node st data))
        (entryConfig capacity (successor site) (dataBank hs f p node st
          (Transport.step hw child pieces[site] data))) := by
  classical
  by_cases hcall : ∃ w i j, pieces[site] = .call w i j
  · obtain ⟨w,i,j,hc⟩ := hcall
    simpa only [hc,pieceBound,Transport.step] using calls site w i j hc data hready
  · obtain ⟨n,hn,hr⟩ := piece_jump capacity hw child hp hs hv f p node st Ready callBound
      (fun site w i j hc data hd => by
        obtain ⟨n,hn,hr⟩ := calls site w i j hc data hd
        exact ⟨n,hn,hr.1⟩) site data hready
    have hV := RecursiveAffinePrepare.volume_positive Shared50ModularControl.prime_prime.two_le v hp
    have hb := noncall_bound (v := v) K k callBound pieces[site]
      (fun w i j hc => hcall ⟨w,i,j,hc⟩) (hK site) hV
    exact ⟨n,hn,RunWithin.heads_of_run_le hr (hn.trans hb) lo hi (hbank data hready)⟩

include hp hv in
theorem schedule_run_within (Ready : Data payloadCount v → Prop)
    (preserves : ∀ piece data, Ready data → Ready (Transport.step hw child piece data))
    (callBound : Wire → Fin Machine.width → Fin Machine.width → ℕ) (K : ℕ)
    (hK : ∀ site : Site, overhead k pieces[site] ≤ K) (lo hi : ℤ)
    (hbank : ∀ data, Ready data → ∀ j,
      lo+(K*volume prime v : ℕ) ≤ (raw (dataBank hs f p node st data)
        (tapeCount capacity widthSlot pcStack (implementation k))).head j ∧
      (raw (dataBank hs f p node st data) (tapeCount capacity widthSlot pcStack (implementation k))).head j+
        (K*volume prime v : ℕ) ≤ hi)
    (calls : ∀ (site : Site) w i j, pieces[site] = .call w i j → ∀ data, Ready data →
      ∃ n ≤ callBound w i j, RunWithin (Control.program capacity widthSlot pcStack (implementation k))
        (fun z => ∀ j, lo ≤ z.head j ∧ z.head j ≤ hi) n
        (entryConfig capacity (.piece site) (dataBank hs f p node st data))
        (entryConfig capacity (successor site) (dataBank hs f p node st (child w i j data))))
    (data : Data payloadCount v) (hready : Ready data) :
    ∃ n ≤ (pieces.map (pieceBound (v := v) callBound)).sum,
      RunWithin (Control.program capacity widthSlot pcStack (implementation k))
        (fun z => ∀ j, lo ≤ z.head j ∧ z.head j ≤ hi) n
        (entryConfig capacity first (dataBank hs f p node st data))
        (entryConfig capacity .tempClear (dataBank hs f p node st (Transport.run hw child pieces data))) := by
  let H : TapePred (tapeCount capacity widthSlot pcStack (implementation k)) prime :=
    fun z => ∀ j, lo ≤ z.head j ∧ z.head j ≤ hi
  let P (i : ℕ) (d : Data payloadCount v) := Ready d ∧ d = Transport.run hw child (pieces.take i) data
  let cost (i : ℕ) := if h : i < pieces.length then pieceBound (v := v) callBound pieces[i] else 0
  have hsafe : H (entryConfig capacity (position 0) (dataBank hs f p node st data)).tapes := by
    intro j
    have hb := hbank data hready j
    change lo ≤ (raw (dataBank hs f p node st data) _).head j ∧
      (raw (dataBank hs f p node st data) _).head j ≤ hi
    omega
  obtain ⟨d,hd,n,hn,hr⟩ := RunWithin.chain_cost
    (M := Control.program capacity widthSlot pcStack (implementation k))
    (fun i d => entryConfig capacity (position i) (dataBank hs f p node st d)) P H cost data
    (show P 0 data from ⟨hready,rfl⟩) hsafe pieces.length (fun i hlt d hd => by
      let site : Site := ⟨i,hlt⟩
      obtain ⟨n,hn,hr⟩ := piece_jump_within capacity hw child hp hs hv f p node st Ready callBound K hK lo hi
        hbank calls site d hd.1
      refine ⟨Transport.step hw child pieces[site] d,⟨preserves _ _ hd.1,?_⟩,n,?_,?_⟩
      · rw [hd.2,List.take_succ_eq_append_getElem hlt]
        simp only [Transport.run,List.foldl_append,List.foldl_cons,List.foldl_nil]
        rfl
      · simpa only [cost,dite_eq_left hlt,Fin.getElem_fin,site] using hn
      · have hp : position i = .piece site := by simp only [position,dite_eq_left hlt]; rfl
        rw [hp]
        exact hr)
  have hsum : (∑ i ∈ Finset.range pieces.length, cost i) = (pieces.map (pieceBound (v := v) callBound)).sum := by
    rw [Finset.sum_range,←List.sum_ofFn]
    congr 1
    apply List.ext_get <;> simp [cost]
  rw [hsum] at hn
  rw [hd.2] at hr
  refine ⟨n,hn,?_⟩
  simpa only [List.take_length,show position 0 = first from rfl,
    show position pieces.length = .tempClear by simp [position]] using hr

end
end IntegerMultBounds.MathlibTM2.M8.Machine.PieceExecution
