module

public import IntegerMultBounds.MathlibTM2.Cover.LabelStock
public import IntegerMultBounds.MathlibTM2.Host.ExpandMask

/-! Expand one low-class selector per label record into the physical stock mask. -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Cover.LabelMask
noncomputable section

open IntegerMultBounds.Machine
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open IntegerMultBounds.MathlibTM2.Stack
open RecursiveInterchangeLayout (Descriptor volume)
open Host LabelStock LabelTransport

def records (v : Descriptor) := v.beforeRows*v.rows*v.beforeH

private theorem records_volume (v : Descriptor) : records v * payload v = volume prime v := by
  unfold records payload volume
  ring

def selectors (m w N : ℕ) := (List.range N).map (live m w 1)

private theorem expanded {A : ℕ} (m w W N : ℕ) :
    expandedMask W symBit ((selectors m w N).map (bitSymbol (a := A))) =
      ((List.range (N*W)).map (live m w W)).map bitSymbol := by
  induction N with
  | zero => simp [selectors, expandedMask]
  | succ n ih =>
    rw [Nat.succ_mul, List.range_add, List.map_append, List.map_append]
    unfold selectors at *
    rw [List.range_succ, List.map_append, List.map_append]
    unfold expandedMask at *
    rw [List.flatMap_append, ih]
    simp only [List.map_singleton, List.flatMap_singleton, symBit_bitSymbol, List.map_map]
    congr 1
    rw [← List.length_range (n := W), ← List.map_const']
    simp only [List.length_range]
    apply List.map_congr_left
    intro j hj
    simp only [Function.comp_apply]
    have hj' := List.mem_range.mp hj
    have h : (n*W+j)/W = n := by
      rw [Nat.mul_comm n W, Nat.mul_add_div (by omega), Nat.div_eq_of_lt hj', Nat.add_zero]
    have he : residue m w W (n*W+j) = residue m w 1 n := by
      funext r c
      simp only [residue, h, Nat.div_one]
    simp only [live, he]

/-- A retained record mask and a retained unary payload width suffice for the stock pass. -/
theorem expand_exec {T Q A : ℕ} {P U : Type} (body : P → Pr P T Q A U)
    {mask width saved tmp acc out : Fin T} (hr : [mask,width,saved,tmp,acc,out].Nodup)
    (v : Descriptor) (m w : ℕ) (u : HS T Q A U) (S : Stacks T A)
    (hm : S.R mask = (selectors m w (records v)).map bitSymbol)
    (hw : (S.R width).length = payload v) (hf : ∀ k ∈ [saved,tmp,acc], S.R k = []) :
    ∃ u' n, u'.user = u.user ∧ n ≤ 6*volume prime v + 10*records v + 6 ∧
      Exec body (expandMask mask width saved tmp acc out symBit) (mk u S) n
        (mk u' { S with R := Function.update S.R out ((((List.range (volume prime v)).map (live m w (payload v))).map bitSymbol) ++ S.R out) }) := by
  obtain ⟨u', n, hu, hn, he⟩ := expandMask_exec (body := body) hr (payload v) symBit u S hw hf
  rw [hm, expanded, records_volume] at he
  refine ⟨u', n, hu, ?_, he⟩
  simp only [hm, selectors, List.length_map, List.length_range] at hn
  rw [← records_volume]
  linarith

/-- Pad compact stock from the record selectors, keeping the expanded mask for later gathers. -/
theorem pad_exec {T Q A : ℕ} {P U : Type} (body : P → Pr P T Q A U)
    {labels width ts tm dst mask src out : Fin T}
    (hr : [labels,width,ts,tm,dst,mask].Nodup) (hs : GSRegs src mask ts tm dst out)
    (v : Descriptor) (m w : ℕ) (bit : ℕ → Bool) (u : HS T Q A U) (S : Stacks T A)
    (hl : S.R labels = (selectors m w (records v)).map bitSymbol)
    (hw : (S.R width).length = payload v) (hf : ∀ k ∈ [ts,tm,dst], S.R k = [])
    (hm : S.R mask = [])
    (hx : S.R src = (((List.range (volume prime v)).filter (live m w (payload v))).map bit).map bitSymbol) :
    let xs := List.range (volume prime v)
    let keep := live m w (payload v)
    let R := Function.update S.R mask ((xs.map keep).map bitSymbol)
    ∃ u' n, u'.user = u.user ∧ n ≤ 14*volume prime v + 10*records v + 14 ∧
      Exec body (.seq (expandMask labels width ts tm dst mask symBit) (spread src mask ts tm dst out))
        (mk u S) n (mk u' { S with R := Function.update R out ((xs.map (fun i => bitSymbol (if keep i then bit i else false))) ++ S.R out) }) := by
  obtain ⟨u₁, n₁, hu₁, hn₁, he₁⟩ := expand_exec body hr v m w u S hl hw hf
  simp only [hm, List.append_nil] at he₁
  have hregs := hs
  unfold GSRegs at hregs
  regs_ne hregs
  let S₁ : Stacks T A := { S with R := Function.update S.R mask (((List.range (volume prime v)).map (live m w (payload v))).map bitSymbol) }
  obtain ⟨u₂, n₂, hu₂, hn₂, he₂⟩ := spread_stock body hs v m w bit u₁ S₁
    ⟨Function.update_self .., by simpa [S₁, ‹src ≠ mask›] using hx⟩
    (by simpa [S₁, Ne.symm ‹mask ≠ ts›] using hf ts (by simp))
    (by simpa [S₁, Ne.symm ‹mask ≠ tm›] using hf tm (by simp))
    (by simpa [S₁, Ne.symm ‹mask ≠ dst›] using hf dst (by simp))
  refine ⟨u₂, n₁+n₂, hu₂.trans hu₁, ?_, ?_⟩
  · exact (show n₁+n₂ ≤ _ by omega)
  · simpa only [S₁, Function.update_of_ne (Ne.symm ‹mask ≠ out›)] using Exec.seq he₁ he₂

end
end IntegerMultBounds.MathlibTM2.Cover.LabelMask
