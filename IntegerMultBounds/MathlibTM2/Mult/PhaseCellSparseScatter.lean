module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellScatterSchedule

/-! Sparse publication is a structural list theorem, independent of the
coordinate type, matrix, interval origin, and numerical representation. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

theorem scatterRows_sparse {α : Type*} (zero : α) (ys xs : List α) (ps : List ℕ)
    (hdis : ps.Pairwise (fun p q => p+1 ≤ q))
    (hfit : ∀ p ∈ ps, p < ys.length) (hx : xs.length = ps.length)
    (hvalue : ∀ n (hn : n < ps.length),
      xs[n]'(by omega) = ys[ps[n]]'(hfit _ (List.getElem_mem hn)))
    (hoff : ∀ i (hi : i < ys.length), i ∉ ps → ys[i] = zero) :
    scatterRows 1 (List.replicate ys.length zero) xs (windowGaps 1 0 ps) = ys := by
  let E := List.replicate ys.length zero
  have hf : ∀ p ∈ ps, p+1 ≤ E.length := by
    intro p hp
    simpa [E] using Nat.succ_le_of_lt (hfit p hp)
  have hxs : ps.length*1 ≤ xs.length := by omega
  have hfits := windowGaps_fits 1 0 ps E (fun _ _ => Nat.zero_le _) hdis hf
  have hlen := length_scatterRows 1 E xs (windowGaps 1 0 ps)
    (by simpa using hfits) (by simpa using hxs)
  apply List.ext_getElem (by simpa [E] using hlen)
  intro i hi hj
  by_cases hm : i ∈ ps
  · obtain ⟨n,hn,he⟩ := List.getElem_of_mem hm
    have hnX : n < xs.length := by omega
    have hw := scatterRows_absolute 1 ps E xs hdis hf hxs n hn
    rw [he,Nat.mul_one,List.take_one_drop_eq_of_lt_length hi,
      List.take_one_drop_eq_of_lt_length hnX] at hw
    have hv := hvalue n hn
    simp only [List.get_eq_getElem] at hw
    exact (List.cons.inj hw).1.trans (by simpa only [he] using hv)
  · have hsep : ∀ n (hn : n < ps.length), i < ps[n] ∨ ps[n]+1 ≤ i := by
      intro n hn
      have hne : i ≠ ps[n] := by intro he; exact hm (he ▸ List.getElem_mem hn)
      omega
    have he := scatterRows_absolute_off 1 ps E xs hdis hf hxs i hsep
    rw [List.getElem?_eq_getElem hi,List.getElem?_eq_getElem (by simpa [E] using hj)] at he
    have hv := Option.some.inj he
    simpa [E,hoff i hj hm] using hv

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
