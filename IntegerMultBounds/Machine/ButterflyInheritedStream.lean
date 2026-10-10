import IntegerMultBounds.Machine.ButterflyAxisDecoded

/-! Literal signed butterflies at an inherited denominator and numerator
budget, independently of the metadata controlling the fixed stored width. -/
namespace IntegerMultBounds.Machine.ButterflyInheritedStream
noncomputable section
open Networks.GaussianPrecision ButterflyStreamSemantics ButterflyStreamData

private def context (x : Coefficient) : DelimitedRadixRecord.Context 2 :=
  ⟨fun _ => 0,0,[],[],x.1,x.2⟩

theorem result_exact (a b : Coefficient) (half n M : ℕ)
    (ha : a.1.length=half+1 ∧ a.2.length=half+1)
    (hb : b.1.length=half+1 ∧ b.2.length=half+1)
    (hga : BoundedGrid n M (decode half n a))
    (hgb : BoundedGrid n M (decode half n b)) (hg : 4*M<2^half) :
    decode half (n+1) (result a b 0)=
      (decode half n a+decode half n b+Complex.I*(decode half n a-decode half n b))/2 ∧
    decode half (n+1) (result a b 1)=
      (decode half n a+decode half n b-Complex.I*(decode half n a-decode half n b))/2 := by
  have h0 := ButterflyGuard.represented_bound
    (ButterflySigned.signedValue half a.1) (ButterflySigned.signedValue half a.2) n M hga
  have h1 := ButterflyGuard.represented_bound
    (ButterflySigned.signedValue half b.1) (ButterflySigned.signedValue half b.2) n M hgb
  exact ButterflySigned.words_butterfly
    (ButterflyRecordRead.components (context a) (context b)) half n
    (ButterflyRecord.component_width (context a) (context b) (half+1) ha hb) (M:ℤ)
    (by intro i; fin_cases i
        · exact h0.1
        · exact h0.2
        · exact h1.1
        · exact h1.2)
    (by exact_mod_cast hg)

theorem result_decode (a b : Coefficient) (half n M : ℕ)
    (ha : a.1.length=half+1 ∧ a.2.length=half+1)
    (hb : b.1.length=half+1 ∧ b.2.length=half+1)
    (hga : BoundedGrid n M (decode half n a))
    (hgb : BoundedGrid n M (decode half n b)) (hg : 4*M<2^half) (j : Fin 2) :
    decode half (n+1) (result a b j)=
      ButterflyAxisDecoded.butterfly j (decode half n a) (decode half n b) := by
  have h := result_exact a b half n M ha hb hga hgb hg
  fin_cases j
  · simpa [ButterflyAxisDecoded.butterfly] using h.1
  · simpa [ButterflyAxisDecoded.butterfly] using h.2

theorem result_grid (a b : Coefficient) (half n M : ℕ)
    (ha : a.1.length=half+1 ∧ a.2.length=half+1)
    (hb : b.1.length=half+1 ∧ b.2.length=half+1)
    (hga : BoundedGrid n M (decode half n a))
    (hgb : BoundedGrid n M (decode half n b)) (hg : 4*M<2^half) (j : Fin 2) :
    BoundedGrid (n+1) (4*M) (decode half (n+1) (result a b j)) := by
  have h := result_exact a b half n M ha hb hga hgb hg
  have hp := bounded_half (bounded_add (bounded_add hga hgb) (bounded_I_mul (bounded_sub hga hgb)))
  have hm := bounded_half (bounded_sub (bounded_add hga hgb) (bounded_I_mul (bounded_sub hga hgb)))
  have he : M+M+(M+M)=4*M := by omega
  fin_cases j
  · apply (congrArg (BoundedGrid (n+1) (4*M)) h.1).mpr
    simpa only [he] using hp
  · apply (congrArg (BoundedGrid (n+1) (4*M)) h.2).mpr
    simpa only [he] using hm

end
end IntegerMultBounds.Machine.ButterflyInheritedStream
