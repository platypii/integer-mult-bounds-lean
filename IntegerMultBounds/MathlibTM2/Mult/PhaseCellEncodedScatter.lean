module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellEncodedStream
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHaloScatterSchedule

/-! Aligned publication preserves the existing integer-word encoding. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

theorem cstream_take (A w n : ℕ) (xs : List GaussianInt) :
    (cstream A w xs).take (n*w) = cstream A w (xs.take n) := by
  induction n generalizing xs with
  | zero => simp
  | succ n ih =>
    cases xs with
    | nil => simp
    | cons x xs =>
      rw [cstream_cons,Nat.succ_mul,List.take_append,
        List.take_of_length_le (by simp)]
      have hlen : (csyms A w x).length = w := by simp
      simpa only [hlen,Nat.add_sub_cancel,List.take_succ_cons,cstream_cons] using
        congrArg (fun ys => csyms A w x++ys) (ih xs)

theorem cstream_drop (A w n : ℕ) (xs : List GaussianInt) :
    (cstream A w xs).drop (n*w) = cstream A w (xs.drop n) := by
  induction n generalizing xs with
  | zero => simp
  | succ n ih =>
    cases xs with
    | nil => simp
    | cons x xs =>
      rw [cstream_cons,Nat.succ_mul,List.drop_append,
        List.drop_eq_nil_of_le (by simp)]
      have hlen : (csyms A w x).length = w := by simp
      simpa only [hlen,Nat.add_sub_cancel,List.nil_append,List.drop_succ_cons] using ih xs

theorem scatterRows_source_suffix {α : Type*} (L : ℕ) (E X tail : List α) (ds : List ℕ)
    (hX : ds.length*L ≤ X.length) : scatterRows L E (X++tail) ds = scatterRows L E X ds := by
  induction ds generalizing E X with
  | nil => simp [scatterRows,scatterPrefix]
  | cons d ds ih =>
    have hL : L ≤ X.length := by simp only [List.length_cons,Nat.add_mul,Nat.one_mul] at hX; omega
    rw [scatterRows_cons,scatterRows_cons,List.take_append_of_le_length hL,
      List.drop_append_of_le_length hL,ih]
    simp only [List.length_drop,List.length_cons,Nat.add_mul,Nat.one_mul] at *
    omega

theorem scatterRows_cstream (A w L : ℕ) (E X : List GaussianInt) (ds : List ℕ) :
    scatterRows (L*w) (cstream A w E) (cstream A w X) (ds.map (fun d => d*w)) =
      cstream A w (scatterRows L E X ds) := by
  induction ds generalizing E X with
  | nil => simp [scatterRows,scatterPrefix]
  | cons d ds ih =>
    simp only [List.map_cons,scatterRows_cons,← Nat.add_mul,cstream_take,cstream_drop,ih,cstream_append]

theorem windowGaps_scale (L cursor w : ℕ) (ps : List ℕ) :
    windowGaps (L*w) (cursor*w) (ps.map (fun p => p*w)) =
      (windowGaps L cursor ps).map (fun d => d*w) := by
  induction ps generalizing cursor with
  | nil => rfl
  | cons p ps ih => simp [windowGaps,← Nat.sub_mul,← Nat.add_mul,ih]

theorem haloScatterGaps_scale (s t band a b L w : ℕ) :
    haloScatterGaps s t band a b L w = (haloScatterGaps s t band a b L 1).map (fun d => d*w) := by
  simpa [haloScatterGaps,haloSymbolOrigins,
    List.map_map,Function.comp_def] using
    windowGaps_scale L 0 w (IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry.haloOrigins s t band a b L)

theorem haloScatterRows_encoded {A w : ℕ} (s t band a b L : ℕ)
    (E tail : List (Fin (A+4))) (X : EncodedStream A w)
    (hE : ∃ zs : List GaussianInt, E = cstream A w zs)
    (hX : X.val.length = (IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry.haloLengthGroup s t band a b L).length*L*w) :
    ∃ zs : List GaussianInt,
      scatterRows (L*w) E (X.val++tail) (haloScatterGaps s t band a b L w) = cstream A w zs := by
  rw [scatterRows_source_suffix (L*w) E X.val tail _ (by simp [hX,Nat.mul_assoc])]
  obtain ⟨es,rfl⟩ := hE
  obtain ⟨xs,hxs⟩ := X.encoded
  rw [hxs,haloScatterGaps_scale,scatterRows_cstream]
  exact ⟨_,rfl⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
