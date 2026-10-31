module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPublicationWindows
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellEncodedHaloPublication
public import IntegerMultBounds.NLogN.PhaseCellHaloBoundary

/-! A publication sweep preserves the packed reader on each destination core.
Accuracy transfers without accumulating an error for every core. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

theorem windowPublication_word {A s L : ℕ} (windows : PublicationWindows s L) (w : ℕ)
    (rows : List (List GaussianInt)) (hcount : rows.length = windows.origins.length)
    (hrows : ∀ row ∈ rows, row.length = L)
    (E : List (Fin (A+4))) (hE : s*w ≤ E.length)
    (n : ℕ) (hn : n < windows.origins.length) (i : ℕ) (hi : i < L) :
    ((scatterRows (L*w) E (cstream A w rows.flatten) (windows.gaps w)).drop
      ((windows.origins[n]+i)*w)).take w =
      ((cstream A w (rows[n]'(by omega))).drop (i*w)).take w := by
  have hx : (windows.symbolOrigins w).length*(L*w) ≤ (cstream A w rows.flatten).length := by
    simp only [PublicationWindows.symbolOrigins,List.length_map,length_cstream,
      length_flatten_const rows hrows,hcount,Nat.mul_assoc]
    exact le_rfl
  have hf : ∀ p ∈ windows.symbolOrigins w, p+L*w ≤ E.length := by
    intro p hp
    change p ∈ windows.origins.map (·*w) at hp
    obtain ⟨origin,horigin,he⟩ := List.mem_map.mp hp
    subst p
    have hh := Nat.mul_le_mul_right w (windows.fits origin horigin)
    rw [Nat.add_mul] at hh
    exact hh.trans hE
  have he := scatterRows_absolute (L*w) (windows.symbolOrigins w) E (cstream A w rows.flatten)
    (windows.symbolOrigins_disjoint w) hf hx n (by simpa [PublicationWindows.symbolOrigins] using hn)
  have hcut : w ≤ L*w-i*w := by
    have hh := Nat.mul_le_mul_right w (Nat.succ_le_of_lt hi)
    simp only [Nat.succ_mul] at hh
    omega
  have hh := congrArg (fun ys : List (Fin (A+4)) => (ys.drop (i*w)).take w) he
  simp only [PublicationWindows.symbolOrigins,List.getElem_map,List.drop_take,List.take_take,
    Nat.min_eq_left hcut,List.drop_drop,←Nat.add_mul] at hh
  change ((scatterRows (L*w) E (cstream A w rows.flatten) (windows.gaps w)).drop
    ((windows.origins[n]+i)*w)).take w = _ at hh
  rw [hh]
  simpa only [List.append_nil,Nat.add_mul,Nat.mul_assoc] using cstream_rows_word (A := A) w L rows hrows [] n i (by omega) hi

theorem windowPublication_errorOn {A s L : ℕ} [NeZero s]
    (windows : PublicationWindows s L) (q w : ℕ)
    (rows : List (List GaussianInt)) (hcount : rows.length = windows.origins.length)
    (hrows : ∀ row ∈ rows, row.length = L)
    (E : List (Fin (A+4))) (hE : s*w ≤ E.length)
    (x : ZMod s → ℂ) (error : ℝ)
    (n : ℕ) (hn : n < windows.origins.length)
    (hgood : PhaseCellInterface.ErrorOn
      (haloVertices s windows.origins[n] (windows.origins[n]+L))
      (packedIntervalRead q w windows.origins[n] (cstream A w (rows[n]'(by omega)))) x error) :
    PhaseCellInterface.ErrorOn (haloVertices s windows.origins[n] (windows.origins[n]+L))
      (pairedCellRead q w (scatterRows (L*w) E (cstream A w rows.flatten) (windows.gaps w))) x error := by
  intro j hj
  obtain ⟨hlo,hhi⟩ := (mem_haloVertices _ _ j).mp hj
  have he := windowPublication_word windows w rows hcount hrows E hE n hn
    (j.val-windows.origins[n]) (by omega)
  rw [Nat.add_sub_of_le hlo] at he
  have hg := hgood j hj
  simpa only [pairedCellRead,packedIntervalRead,he] using hg

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
