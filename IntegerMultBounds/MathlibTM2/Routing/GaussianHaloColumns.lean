module

public import IntegerMultBounds.MathlibTM2.Routing.HaloRecordLayout
public import IntegerMultBounds.MathlibTM2.Routing.GeneratedPeriodicHalo

/-! Identify actual emitted coefficient bytes with windows of complete
spectator columns. Their rectangular shape is derived from the source fiber. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing.GaussianHaloColumns
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast HaloIntervalLayout
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 117 Q A U}

theorem extended_bytes (A w B H : ℕ) (cols : List (List GaussianInt))
    (hB : ∀ col ∈ cols, col.length = B) :
    PeriodicHaloStream.extended A w (H*B) cols.flatten =
      (HaloRecordLayout.extended H cols).flatMap (cstream A w) := by
  have he := HaloRecordLayout.extended_flatMap (fun col : List GaussianInt => col) B cols hB H
  simp only [List.flatMap_id'] at he
  change cstream A w (HaloRecordLayout.extended (H*B) cols.flatten) = _
  rw [he]
  change ((HaloRecordLayout.extended H cols).flatten).flatMap (csyms A w) =
    (HaloRecordLayout.extended H cols).flatMap (fun col => col.flatMap (csyms A w))
  simp only [List.flatten_eq_flatMap,List.flatMap_assoc,id_eq]

theorem emitted_bytes (A w B L H N : ℕ) (cols : List (List GaussianInt))
    (hB : ∀ col ∈ cols, col.length = B) :
    (List.range' 0 N).flatMap (fun j => slice (PeriodicHaloStream.extended A w (H*B) cols.flatten)
      (j*((L*B)*w)) ((j+1)*((L*B)*w)+2*((H*B)*w))) =
      (HaloRecordLayout.windows L H N cols).flatMap (fun window => window.flatMap (cstream A w)) := by
  rw [extended_bytes A w B H cols hB]
  have hencode : ∀ col ∈ cols, (cstream A w col).length = B*w := by
    intro col hc
    simp [hB col hc]
  have hh := HaloRecordLayout.emitted_flatMap (cstream A w) (B*w) cols hencode L H N
  rw [HaloRecordLayout.extended_flatMap (cstream A w) (B*w) cols hencode] at hh
  simpa only [Nat.mul_assoc] using hh

theorem column_windows_shape (B L H N : ℕ) (cols : List (List GaussianInt))
    (hlen : cols.length = N*L) (hH : H ≤ cols.length) (hB : ∀ col ∈ cols, col.length = B) :
    (∀ window ∈ HaloRecordLayout.windows L H N cols, window.length = L+2*H) ∧
      (∀ window ∈ HaloRecordLayout.windows L H N cols, ∀ col ∈ window, col.length = B) := by
  refine ⟨HaloRecordLayout.windows_row_length L H N cols hlen hH,?_⟩
  intro window hw col hc
  exact hB col (HaloRecordLayout.mem_windows hw hc)

theorem emit_columns_exec (w V B L H N : ℕ) (cols : List (List GaussianInt))
    (hN : 0 < N) (hgap : 2*H ≤ L) (hlen : cols.length = N*L)
    (hB : ∀ col ∈ cols, col.length = B) (hfit : (N*L+2*H)*(B*w) < 2^V)
    (hwide : N+2 < 2^V) (hA : 4 ≤ A) (tail : List (Fin (A+4)))
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hM : (S.R 31).length = cols.flatten.length) (hH : (S.R 32).length = H*B) (hw : (S.R 33).length = w)
    (hV : (S.R 115).length = V) (hNb : S.R 97 = binSyms V N)
    (hLb : S.R 98 = binSyms V (L*(B*w))) (hBb : S.R 100 = binSyms V (2*(H*(B*w)))) (hz : S.R 116 = [])
    (hsrc : S.R 39 = cstream A w cols.flatten++tail)
    (hblank : ∀ i : Fin 117, i.val < 31 ∨ i ∈ [34,35,36,96,95,94,37,38,40,41,42,93,92,114] → S.R i = []) :
    ∃ vf n, vf.user = v.user ∧ n ≤ GeneratedPeriodicHalo.cost (N*L*B) (H*B) w N V (L*B) ∧
      Exec body GeneratedPeriodicHalo.emit (mk v S) n (mk vf {S with R := (Function.update S.R 39
        ((HaloRecordLayout.windows L H N cols).flatMap (fun window => window.flatMap (cstream A w))++tail))}) := by
  have hvolume : cols.flatten.length = N*(L*B) := by
    have hh := HaloRecordLayout.length_flatMap (fun col : List GaussianInt => col) B cols hB
    simpa only [List.flatMap_id',hlen,Nat.mul_assoc] using hh
  obtain ⟨vf,n,hu,hn,he⟩ := GeneratedPeriodicHalo.emit_exec (body := body) w V (L*B) (H*B) N
    cols.flatten hN (by nlinarith only [Nat.mul_le_mul_right B hgap]) hvolume
    (by convert hfit using 1; ring) hwide hA tail v S hM hH hw hV hNb
    (by simpa only [Nat.mul_assoc] using hLb) (by simpa only [Nat.mul_assoc] using hBb) hz hsrc hblank
  refine ⟨vf,n,hu,?_,?_⟩
  · simpa only [hvolume,Nat.mul_assoc] using hn
  · simpa only [emitted_bytes A w B L H N cols hB] using he

end IntegerMultBounds.MathlibTM2.Routing.GaussianHaloColumns
