module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaPublicationData
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellOutputRows
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundedEncodedStream

/-! Convert the actual compact numerical output into publication rows by
structural splitting. No decoded row or publication execution oracle is supplied. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {A s L : ℕ}

theorem publicationReplicas_of_words (windows : PublicationWindows s L) (w : ℕ)
    (ambientRows : List (List (Fin (A+4))))
    (hambient : ∀ xs ∈ ambientRows, xs.length = s*w)
    (zs : List GaussianInt) (hlen : zs.length = ambientRows.length*(windows.origins.length*L)) :
    ∃ replicas : List (PublicationReplica A), replicas.length = ambientRows.length ∧
      replicas.map PublicationReplica.ambient = ambientRows ∧
      replicas.flatMap (PublicationReplica.input w) = cstream A w zs ∧
      ∀ r ∈ replicas, r.Valid windows w 0 := by
  induction ambientRows generalizing zs with
  | nil =>
    have hz : zs = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
    exact ⟨[],rfl,rfl,by simp [hz,cstream],by simp⟩
  | cons ambient ambientRows ih =>
    let B := windows.origins.length
    have htotal : zs.length = ambientRows.length*(B*L)+B*L := by
      simpa only [List.length_cons,Nat.succ_mul,B] using hlen
    have hp : B*L ≤ zs.length := by omega
    have htake : (zs.take (B*L)).length = B*L := by simp [List.length_take,Nat.min_eq_left hp]
    have hdrop : (zs.drop (B*L)).length = ambientRows.length*(B*L) := by
      simp only [List.length_drop]
      omega
    let rows := outputRows B L (zs.take (B*L))
    have hrows := outputRows_spec B L (zs.take (B*L)) htake
    let r : PublicationReplica A := ⟨rows,rows,ambient⟩
    have hr : r.Valid windows w 0 := by
      refine ⟨?_,?_,?_,?_,?_,?_⟩
      · exact outputRows_length B L _
      · exact hrows.2
      · exact hrows.2
      · simp [r]
      · simp [r]
      · exact hambient ambient (by simp)
    obtain ⟨replicas,hn,ha,hi,hvalid⟩ := ih
      (fun xs hx => hambient xs (by simp [hx])) (zs.drop (B*L)) hdrop
    refine ⟨r::replicas,by simp [hn],by simp [r,ha],?_,?_⟩
    · simp only [List.flatMap_cons,hi,PublicationReplica.input,r]
      rw [show rows.flatten = zs.take (B*L) from hrows.1]
      simpa only [← cstream_append] using congrArg (cstream A w) (List.take_append_drop (B*L) zs)
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hr
      · exact hvalid x hx

theorem publicationReplicas_of_encoded (windows : PublicationWindows s L) {w q e : ℕ}
    (hw : 0 < w) (xs : BoundedEncodedStream A w q e)
    (ambientRows : List (List (Fin (A+4))))
    (hambient : ∀ ys ∈ ambientRows, ys.length = s*w)
    (hlen : xs.val.length = ambientRows.length*(windows.origins.length*L)*w) :
    ∃ replicas : List (PublicationReplica A), replicas.length = ambientRows.length ∧
      replicas.map PublicationReplica.ambient = ambientRows ∧
      replicas.flatMap (PublicationReplica.input w) = xs.val ∧
      ∀ r ∈ replicas, r.Valid windows w 0 := by
  obtain ⟨zs,hzs,hbound⟩ := xs.bounded
  have hzlen : zs.length = ambientRows.length*(windows.origins.length*L) := by
    have hh : zs.length*w = ambientRows.length*(windows.origins.length*L)*w := by
      rw [hzs,length_cstream] at hlen
      exact hlen
    exact Nat.eq_of_mul_eq_mul_right hw hh
  obtain ⟨replicas,hn,ha,hi,hv⟩ := publicationReplicas_of_words windows w ambientRows hambient zs hzlen
  exact ⟨replicas,hn,ha,hi.trans hzs.symm,hv⟩

/-- Every published word is exactly the corresponding compact solver word. -/
theorem PublicationWindows.scatter_word {α : Type*} (windows : PublicationWindows s L)
    (w : ℕ) (E X : List α) (hE : s*w ≤ E.length)
    (hX : windows.origins.length*(L*w) ≤ X.length)
    (n : Fin windows.origins.length) (i : Fin L) :
    ((scatterRows (L*w) E X (windows.gaps w)).drop
      (((windows.origins[n.val]'n.isLt)+i.val)*w)).take w =
        (X.drop ((n.val*L+i.val)*w)).take w := by
  have hn : n.val < (windows.symbolOrigins w).length := by simp [PublicationWindows.symbolOrigins]
  have hx : (windows.symbolOrigins w).length*(L*w) ≤ X.length := by
    simpa only [PublicationWindows.symbolOrigins,List.length_map] using hX
  have hf : ∀ p ∈ windows.symbolOrigins w, p+L*w ≤ E.length := by
    intro p hp
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hp
    have hh := Nat.mul_le_mul_right w (windows.fits a ha)
    have hh' : a*w+L*w ≤ s*w := by simpa only [Nat.add_mul] using hh
    exact hh'.trans hE
  have he := scatterRows_absolute (L*w) (windows.symbolOrigins w) E X
    (windows.symbolOrigins_disjoint w) hf hx n.val hn
  have horigin : (windows.symbolOrigins w)[n.val]'hn = (windows.origins[n.val]'n.isLt)*w := by
    simp only [PublicationWindows.symbolOrigins,List.getElem_map]
  rw [horigin] at he
  have hcut : w ≤ L*w-i.val*w := by
    have hh := Nat.mul_le_mul_right w (Nat.succ_le_of_lt i.isLt)
    simp only [Nat.succ_mul] at hh
    omega
  have hh := congrArg (fun ys : List α => (ys.drop (i.val*w)).take w) he
  simpa only [PublicationWindows.gaps,List.drop_take,List.take_take,Nat.min_eq_left hcut,
    List.drop_drop,Nat.add_mul,Nat.mul_assoc] using hh

theorem PublicationReplica.Valid.output_word {w : ℕ} {r : PublicationReplica A}
    {windows : PublicationWindows s L} (h : r.Valid windows w 0)
    (n : Fin windows.origins.length) (i : Fin L) :
    ((r.output windows w).drop (((windows.origins[n.val]'n.isLt)+i.val)*w)).take w =
      ((r.words w).drop ((n.val*L+i.val)*w)).take w := by
  exact windows.scatter_word w r.ambient (r.words w) (by rw [h.ambientLength])
    (by rw [h.words_length]) n i

/-- Publication preserves each local error bound without a row-count factor. -/
theorem PublicationWindows.scatter_error (windows : PublicationWindows s L)
    (q w : ℕ) (E X : List (Fin (A+4))) (hE : s*w ≤ E.length)
    (hX : windows.origins.length*(L*w) ≤ X.length) (x : ℕ → ℝ) (error : ℝ)
    (hlocal : ∀ n : Fin windows.origins.length, ∀ i : Fin L,
      |(value q (decodeWord ((X.drop ((n.val*L+i.val)*w)).take w))).re-
        x ((windows.origins[n.val]'n.isLt)+i.val)| ≤ error)
    (n : Fin windows.origins.length) (i : Fin L) :
    |(value q (decodeWord (((scatterRows (L*w) E X (windows.gaps w)).drop
      (((windows.origins[n.val]'n.isLt)+i.val)*w)).take w))).re-
        x ((windows.origins[n.val]'n.isLt)+i.val)| ≤ error := by
  rw [windows.scatter_word w E X hE hX n i]
  exact hlocal n i

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
