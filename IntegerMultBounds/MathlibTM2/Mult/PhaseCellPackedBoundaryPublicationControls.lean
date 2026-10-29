module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedBoundaryPublicationSchedule
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPublicationControls
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPublicationSchedule

/-! Convert ascending boundary origin advances into the actual scatter controls. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 224 Q A U}

def packedBoundaryPublicationControls : Pr P 224 Q A U :=
  publicationControls 116 184 206 217 201 160 223 208 220 211 215

theorem packedBoundaryPublicationControls_nonempty_exec (s : ℕ) [NeZero s] (B : Finset (ZMod s))
    (a L w : ℕ) (hinside : ∀ i ∈ B, a ≤ i.val ∧ i.val < a+L) (hwpos : 1 ≤ w) (hB : 0 < B.card)
    (borrowed : List (Fin (A+4))) (v : HS 224 Q A U) (S : Stacks 224 A)
    (hc : S.R 116 = List.replicate B.card tick)
    (hs : S.R 206 = gatherControls A (originAdvances w 0 (packedBoundaryOrigins B a)++[0])++borrowed)
    (hw : (S.R 160).length = w)
    (hz : ∀ i ∈ ([184,217,201,223,208,211,215] : List (Fin 224)), S.R i = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ 33*L*w+21 ∧
      Exec body packedBoundaryPublicationControls (mk v S) n
        (mk v' {S with R := (Function.update S.R 220
          (gatherControls A (packedBoundaryGaps B a w)++S.R 220))}) := by
  cases he : packedBoundaryOrigins B a with
  | nil =>
    have hh : (packedBoundaryOrigins B a).length = B.card := by simp [packedBoundaryOrigins,bOrder_length]
    rw [he] at hh
    simp only [List.length_nil] at hh
    omega
  | cons p ps =>
    let ds := originAdvances w p ps
    have hlen : B.card = ps.length+1 := by
      have hh : (packedBoundaryOrigins B a).length = B.card := by simp [packedBoundaryOrigins,bOrder_length]
      simpa only [he,List.length_cons] using hh.symm
    have hds : ds.length = ps.length := originAdvances_length w p ps
    have hadv : originAdvances w 0 (packedBoundaryOrigins B a) = p*w::ds := by simp [he,originAdvances,ds]
    have hdis : (p::ps).Pairwise (fun p q => p+1 ≤ q) := by rw [← he]; exact packedBoundaryOrigins_disjoint B a L hinside
    have hLd : ∀ d ∈ ds, w ≤ d := by simpa only [Nat.one_mul] using originAdvances_lower 1 w p ps hdis
    have hsrc : S.R 206 = gatherControls A (p*w::ds)++([blank]++borrowed) := by
      rw [hs,hadv,gatherControls_append]
      simp [gatherControls,List.append_assoc]
    obtain ⟨v',n,hu,hn,hx⟩ := publicationControls_exec (body := body)
      (count := 116) (savedCount := 184) (control := 206) (savedControl := 217) (counter := 201)
      (window := 160) (zero := 223) (acc := 208) (dst := 220) (trash := 211) (tmp := 215)
      (by decide) w (p*w) ds hLd tick (List.replicate ps.length tick) ([blank]++borrowed)
      (by simp [hds]) v S (by simpa [hlen,List.replicate_succ] using hc) hsrc hw hz
    have hgaps : p*w::ds.map (·-w) = packedBoundaryGaps B a w := by
      have hh := packedBoundaryPublicationGaps B a w
      rw [hadv] at hh
      exact hh
    refine ⟨v',n,hu,?_,by simpa only [hgaps,packedBoundaryPublicationControls] using hx⟩
    have hvol := packedBoundaryOriginAdvances_volume B a L w hinside
    rw [hadv,List.sum_cons] at hvol
    have hnB : B.card ≤ L := by
      have hh := scatterVolume_le 1 (List.replicate L ()) (packedBoundaryGaps B a 1)
        (packedBoundaryGaps_fits B a L 1 hinside _ (by simp))
      simp only [scatterVolume,packedBoundaryGaps_length,Nat.mul_one,List.length_replicate] at hh
      omega
    have hsw : L ≤ L*w := by simpa using Nat.mul_le_mul_left L hwpos
    rw [hds] at hn
    rw [hlen] at hnB
    nlinarith only [hn,hvol,hnB,hsw]

/-- The same converter also handles an empty boundary without reading a packet. -/
def conditionalPackedBoundaryPublicationControls : Pr P 224 Q A U :=
  .seq (.act (peekR 116)) (.cond (·.flag) packedBoundaryPublicationControls (.act .done))

theorem conditionalPackedBoundaryPublicationControls_exec (s : ℕ) [NeZero s] (B : Finset (ZMod s))
    (a L w : ℕ) (hinside : ∀ i ∈ B, a ≤ i.val ∧ i.val < a+L) (hwpos : 1 ≤ w) (borrowed : List (Fin (A+4))) (v : HS 224 Q A U) (S : Stacks 224 A)
    (hc : S.R 116 = List.replicate B.card tick)
    (hs : S.R 206 = gatherControls A (originAdvances w 0 (packedBoundaryOrigins B a)++[0])++borrowed)
    (hw : (S.R 160).length = w)
    (hz : ∀ i ∈ ([184,217,201,223,208,211,215] : List (Fin 224)), S.R i = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ 33*L*w+23 ∧
      Exec body conditionalPackedBoundaryPublicationControls (mk v S) n
        (mk v' {S with R := (Function.update S.R 220
          (gatherControls A (packedBoundaryGaps B a w)++S.R 220))}) := by
  let v₀ : HS 224 Q A U := {v with flag := (S.R 116).head?.isSome}
  have hpeek : Exec body (.act (peekR 116)) (mk v S) 1 (mk v₀ S) := by
    simpa only [peekR_run,v₀] using Exec.act (body := body) (peekR 116) (mk v S)
  by_cases hB : B.card = 0
  · have hflag : v₀.flag = false := by simp [v₀,hc,hB]
    have hgaps : packedBoundaryGaps B a w = [] := by
      apply List.eq_nil_of_length_eq_zero
      rw [packedBoundaryGaps_length,hB]
    have hdone := Exec.act (body := body) (.done : Act 224 Q A U) (mk v₀ S)
    have he := Exec.seq hpeek (Exec.cond_false (p := packedBoundaryPublicationControls)
      (by change v₀.flag = false; exact hflag) hdone)
    refine ⟨v₀,3,rfl,by omega,?_⟩
    simpa [conditionalPackedBoundaryPublicationControls,hgaps,gatherControls] using he
  · have hBpos : 0 < B.card := by omega
    obtain ⟨n,hn⟩ := Nat.exists_eq_succ_of_ne_zero hB
    have hflag : v₀.flag = true := by simp [v₀,hc,hn,List.replicate_succ]
    obtain ⟨v',n',hu,hn',he⟩ := packedBoundaryPublicationControls_nonempty_exec (body := body)
      s B a L w hinside hwpos hBpos borrowed v₀ S hc hs hw hz
    refine ⟨v',n'+2,hu,by omega,?_⟩
    exact (Exec.seq hpeek (Exec.cond_true (by change v₀.flag = true; exact hflag) he)).cast (by omega) rfl

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
