module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellAdvanceControls
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedAdvanceBank
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedBoundaryPublicationSchedule

/-! Generate the complete delimited sweep controls, restoring the binary
origin stream and unary batch count. Only the control destination and bounded
table state change; all conversion scratch is released. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {U P : Type} {body : P → Pr P 117 Q A U}

theorem packedBoundaryAdvanceControls_exec {W e w s : ℕ} [NeZero s] (he : e ≤ W)
    (B : Finset (ZMod s)) (a L : ℕ)
    (hB : ∀ i ∈ B, a ≤ i.val ∧ i.val < a+L)
    (hLW : L < 2^W) (hLwW : L*w < 2^W)
    (st : TblSt 4 A) (hp : st.val 1 = 0) (hw : st.val 2 = w) (hfit : ∀ i, st.val i < 2^W)
    (cs suffix : List (Fin (A+4))) (hlen : cs.length = (packedBoundaryOrigins B a).length)
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hS : tblHolds advanceReg S (tblRho W (List.replicate W tick) (List.replicate e tick) st))
    (hc : S.R 116 = cs) (hsrc : S.R 109 = (packedBoundaryOrigins B a).flatMap (binSyms W) ++ suffix)
    (h88 : S.R 88 = []) (h89 : S.R 89 = []) (h90 : S.R 90 = []) :
    ∃ st' v' S' n, st'.val 2 = w ∧ st'.acc = st.acc ∧ (∀ i, st'.val i < 2^W) ∧
      v'.user = v.user ∧
      n ≤ B.card*(3*tblC W e+29*W+30)+8*(L*w)+11 ∧
      Exec body originAdvanceControls (mk v S) n (mk v' S') ∧
      tblHolds advanceReg S' (tblRho W (List.replicate W tick) (List.replicate e tick) st') ∧
      S'.R 91 = gatherControls A (originAdvances w 0 (packedBoundaryOrigins B a) ++ [0]) ++ S.R 91 ∧
      S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧
      ∀ k, k ≠ 91 → (∀ r, advanceReg r ≠ k) → S'.R k = S.R k := by
  have ho : (0::packedBoundaryOrigins B a).Pairwise (· ≤ ·) :=
    List.pairwise_cons.mpr ⟨by simp,
      (packedBoundaryOrigins_disjoint B a L hB).imp (fun h => by omega)⟩
  have hf : ∀ p ∈ packedBoundaryOrigins B a, p < L := by
    intro p hp
    have hh := packedBoundaryOrigins_fit B a L hB p hp
    omega
  obtain ⟨st',v',S',n,hw',ha,hbound,hu,hn,hex,hholds,hout,hframe⟩ :=
    originAdvanceControls_exec (body := body) he (packedBoundaryOrigins B a) ho
      (fun p hp => (hf p hp).trans hLW)
      (fun p hp => (Nat.mul_le_mul_right w (hf p hp).le).trans_lt hLwW)
      st hp hw hfit cs suffix hlen v S hS hc hsrc h88 h89 h90
  refine ⟨st',v',S',n,hw',ha,hbound,hu,?_,hex,hholds,hout,hframe⟩
  have hv := packedBoundaryOriginAdvances_volume B a L w hB
  have hl : (packedBoundaryOrigins B a).length = B.card := by
    simp [packedBoundaryOrigins,IntegerMultBounds.NLogN.PhaseCellMatrix.bOrder_length]
  rw [hl] at hn
  omega

theorem ambientBoundaryAdvanceControls_exec {W e w s : ℕ} [NeZero s] (he : e ≤ W)
    (B : Finset (ZMod s)) (a L : ℕ)
    (hB : ∀ i ∈ B, a ≤ i.val ∧ i.val < a+L)
    (hsW : s < 2^W) (hswW : s*w < 2^W)
    (st : TblSt 4 A) (hp : st.val 1 = a) (hw : st.val 2 = w) (hfit : ∀ i, st.val i < 2^W)
    (cs suffix : List (Fin (A+4))) (hlen : cs.length = ((IntegerMultBounds.NLogN.PhaseCellMatrix.bOrder s B).map ZMod.val).length)
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hS : tblHolds advanceReg S (tblRho W (List.replicate W tick) (List.replicate e tick) st))
    (hc : S.R 116 = cs) (hsrc : S.R 109 = ((IntegerMultBounds.NLogN.PhaseCellMatrix.bOrder s B).map ZMod.val).flatMap (binSyms W) ++ suffix)
    (h88 : S.R 88 = []) (h89 : S.R 89 = []) (h90 : S.R 90 = []) :
    ∃ st' v' S' n, st'.val 2 = w ∧ st'.acc = st.acc ∧ (∀ i, st'.val i < 2^W) ∧
      v'.user = v.user ∧
      n ≤ B.card*(3*tblC W e+29*W+30)+8*(L*w)+11 ∧
      Exec body originAdvanceControls (mk v S) n (mk v' S') ∧
      tblHolds advanceReg S' (tblRho W (List.replicate W tick) (List.replicate e tick) st') ∧
      S'.R 91 = gatherControls A (originAdvances w 0 (packedBoundaryOrigins B a) ++ [0]) ++ S.R 91 ∧
      S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧
      ∀ k, k ≠ 91 → (∀ r, advanceReg r ≠ k) → S'.R k = S.R k := by
  let origins := (IntegerMultBounds.NLogN.PhaseCellMatrix.bOrder s B).map ZMod.val
  have hbefore : ∀ p ∈ origins, a ≤ p ∧ p < s := by
    intro p hp
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hp
    have hm : i ∈ B := by
      simpa only [← List.mem_toFinset,IntegerMultBounds.NLogN.PhaseCellMatrix.bOrder_toFinset] using hi
    exact ⟨(hB i hm).1,i.val_lt⟩
  have ho : (a::origins).Pairwise (· ≤ ·) := by
    apply List.pairwise_cons.mpr
    refine ⟨fun p hp => (hbefore p hp).1,?_⟩
    rw [List.pairwise_map]
    exact (IntegerMultBounds.NLogN.PhaseCellMatrix.bOrder_val_sorted s B).imp (fun h => h.le)
  obtain ⟨st',v',S',n,hw',ha,hbound,hu,hn,hex,hholds,hout,hframe⟩ :=
    originAdvanceControls_exec (body := body) he origins ho
      (fun p hp => (hbefore p hp).2.trans hsW)
      (fun p hp => (Nat.mul_le_mul_right w (hbefore p hp).2.le).trans_lt hswW)
      st hp hw hfit cs suffix hlen v S hS hc hsrc h88 h89 h90
  have heq := packedBoundaryAdvances_from_ambient B a L w hB
  change originAdvances w a origins = _ at heq
  rw [heq] at hn hout
  refine ⟨st',v',S',n,hw',ha,hbound,hu,?_,hex,hholds,hout,hframe⟩
  have hv := packedBoundaryOriginAdvances_volume B a L w hB
  have hl : origins.length = B.card := by
    simp [origins,IntegerMultBounds.NLogN.PhaseCellMatrix.bOrder_length]
  rw [hl] at hn
  omega


theorem initializedBoundaryAdvanceControls_exec {V w s : ℕ} [NeZero s]
    (B : Finset (ZMod s)) (a L : ℕ)
    (hB : ∀ i ∈ B, a ≤ i.val ∧ i.val < a+L)
    (ha : a < 2^V) (hw : w < 2^V) (hs : s < 2^V) (hsw : s*w < 2^V)
    (cs suffix : List (Fin (A+4)))
    (hlen : cs.length = ((IntegerMultBounds.NLogN.PhaseCellMatrix.bOrder s B).map ZMod.val).length)
    (v : HS 117 Q A U) (S : Stacks 117 A) (hV : (S.R 115).length = V)
    (hmeta : ∀ i, S.R (packedAdvanceSource i) = binSyms V (packedAdvanceValues a w (packedAdvanceSource i)))
    (hblank : ∀ r, S.R (advanceReg r) = []) (hc : S.R 116 = cs)
    (hsrc : S.R 109 = ((IntegerMultBounds.NLogN.PhaseCellMatrix.bOrder s B).map ZMod.val).flatMap (binSyms V)++suffix)
    (h88 : S.R 88 = []) (h89 : S.R 89 = []) (h90 : S.R 90 = []) :
    ∃ v' S' n, v'.user = v.user ∧
      n ≤ 40*V+41+(B.card*(3*tblC V V+29*V+30)+8*(L*w)+11) ∧
      Exec body (.seq (chirpBankLoad advanceReg packedAdvanceSource 115 115) originAdvanceControls)
        (mk v S) n (mk v' S') ∧
      S'.R 91 = gatherControls A (originAdvances w 0 (packedBoundaryOrigins B a)++[0])++S.R 91 ∧
      (∃ values : Fin 4 → ℕ, tblHolds advanceReg S'
        (tblRho V (List.replicate V tick) (List.replicate V tick) ⟨values,[]⟩)) ∧
      S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧
      ∀ k : Fin 117, 19 ≤ k.val → k ≠ 91 → S'.R k = S.R k := by
  obtain ⟨v₁,hu₁,he₁,hh,hframe⟩ := packedAdvanceBank_exec V a w ha hw v S hV hmeta hblank
  let S₁ : Stacks 117 A := {S with R := chirpBankLoadR advanceReg packedAdvanceSource V V (packedAdvanceValues a w) S.R}
  have hf (k : Fin 117) (hk : 19 ≤ k.val) : S₁.R k = S.R k := hframe k hk
  obtain ⟨st',v₂,S₂,n,hw',ha',hb',hu₂,hn,he₂,hh₂,hout,hrest⟩ :=
    ambientBoundaryAdvanceControls_exec (body := body) le_rfl B a L hB hs hsw
      ⟨fun i => packedAdvanceValues a w (packedAdvanceSource i),[]⟩
      (packedAdvanceOrigin a w) (packedAdvanceWordWidth a w) (packedAdvanceBank_bounded V a w ha hw)
      cs suffix hlen v₁ S₁ hh
      (by rw [hf 116 (by decide)]; exact hc)
      (by rw [hf 109 (by decide)]; exact hsrc)
      (by rw [hf 88 (by decide)]; exact h88)
      (by rw [hf 89 (by decide)]; exact h89)
      (by rw [hf 90 (by decide)]; exact h90)
  refine ⟨v₂,S₂,40*V+41+n,hu₂.trans hu₁,Nat.add_le_add_left hn _,
    Exec.seq he₁ he₂,by simpa only [hf 91 (by decide)] using hout,
    ⟨st'.val,?_⟩,hrest.1,hrest.2.1,hrest.2.2.1,?_⟩
  · have heq : st' = ⟨st'.val,[]⟩ := by
      cases st'
      simp_all
    rw [← heq]
    exact hh₂
  · intro k hk hk91
    apply (hrest.2.2.2 k hk91 ?_).trans (hf k hk)
    intro r he
    have hr := advanceReg_range r
    rw [he] at hr
    omega

theorem releasedBoundaryAdvanceControls_exec {V w s : ℕ} [NeZero s]
    (B : Finset (ZMod s)) (a L : ℕ)
    (hB : ∀ i ∈ B, a ≤ i.val ∧ i.val < a+L)
    (ha : a < 2^V) (hw : w < 2^V) (hs : s < 2^V) (hsw : s*w < 2^V)
    (cs suffix : List (Fin (A+4)))
    (hlen : cs.length = ((IntegerMultBounds.NLogN.PhaseCellMatrix.bOrder s B).map ZMod.val).length)
    (v : HS 117 Q A U) (S : Stacks 117 A) (hV : (S.R 115).length = V)
    (hmeta : ∀ i, S.R (packedAdvanceSource i) = binSyms V (packedAdvanceValues a w (packedAdvanceSource i)))
    (hblank : ∀ r, S.R (advanceReg r) = []) (hc : S.R 116 = cs)
    (hsrc : S.R 109 = ((IntegerMultBounds.NLogN.PhaseCellMatrix.bOrder s B).map ZMod.val).flatMap (binSyms V)++suffix)
    (h88 : S.R 88 = []) (h89 : S.R 89 = []) (h90 : S.R 90 = []) :
    ∃ v' S' n, v'.user = v.user ∧
      n ≤ 40*V+41+(B.card*(3*tblC V V+29*V+30)+8*(L*w)+11)+(38*V+39) ∧
      Exec body (.seq (.seq (chirpBankLoad advanceReg packedAdvanceSource 115 115) originAdvanceControls) releaseAdvanceBank)
        (mk v S) n (mk v' S') ∧
      S'.R 91 = gatherControls A (originAdvances w 0 (packedBoundaryOrigins B a)++[0])++S.R 91 ∧
      (∀ k : Fin 117, k.val < 19 → S'.R k = []) ∧
      S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧
      ∀ k : Fin 117, 19 ≤ k.val → k ≠ 91 → S'.R k = S.R k := by
  obtain ⟨v₁,S₁,n₁,hu₁,hn₁,he₁,hout,⟨values,hh⟩,hi,ho,hl,hframe⟩ :=
    initializedBoundaryAdvanceControls_exec (body := body) B a L hB ha hw hs hsw
      cs suffix hlen v S hV hmeta hblank hc hsrc h88 h89 h90
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := releaseAdvanceBank_exec V values v₁ S₁ hh
  refine ⟨v₂,_,n₁+n₂,hu₂.trans hu₁,by omega,Exec.seq he₁ he₂,?_,?_,hi,ho,hl,?_⟩
  · simpa using hout
  · intro k hk
    simp [hk]
  · intro k hk hk91
    simpa [show ¬ k.val < 19 by omega] using hframe k hk hk91

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
