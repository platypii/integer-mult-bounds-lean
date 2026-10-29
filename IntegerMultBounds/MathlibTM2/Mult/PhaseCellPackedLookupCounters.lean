module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedLookupCode
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellOriginRelease
public import IntegerMultBounds.MathlibTM2.Host.BinArith
public import IntegerMultBounds.MathlibTM2.Mult.ChirpUnaryCopies
public import IntegerMultBounds.MathlibTM2.Fast.TableBounds

/-! Publish the local address and ambient membership flag before releasing
the geometry table. This uses the existing recovery-counter host pattern. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

def packedLookupEmitCounters {P U : Type} {Q A : ℕ} : Pr P 117 Q A U :=
  tblUnaryCopies originReg [(3,108),(15,109)]

def packedLookupCountersFor {P U : Type} {Q A : ℕ} (code : TblCode 16) : Pr P 117 Q A U :=
  .seq (tblCompile originReg code)
    (.seq packedLookupEmitCounters releaseOriginBank)

def packedLookupCounters {P U : Type} {Q A : ℕ} (boundary : Bool) : Pr P 117 Q A U :=
  packedLookupCountersFor (packedLookupCode boundary)

theorem packedLookupEmitCounters_holds {A V : ℕ} (st : TblSt 16 A) (S : Stacks 117 A)
    (hS : tblHolds originReg S (tblRho V (List.replicate V tick) (List.replicate V tick) st)) :
    tblHolds originReg {S with R := unaryCopiesR st.val S.R [(3,108),(15,109)]}
      (tblRho V (List.replicate V tick) (List.replicate V tick) st) := by
  intro r
  have hr := originReg_range r
  have h108 : originReg r ≠ 108 := by intro he; rw [he] at hr; omega
  have h109 : originReg r ≠ 109 := by intro he; rw [he] at hr; omega
  simpa only [unaryCopiesR,Function.update_of_ne h108,Function.update_of_ne h109] using hS r

theorem packedLookupEmitCounters_exec {P U : Type} {Q A V : ℕ}
    {body : P → Pr P 117 Q A U} (st : TblSt 16 A)
    (hbound : ∀ i, st.val i < 2^V) (v : HS 117 Q A U) (S : Stacks 117 A)
    (hS : tblHolds originReg S (tblRho V (List.replicate V tick) (List.replicate V tick) st)) :
    ∃ v' m, v'.user = v.user ∧ m ≤ 6*(st.val 3+st.val 15)+22*V+13 ∧
      Exec body packedLookupEmitCounters (mk v S) m
        (mk v' {S with R := unaryCopiesR st.val S.R [(3,108),(15,109)]}) ∧
      tblHolds originReg {S with R := unaryCopiesR st.val S.R [(3,108),(15,109)]}
        (tblRho V (List.replicate V tick) (List.replicate V tick) st) := by
  have hoff : ∀ p ∈ ([(3,108),(15,109)] : List (Fin 16 × Fin 117)), ∀ r, originReg r ≠ p.2 := by
    intro p hp r he
    have hr := originReg_range r
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl | rfl <;> rw [he] at hr <;> norm_num at hr
  obtain ⟨v',m,hu,hm,he⟩ := tblUnaryCopies_exec (body := body) originReg_injective
    (List.replicate V tick) (List.replicate V tick) st hbound [(3,108),(15,109)] hoff v S hS
  refine ⟨v',m,hu,?_,he,packedLookupEmitCounters_holds st S hS⟩
  simp only [unaryCopiesCost,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hm
  omega

theorem packedLookupEmitRelease_exec {P U : Type} {Q A V : ℕ}
    {body : P → Pr P 117 Q A U} (st : TblSt 16 A) (hacc : st.acc = [])
    (hbound : ∀ i, st.val i < 2^V) (v : HS 117 Q A U) (S : Stacks 117 A)
    (hS : tblHolds originReg S (tblRho V (List.replicate V tick) (List.replicate V tick) st)) :
    ∃ v' m, v'.user = v.user ∧ m ≤ 6*(st.val 3+st.val 15)+84*V+76 ∧
      Exec body (.seq packedLookupEmitCounters releaseOriginBank) (mk v S) m
        (mk v' {S with R := (fun r => if r.val < 31 then [] else
          unaryCopiesR st.val S.R [(3,108),(15,109)] r)}) := by
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁,hh⟩ := packedLookupEmitCounters_exec (body := body) st hbound v S hS
  let S₁ : Stacks 117 A := {S with R := unaryCopiesR st.val S.R [(3,108),(15,109)]}
  have hh' : tblHolds originReg S₁
      (tblRho V (List.replicate V tick) (List.replicate V tick) ⟨st.val,[]⟩) := by
    have heq : st = ⟨st.val,[]⟩ := by cases st; simp only [TblSt.mk.injEq]; exact ⟨trivial,hacc⟩
    rw [← heq]
    exact hh
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := releaseOriginBank_width_exec V V le_rfl st.val v₁ S₁ hh'
  exact ⟨v₂,n₁+n₂,hu₂.trans hu₁,by omega,Exec.seq he₁ he₂⟩

/-- Exact counter values after emission and bank release, with arbitrary
pre-existing counter tails. Other registers above the bank retain their words. -/
theorem packedLookup_released_outputs {A : ℕ} (st : TblSt 16 A) (S : Stacks 117 A) :
    let R := fun r : Fin 117 => if r.val < 31 then [] else
      unaryCopiesR st.val S.R [(3,108),(15,109)] r
    R 108 = List.replicate (st.val 3) tick++S.R 108 ∧
    R 109 = List.replicate (st.val 15) tick++S.R 109 ∧
    ∀ r, 31 ≤ r.val → r ≠ 108 → r ≠ 109 → R r = S.R r := by
  dsimp only
  refine ⟨?_,?_,?_⟩
  · simp [unaryCopiesR]
  · simp [unaryCopiesR]
  · intro r hr h108 h109
    simp [show ¬ r.val < 31 by omega,unaryCopiesR,h108,h109]


theorem packedLookupCounters_of_code {P U : Type} {Q A V K : ℕ}
    {body : P → Pr P 117 Q A U} (code : TblCode 16) (st : TblSt 16 A) (index flag : ℕ) (hflag : flag ≤ 1)
    (hbound : ∀ i, st.val i < 2^V)
    (hcode : TblDo A V V code st
      (fun st' => st'.acc = [] ∧ st'.val 3 = index ∧ st'.val 15 = flag) K)
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hS : tblHolds originReg S (tblRho V (List.replicate V tick) (List.replicate V tick) st)) :
    ∃ v' S' n, v'.user = v.user ∧
      n ≤ K*tblC V V+6*(index+1)+84*V+76 ∧
      Exec body (packedLookupCountersFor code) (mk v S) n (mk v' S') ∧
      S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧
      (∀ r : Fin 117, r.val < 31 → S'.R r = []) ∧
      S'.R 108 = List.replicate (index) tick++S.R 108 ∧
      S'.R 109 = List.replicate flag tick++S.R 109 ∧
      ∀ r : Fin 117, 31 ≤ r.val → r ≠ 108 → r ≠ 109 → S'.R r = S.R r := by
  obtain ⟨st',⟨hpost,hb⟩,hr⟩ := TblDo.host (body := body) originReg_injective
    (List.replicate V tick) (List.replicate V tick) (by simp) (by simp) le_rfl (hcode.bounded hbound) hbound
  obtain ⟨v₁,S₁,n₁,hu₁,hn₁,he₁,hh,hframe⟩ := hr v S hS
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := packedLookupEmitRelease_exec (body := body) st' hpost.1 hb v₁ S₁ hh
  refine ⟨v₂,_,n₁+n₂,hu₂.trans hu₁,?_,Exec.seq he₁ he₂,hframe.1,hframe.2.1,hframe.2.2.1,?_,?_,?_,?_⟩
  · rw [hpost.2.1] at hn₂
    omega
  · intro r hr
    simp [hr]
  · have hout := packedLookup_released_outputs st' S₁
    dsimp only at hout
    dsimp only
    rw [hout.1,hpost.2.1]
    congr 1
    exact hframe.2.2.2 108 (by
      intro r he
      have hr := originReg_range r
      rw [he] at hr
      omega)
  · have hout := packedLookup_released_outputs st' S₁
    dsimp only at hout ⊢
    rw [hout.2.1,hpost.2.2]
    congr 1
    exact hframe.2.2.2 109 (by
      intro r he
      have hr := originReg_range r
      rw [he] at hr
      omega)
  · intro r hr h108 h109
    have hout := packedLookup_released_outputs st' S₁
    dsimp only at hout
    dsimp only
    rw [hout.2.2 r hr h108 h109]
    exact hframe.2.2.2 r (by
      intro x he
      have hx := originReg_range x
      rw [he] at hx
      omega)


theorem packedLookupCounters_exec {P U : Type} {Q A V s t band a b k : ℕ}
    {body : P → Pr P 117 Q A U} (boundary : Bool) (st : TblSt 16 A)
    (hs : st.val 0 = s) (ht : st.val 1 = t) (hband : st.val 2 = band) (hk : st.val 3 = k)
    (ha : st.val 4 = a) (hb : st.val 5 = b) (hacc : st.acc = [])
    (hs0 : 0 < s) (hst : s < t) (haS : a ≤ s) (hbS : b ≤ s)
    (hwide : 8*(t+1)^2+2*band+8 < 2^V) (hkW : k < 2^V)
    (hbound : ∀ i, st.val i < 2^V) (v : HS 117 Q A U) (S : Stacks 117 A)
    (hS : tblHolds originReg S (tblRho V (List.replicate V tick) (List.replicate V tick) st)) :
    ∃ v' S' n, v'.user = v.user ∧
      n ≤ 27*tblC V V+6*(k-a+1)+84*V+76 ∧
      Exec body (packedLookupCounters boundary) (mk v S) n (mk v' S') ∧
      S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧
      (∀ r : Fin 117, r.val < 31 → S'.R r = []) ∧
      S'.R 108 = List.replicate (k-a) tick++S.R 108 ∧
      S'.R 109 = (if IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry.haloMaskAt boundary s t band a b k
        then [tick] else [])++S.R 109 ∧
      ∀ r : Fin 117, 31 ≤ r.val → r ≠ 108 → r ≠ 109 → S'.R r = S.R r := by
  have hc := packedLookupCode_do (A := A) (V := V) (w := V) boundary st
    hs ht hband hk ha hb hs0 hst haS hbS hwide hkW
  have hc' : TblDo A V V (packedLookupCode boundary) st
      (fun st' => st'.acc = [] ∧ st'.val 3 = st.val 3-st.val 4 ∧ st'.val 15 = (if IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry.haloMaskAt boundary s t band a b k then 1 else 0)) 27 := hc.mono (fun st' h => by
    refine ⟨h.2.2.trans hacc,?_,?_⟩
    · simpa only [hk,ha] using h.2.1
    · exact h.1) le_rfl
  have he := packedLookupCounters_of_code (body := body) (packedLookupCode boundary) st (st.val 3-st.val 4) _ (by split <;> omega) hbound hc' v S hS
  obtain ⟨v',S',n,hu,hn,hex,hi,ho,hl,hzero,hindex,hmask,hframe⟩ := he
  refine ⟨v',S',n,hu,by simpa only [hk,ha] using hn,hex,hi,ho,hl,hzero,?_,?_,hframe⟩
  · simpa only [hk,ha] using hindex
  · split <;> simp_all

theorem guardedPackedLookupCounters_exec {P U : Type} {Q A V s t band a b k : ℕ}
    {body : P → Pr P 117 Q A U} (boundary : Bool) (st : TblSt 16 A)
    (hs : st.val 0 = s) (ht : st.val 1 = t) (hband : st.val 2 = band) (hk : st.val 3 = k)
    (ha : st.val 4 = a) (hb : st.val 5 = b) (hacc : st.acc = [])
    (hs0 : 0 < s) (hst : s < t) (haS : a ≤ s) (hbS : b ≤ s)
    (hwide : 8*(t+1)^2+2*band+8 < 2^V) (hkW : k < 2^V)
    (hbound : ∀ i, st.val i < 2^V) (v : HS 117 Q A U) (S : Stacks 117 A)
    [NeZero s] (hkS : k < s)
    (hS : tblHolds originReg S (tblRho V (List.replicate V tick) (List.replicate V tick) st)) :
    ∃ v' S' n, v'.user = v.user ∧
      n ≤ 29*tblC V V+6*(b-a+1)+84*V+76 ∧
      Exec body (packedLookupCountersFor (guardedPackedLookupCode boundary)) (mk v S) n (mk v' S') ∧
      S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧
      (∀ r : Fin 117, r.val < 31 → S'.R r = []) ∧
      S'.R 108 = List.replicate (if IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry.haloMaskAt boundary s t band a b k then k-a else 0) tick++S.R 108 ∧
      S'.R 109 = (if IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry.haloMaskAt boundary s t band a b k
        then [tick] else [])++S.R 109 ∧
      ∀ r : Fin 117, 31 ≤ r.val → r ≠ 108 → r ≠ 109 → S'.R r = S.R r := by
  have hc := guardedPackedLookupCode_do (A := A) (V := V) (w := V) boundary st
    hs ht hband hk ha hb hs0 hst haS hbS hwide hkW
  have hc' : TblDo A V V (guardedPackedLookupCode boundary) st
      (fun st' => st'.acc = [] ∧ st'.val 3 = (if IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry.haloMaskAt boundary s t band a b k then k-a else 0) ∧ st'.val 15 = (if IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry.haloMaskAt boundary s t band a b k then 1 else 0)) 29 := hc.mono (fun st' h => by
    refine ⟨h.2.2.trans hacc,?_,?_⟩
    · simpa only [hk,ha] using h.2.1
    · exact h.1) le_rfl
  have he := packedLookupCounters_of_code (body := body) (guardedPackedLookupCode boundary) st (if IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry.haloMaskAt boundary s t band a b k then k-a else 0) _ (by split <;> omega) hbound hc' v S hS
  obtain ⟨v',S',n,hu,hn,hex,hi,ho,hl,hzero,hindex,hmask,hframe⟩ := he
  have hindexBound := guardedPackedLookupIndex_le boundary hst band a b k hbS hkS
  refine ⟨v',S',n,hu,by omega,hex,hi,ho,hl,hzero,?_,?_,hframe⟩
  · simpa only [hk,ha] using hindex
  · split <;> simp_all

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
