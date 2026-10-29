module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedLookupCounters
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedLookupBank
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellMaskedPackedWord

/-! Test ambient membership, emit a local packed address, read the selected
operand, and clear the temporary address. The ambient query lives in the
geometry table until the local counters are generated. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Stack

def packedHaloRead {P U : Type} {Q A : ℕ} : Pr P 117 Q A U :=
  .seq (maskedIndexedWord 109 108 94 92 110 3 0 1 2 4 5) (uclear 108)

def packedHaloLookup {P U : Type} {Q A : ℕ} (boundary : Bool) : Pr P 117 Q A U :=
  .seq (packedLookupCounters boundary)
    packedHaloRead


theorem packedHaloRead_exec {P U : Type} {Q A s : ℕ} {body : P → Pr P 117 Q A U}
    (flag : Bool) (w a L k : ℕ) (F : ZMod s → GaussianInt)
    (hfit : a+L ≤ s) (hk : flag = true → a ≤ k ∧ k < a+L)
    (tail : List (Fin (A+4))) (v : HS 117 Q A U) (S : Stacks 117 A)
    (hmask : S.R 109 = if flag then [tick] else [])
    (hindex : (S.R 108).length = k-a) (hwidth : (S.R 94).length = w)
    (hsrc : S.R 92 = cstream A w (packedInterval a L F)++tail)
    (hclean : ∀ r ∈ ([3,0,1,2,4,5] : List (Fin 117)), S.R r = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ (k-a)*(12*w+11)+10*w+30 ∧
      Exec body packedHaloRead (mk v S) n
        (mk v' {S with R := (Function.update (Function.update (Function.update S.R 110
          (csyms A w (if flag then F (k : ZMod s) else 0)++S.R 110)) 109 []) 108 [])}) := by
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := maskedPackedAmbientWord_exec (body := body)
    (by decide : ([(109 : Fin 117),108,94,92,110,3,0,1,2,4,5]).Nodup)
    flag w a L k F hfit hk tail v S hmask hindex hwidth hsrc hclean
  let S₁ : Stacks 117 A := {S with R := (Function.update (Function.update S.R 110
    (csyms A w (if flag then F (k : ZMod s) else 0)++S.R 110)) 109 [])}
  obtain ⟨v₂,hu₂,he₂⟩ := uclear_exec body 108 v₁ S₁
  have hlen : (S₁.R 108).length = k-a := by simpa [S₁] using hindex
  refine ⟨v₂,n₁+(2*(k-a)+2),hu₂.trans hu₁,by nlinarith only [hn₁],?_⟩
  simpa only [hlen,packedHaloRead,S₁] using Exec.seq he₁ he₂

theorem packedHaloLookup_exec {P U : Type} {Q A V s t band a b k : ℕ}
    {body : P → Pr P 117 Q A U} (boundary : Bool) (st : TblSt 16 A)
    (hs : st.val 0 = s) (ht : st.val 1 = t) (hband : st.val 2 = band) (hk : st.val 3 = k)
    (ha : st.val 4 = a) (hb : st.val 5 = b) (hacc : st.acc = [])
    (hs0 : 0 < s) (hst : s < t) (haS : a ≤ s) (hbS : b ≤ s)
    (hwide : 8*(t+1)^2+2*band+8 < 2^V) (hkW : k < 2^V)
    (hbound : ∀ i, st.val i < 2^V) (v : HS 117 Q A U) (S : Stacks 117 A)
    (hS : tblHolds originReg S (tblRho V (List.replicate V tick) (List.replicate V tick) st))
    [NeZero s] (hab : a ≤ b) (hkS : k < s) (w : ℕ)
    (F : ZMod s → GaussianInt) (tail : List (Fin (A+4)))
    (hwidth : (S.R 94).length = w)
    (hsrc : S.R 92 = cstream A w (packedInterval a (b-a) F)++tail)
    (h108 : S.R 108 = []) (h109 : S.R 109 = []) :
    ∃ v' S' n, v'.user = v.user ∧
      n ≤ 27*tblC V V+6*(k-a+1)+84*V+76+((k-a)*(12*w+11)+10*w+30) ∧
      Exec body (packedHaloLookup boundary) (mk v S) n (mk v' S') ∧
      S'.R 110 = csyms A w (if IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry.haloMaskAt boundary s t band a b k
        then F (k : ZMod s) else 0)++S.R 110 ∧
      S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧
      (∀ r : Fin 117, r.val < 31 → S'.R r = []) ∧
      ∀ r : Fin 117, 31 ≤ r.val → r ≠ 110 → S'.R r = S.R r := by
  obtain ⟨v₁,S₁,n₁,hu₁,hn₁,he₁,hi₁,ho₁,hl₁,hzero,hindex,hmask,hframe⟩ :=
    packedLookupCounters_exec (body := body) boundary st hs ht hband hk ha hb hacc
      hs0 hst haS hbS hwide hkW hbound v S hS
  have hf (r : Fin 117) (hr : 31 ≤ r.val) (h108' : r ≠ 108) (h109' : r ≠ 109) :=
    hframe r hr h108' h109'
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := packedHaloRead_exec (body := body)
    (IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry.haloMaskAt boundary s t band a b k)
    w a (b-a) k F (by omega) (by
      intro hm
      have hh := haloMaskAt_packed_bounds boundary hst band a b k hbS hkS hm
      omega) tail v₁ S₁
    (by simpa only [h109,List.append_nil] using hmask)
    (by simp only [hindex,h108,List.append_nil,List.length_replicate])
    (by rw [hf 94 (by decide) (by decide) (by decide)]; exact hwidth)
    (by rw [hf 92 (by decide) (by decide) (by decide)]; exact hsrc)
    (by intro r hr; apply hzero; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  refine ⟨v₂,_,n₁+n₂,hu₂.trans hu₁,by omega,Exec.seq he₁ he₂,?_,hi₁,ho₁,hl₁,?_,?_⟩
  · simp only [Function.update_of_ne (by decide : (110 : Fin 117) ≠ 108),
      Function.update_of_ne (by decide : (110 : Fin 117) ≠ 109),Function.update_self]
    rw [hf 110 (by decide) (by decide) (by decide)]

  · intro r hr
    have h108' : r ≠ 108 := by intro he; subst r; norm_num at hr
    have h109' : r ≠ 109 := by intro he; subst r; norm_num at hr
    have h110' : r ≠ 110 := by intro he; subst r; norm_num at hr
    simpa only [Function.update_of_ne h108',Function.update_of_ne h109',Function.update_of_ne h110'] using hzero r hr
  · intro r hr h110'
    by_cases h108' : r = 108
    · subst r; simpa only [Function.update_self] using h108.symm
    by_cases h109' : r = 109
    · subst r
      simpa only [Function.update_of_ne (by decide : (109 : Fin 117) ≠ 108),Function.update_self] using h109.symm
    simpa only [Function.update_of_ne h108',Function.update_of_ne h109',Function.update_of_ne h110'] using hf r hr h108' h109'

theorem packedHaloLookup_state_exec {P U : Type} {Q A V s t band a b k : ℕ}
    {body : P → Pr P 117 Q A U} (boundary : Bool) (st : TblSt 16 A)
    (hs : st.val 0 = s) (ht : st.val 1 = t) (hband : st.val 2 = band) (hk : st.val 3 = k)
    (ha : st.val 4 = a) (hb : st.val 5 = b) (hacc : st.acc = [])
    (hs0 : 0 < s) (hst : s < t) (haS : a ≤ s) (hbS : b ≤ s)
    (hwide : 8*(t+1)^2+2*band+8 < 2^V) (hkW : k < 2^V)
    (hbound : ∀ i, st.val i < 2^V) (v : HS 117 Q A U) (S : Stacks 117 A)
    (hS : tblHolds originReg S (tblRho V (List.replicate V tick) (List.replicate V tick) st))
    [NeZero s] (hab : a ≤ b) (hkS : k < s) (w : ℕ)
    (F : ZMod s → GaussianInt) (tail : List (Fin (A+4)))
    (hwidth : (S.R 94).length = w)
    (hsrc : S.R 92 = cstream A w (packedInterval a (b-a) F)++tail)
    (h108 : S.R 108 = []) (h109 : S.R 109 = []) :
    ∃ v' n, v'.user = v.user ∧
      n ≤ 27*tblC V V+6*(k-a+1)+84*V+76+((k-a)*(12*w+11)+10*w+30) ∧
      Exec body (packedHaloLookup boundary) (mk v S) n
        (mk v' {S with R := (fun r => if r.val < 31 then [] else if r = 110 then
          csyms A w (if IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry.haloMaskAt boundary s t band a b k
            then F (k : ZMod s) else 0)++S.R 110 else S.R r)}) := by
  obtain ⟨v',S',n,hu,hn,he,hout,hi,ho,hl,hzero,hframe⟩ := packedHaloLookup_exec
    (body := body) boundary st hs ht hband hk ha hb hacc hs0 hst haS hbS hwide hkW hbound
    v S hS hab hkS w F tail hwidth hsrc h108 h109
  refine ⟨v',n,hu,hn,he.cast rfl ?_⟩
  apply congrArg (mk v')
  refine Stacks.ext hi ho hl ?_
  funext r
  by_cases hr : r.val < 31
  · simp only [hr,ite_true]
    exact hzero r hr
  · by_cases h110 : r = 110
    · subst r
      simpa only [hr,ite_false,ite_true] using hout
    · simpa only [hr,ite_false,h110] using hframe r (by omega) h110


theorem binaryPackedHaloLookup_exec {P U : Type} {Q A V s t band a b k : ℕ} [NeZero s]
    {body : P → Pr P 117 Q A U} (boundary : Bool) (value : Fin 117 → ℕ)
    (hs : value 97 = s) (ht : value 98 = t) (hband : value 100 = band)
    (hk : value 107 = k) (ha : value 101 = a) (hb : value 103 = b)
    (hst : s < t) (hab : a ≤ b) (hbS : b ≤ s) (hkS : k < s)
    (hwide : 8*(t+1)^2+2*band+8 < 2^V)
    (hbound : ∀ i, value (packedLookupBankSource i) < 2^V)
    (v : HS 117 Q A U) (S : Stacks 117 A) (hV : (S.R 115).length = V)
    (hmeta : ∀ i, S.R (packedLookupBankSource i) = binSyms V (value (packedLookupBankSource i)))
    (hblank : ∀ r, S.R (originReg r) = []) (w : ℕ) (F : ZMod s → GaussianInt)
    (tail : List (Fin (A+4))) (hwidth : (S.R 94).length = w)
    (hsrc : S.R 92 = cstream A w (packedInterval a (b-a) F)++tail)
    (h108 : S.R 108 = []) (h109 : S.R 109 = []) :
    ∃ v' S' n, v'.user = v.user ∧
      n ≤ 136*V+137+(27*tblC V V+6*(k-a+1)+84*V+76+((k-a)*(12*w+11)+10*w+30)) ∧
      Exec body (.seq loadPackedLookupBank (packedHaloLookup boundary)) (mk v S) n (mk v' S') ∧
      S'.R 110 = csyms A w (if IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry.haloMaskAt boundary s t band a b k
        then F (k : ZMod s) else 0)++S.R 110 ∧
      S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧
      (∀ r : Fin 117, r.val < 31 → S'.R r = []) ∧
      ∀ r : Fin 117, 31 ≤ r.val → r ≠ 110 → S'.R r = S.R r := by
  obtain ⟨v₁,hu₁,he₁,hh,hframe⟩ := loadPackedLookupBank_exec V value hbound v S hV hmeta hblank
  let S₁ : Stacks 117 A := {S with R := chirpBankLoadR originReg packedLookupBankSource V V value S.R}
  let st : TblSt 16 A := ⟨fun i => value (packedLookupBankSource i),[]⟩
  have hf (r : Fin 117) (hr : 31 ≤ r.val) : S₁.R r = S.R r := hframe r hr
  have hkW : k < 2^V := by simpa [packedLookupBankSource,hk] using hbound 3
  obtain ⟨v₂,S₂,n₂,hu₂,hn₂,he₂,hout,hrest⟩ := packedHaloLookup_exec (body := body) boundary st
    (by simp [st,packedLookupBankSource,hs]) (by simp [st,packedLookupBankSource,ht])
    (by simp [st,packedLookupBankSource,hband]) (by simp [st,packedLookupBankSource,hk])
    (by simp [st,packedLookupBankSource,ha]) (by simp [st,packedLookupBankSource,hb]) rfl
    (NeZero.pos s) hst (by omega) hbS hwide hkW hbound v₁ S₁ hh hab hkS w F tail
    (by rw [hf 94 (by decide)]; exact hwidth) (by rw [hf 92 (by decide)]; exact hsrc)
    (by rw [hf 108 (by decide)]; exact h108) (by rw [hf 109 (by decide)]; exact h109)
  refine ⟨v₂,S₂,136*V+137+n₂,hu₂.trans hu₁,Nat.add_le_add_left hn₂ _,Exec.seq he₁ he₂,
    by simpa only [hf 110 (by decide)] using hout,
    hrest.1,hrest.2.1,hrest.2.2.1,hrest.2.2.2.1,?_⟩
  intro r hr h110
  exact (hrest.2.2.2.2 r hr h110).trans (hf r hr)

theorem guardedPackedHaloRead_exec {P U : Type} {Q A s : ℕ} {body : P → Pr P 117 Q A U}
    (flag : Bool) (w a L k : ℕ) (F : ZMod s → GaussianInt)
    (hfit : a+L ≤ s) (hk : flag = true → a ≤ k ∧ k < a+L)
    (tail : List (Fin (A+4))) (v : HS 117 Q A U) (S : Stacks 117 A)
    (hmask : S.R 109 = if flag then [tick] else [])
    (hindex : (S.R 108).length = (if flag then k-a else 0)) (hwidth : (S.R 94).length = w)
    (hsrc : S.R 92 = cstream A w (packedInterval a L F)++tail)
    (hclean : ∀ r ∈ ([3,0,1,2,4,5] : List (Fin 117)), S.R r = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ (if flag then k-a else 0)*(12*w+11)+10*w+30 ∧
      Exec body packedHaloRead (mk v S) n
        (mk v' {S with R := (Function.update (Function.update (Function.update S.R 110
          (csyms A w (if flag then F (k : ZMod s) else 0)++S.R 110)) 109 []) 108 [])}) := by
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := maskedPackedAmbientWord_selected_index_exec (body := body)
    (by decide : ([(109 : Fin 117),108,94,92,110,3,0,1,2,4,5]).Nodup)
    flag w a L k F hfit hk tail v S hmask (by intro hf; simpa only [hf,ite_true] using hindex) hwidth hsrc hclean
  let S₁ : Stacks 117 A := {S with R := (Function.update (Function.update S.R 110
    (csyms A w (if flag then F (k : ZMod s) else 0)++S.R 110)) 109 [])}
  obtain ⟨v₂,hu₂,he₂⟩ := uclear_exec body 108 v₁ S₁
  have hlen : (S₁.R 108).length = (if flag then k-a else 0) := by simpa [S₁] using hindex
  refine ⟨v₂,n₁+(2*(if flag then k-a else 0)+2),hu₂.trans hu₁,by nlinarith only [hn₁],?_⟩
  simpa only [hlen,packedHaloRead,S₁] using Exec.seq he₁ he₂


theorem guardedPackedHaloLookup_exec {P U : Type} {Q A V s t band a b k : ℕ}
    {body : P → Pr P 117 Q A U} (boundary : Bool) (st : TblSt 16 A)
    (hs : st.val 0 = s) (ht : st.val 1 = t) (hband : st.val 2 = band) (hk : st.val 3 = k)
    (ha : st.val 4 = a) (hb : st.val 5 = b) (hacc : st.acc = [])
    (hs0 : 0 < s) (hst : s < t) (haS : a ≤ s) (hbS : b ≤ s)
    (hwide : 8*(t+1)^2+2*band+8 < 2^V) (hkW : k < 2^V)
    (hbound : ∀ i, st.val i < 2^V) (v : HS 117 Q A U) (S : Stacks 117 A)
    (hS : tblHolds originReg S (tblRho V (List.replicate V tick) (List.replicate V tick) st))
    [NeZero s] (hab : a ≤ b) (hkS : k < s) (w : ℕ)
    (F : ZMod s → GaussianInt) (tail : List (Fin (A+4)))
    (hwidth : (S.R 94).length = w)
    (hsrc : S.R 92 = cstream A w (packedInterval a (b-a) F)++tail)
    (h108 : S.R 108 = []) (h109 : S.R 109 = []) :
    ∃ v' S' n, v'.user = v.user ∧
      n ≤ 29*tblC V V+6*(b-a+1)+84*V+76+((b-a)*(12*w+11)+10*w+30) ∧
      Exec body (.seq (packedLookupCountersFor (guardedPackedLookupCode boundary)) packedHaloRead) (mk v S) n (mk v' S') ∧
      S'.R 110 = csyms A w (if IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry.haloMaskAt boundary s t band a b k
        then F (k : ZMod s) else 0)++S.R 110 ∧
      S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧
      (∀ r : Fin 117, r.val < 31 → S'.R r = []) ∧
      ∀ r : Fin 117, 31 ≤ r.val → r ≠ 110 → S'.R r = S.R r := by
  obtain ⟨v₁,S₁,n₁,hu₁,hn₁,he₁,hi₁,ho₁,hl₁,hzero,hindex,hmask,hframe⟩ :=
    guardedPackedLookupCounters_exec (body := body) boundary st hs ht hband hk ha hb hacc
      hs0 hst haS hbS hwide hkW hbound v S hkS hS
  have hf (r : Fin 117) (hr : 31 ≤ r.val) (h108' : r ≠ 108) (h109' : r ≠ 109) :=
    hframe r hr h108' h109'
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := guardedPackedHaloRead_exec (body := body)
    (IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry.haloMaskAt boundary s t band a b k)
    w a (b-a) k F (by omega) (by
      intro hm
      have hh := haloMaskAt_packed_bounds boundary hst band a b k hbS hkS hm
      omega) tail v₁ S₁
    (by simpa only [h109,List.append_nil] using hmask)
    (by simp only [hindex,h108,List.append_nil,List.length_replicate])
    (by rw [hf 94 (by decide) (by decide) (by decide)]; exact hwidth)
    (by rw [hf 92 (by decide) (by decide) (by decide)]; exact hsrc)
    (by intro r hr; apply hzero; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  refine ⟨v₂,_,n₁+n₂,hu₂.trans hu₁,?_,Exec.seq he₁ he₂,?_,hi₁,ho₁,hl₁,?_,?_⟩
  · have hbnd := guardedPackedLookupIndex_le boundary hst band a b k hbS hkS
    have hm := Nat.mul_le_mul_right (12*w+11) hbnd
    omega
  · simp only [Function.update_of_ne (by decide : (110 : Fin 117) ≠ 108),
      Function.update_of_ne (by decide : (110 : Fin 117) ≠ 109),Function.update_self]
    rw [hf 110 (by decide) (by decide) (by decide)]

  · intro r hr
    have h108' : r ≠ 108 := by intro he; subst r; norm_num at hr
    have h109' : r ≠ 109 := by intro he; subst r; norm_num at hr
    have h110' : r ≠ 110 := by intro he; subst r; norm_num at hr
    simpa only [Function.update_of_ne h108',Function.update_of_ne h109',Function.update_of_ne h110'] using hzero r hr
  · intro r hr h110'
    by_cases h108' : r = 108
    · subst r; simpa only [Function.update_self] using h108.symm
    by_cases h109' : r = 109
    · subst r
      simpa only [Function.update_of_ne (by decide : (109 : Fin 117) ≠ 108),Function.update_self] using h109.symm
    simpa only [Function.update_of_ne h108',Function.update_of_ne h109',Function.update_of_ne h110'] using hf r hr h108' h109'


end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
