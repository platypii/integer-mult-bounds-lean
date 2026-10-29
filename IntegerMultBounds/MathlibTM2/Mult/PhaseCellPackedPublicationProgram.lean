module

public import IntegerMultBounds.MathlibTM2.Host.Embed
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedBoundaryAdvanceControls
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedBoundaryPublicationControls

/-! Place the restored scanner's output directly at the existing publication
converter's input. The embedding adds no tape traversal or register moves. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.Machine
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

def packedPublicationReg (i : Fin 117) : Fin 224 :=
  if i = 91 then 206 else ⟨i.val,by omega⟩

theorem packedPublicationReg_injective : Function.Injective packedPublicationReg := by
  intro i j he
  have hv := congrArg Fin.val he
  apply Fin.ext
  simp only [packedPublicationReg] at hv
  split_ifs at hv <;> simp_all <;> omega

def packedPublicationProgram {P U : Type} {Q A : ℕ} : Pr P 224 Q A U :=
  .seq (embProg packedPublicationReg id
    (.seq (.seq (chirpBankLoad advanceReg packedAdvanceSource 115 115) originAdvanceControls)
      releaseAdvanceBank)) conditionalPackedBoundaryPublicationControls

theorem packedPublicationReg_off (k : Fin 224) (hk : 117 ≤ k.val) (hk206 : k ≠ 206) :
    ∀ i, packedPublicationReg i ≠ k := by
  intro i he
  by_cases hi : i = 91
  · subst i
    exact hk206 he.symm
  · have hv := congrArg Fin.val he
    simp only [packedPublicationReg,ite_eq_right hi] at hv
    have hh := i.isLt
    omega

/-- Converter width, scratch and output registers are outside the scanner. -/
theorem packedPublication_converter_frame {A : ℕ} (S : Stacks 224 A) (B : Stacks 117 A)
    (k : Fin 224) (hk : 117 ≤ k.val) (hk206 : k ≠ 206) :
    (embOvr packedPublicationReg B.get S).L k = S.L k ∧
      (embOvr packedPublicationReg B.get S).R k = S.R k := by
  exact embOvr_off B.get S (packedPublicationReg_off k hk hk206)

/-- Compose an embedded restored scan with the existing converter. The scan
premise is discharged by the initialized/released scanner at the caller. -/
theorem packedPublicationScan_lift {P U : Type} {Q A : ℕ}
    {body : P → Pr P 224 Q A U} (v : HS 224 Q A U) (S : Stacks 224 A)
    (v₁ : HS 117 Q A U) (B : Stacks 117 A) (n : ℕ)
    (hu : v₁.user = v.user)
    (smallBody : P → Pr P 117 Q A U)
    (hbody : ∀ p, body p = embProg packedPublicationReg id (smallBody p))
    (he : Exec smallBody
      (.seq (.seq (chirpBankLoad advanceReg packedAdvanceSource 115 115) originAdvanceControls)
        releaseAdvanceBank) (mk (embDn packedPublicationReg v) (embStk packedPublicationReg S)) n
        (mk v₁ B)) :
    ∃ v' S', v'.user = v.user ∧
      Exec body (embProg packedPublicationReg id
        (.seq (.seq (chirpBankLoad advanceReg packedAdvanceSource 115 115) originAdvanceControls)
          releaseAdvanceBank)) (mk v S) n (mk v' S') ∧
      embStk packedPublicationReg S' = B ∧
      ∀ k : Fin 224, 117 ≤ k.val → k ≠ 206 → S'.R k = S.R k := by
  obtain ⟨v',S',hex,hv,hu',hproject,hframe⟩ := exec_emb (ι := id) (body' := body)
    packedPublicationReg_injective hbody he v rfl S rfl
  exact ⟨v',S',hu'.trans hu,hex,hproject,
    fun k hk hk206 => (hframe k (packedPublicationReg_off k hk hk206)).2⟩

theorem packedPublicationProgram_of_scan {P U : Type} {Q A s : ℕ} [NeZero s]
    {body : P → Pr P 224 Q A U} (B : Finset (ZMod s)) (a L w : ℕ)
    (hB : ∀ i ∈ B, a ≤ i.val ∧ i.val < a+L) (hwpos : 1 ≤ w)
    (borrowed : List (Fin (A+4))) (v v₁ : HS 224 Q A U) (S S₁ : Stacks 224 A)
    (n : ℕ) (hu : v₁.user = v.user)
    (hscan : Exec body (embProg packedPublicationReg id
      (.seq (.seq (chirpBankLoad advanceReg packedAdvanceSource 115 115) originAdvanceControls)
        releaseAdvanceBank)) (mk v S) n (mk v₁ S₁))
    (hc : S₁.R 116 = List.replicate B.card tick)
    (hs : S₁.R 206 = gatherControls A (originAdvances w 0 (packedBoundaryOrigins B a)++[0])++borrowed)
    (hframe : ∀ k : Fin 224, 117 ≤ k.val → k ≠ 206 → S₁.R k = S.R k)
    (hw : (S.R 160).length = w)
    (hz : ∀ i ∈ ([184,217,201,223,208,211,215] : List (Fin 224)), S.R i = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ n+(33*L*w+23) ∧
      Exec body packedPublicationProgram (mk v S) m
        (mk v' {S₁ with R := (Function.update S₁.R 220
          (gatherControls A (packedBoundaryGaps B a w)++S₁.R 220))}) := by
  have hw₁ : (S₁.R 160).length = w := by
    rw [hframe 160 (by decide) (by decide)]
    exact hw
  have hz₁ : ∀ i ∈ ([184,217,201,223,208,211,215] : List (Fin 224)), S₁.R i = [] := by
    intro i hi
    have hh := hi
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hh
    rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rw [hframe _ (by decide) (by decide)] <;> exact hz _ (by simp)
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := conditionalPackedBoundaryPublicationControls_exec
    (body := body) s B a L w hB hwpos borrowed v₁ S₁ hc hs hw₁ hz₁
  exact ⟨v₂,n+n₂,hu₂.trans hu,Nat.add_le_add_left hn₂ _,Exec.seq hscan he₂⟩

/-- The scanner projection supplies exactly the converter's two input ports. -/
theorem packedPublication_inputs {A : ℕ} (S : Stacks 224 A) (B : Stacks 117 A)
    (hproject : embStk packedPublicationReg S = B)
    (count controls : List (Fin (A+4)))
    (hc : B.R 116 = count) (hs : B.R 91 = controls) :
    S.R 116 = count ∧ S.R 206 = controls := by
  constructor
  · have hh := congrArg (fun X : Stacks 117 A => X.R 116) hproject
    simpa [embStk,packedPublicationReg] using hh.trans hc
  · have hh := congrArg (fun X : Stacks 117 A => X.R 91) hproject
    simpa [embStk,packedPublicationReg] using hh.trans hs


theorem packedPublicationProgram_of_small_scan {P U : Type} {Q A s : ℕ} [NeZero s]
    {body : P → Pr P 224 Q A U} (B : Finset (ZMod s)) (a L w : ℕ)
    (hB : ∀ i ∈ B, a ≤ i.val ∧ i.val < a+L) (hwpos : 1 ≤ w)
    (borrowed : List (Fin (A+4))) (v : HS 224 Q A U) (S : Stacks 224 A)
    (v₁ : HS 117 Q A U) (X : Stacks 117 A) (n : ℕ) (hu : v₁.user = v.user)
    (smallBody : P → Pr P 117 Q A U)
    (hbody : ∀ p, body p = embProg packedPublicationReg id (smallBody p))
    (he : Exec smallBody
      (.seq (.seq (chirpBankLoad advanceReg packedAdvanceSource 115 115) originAdvanceControls)
        releaseAdvanceBank) (mk (embDn packedPublicationReg v) (embStk packedPublicationReg S)) n (mk v₁ X))
    (hc : X.R 116 = List.replicate B.card tick)
    (hs : X.R 91 = gatherControls A (originAdvances w 0 (packedBoundaryOrigins B a)++[0])++borrowed)
    (hw : (S.R 160).length = w)
    (hz : ∀ i ∈ ([184,217,201,223,208,211,215] : List (Fin 224)), S.R i = []) :
    ∃ v' S' m, v'.user = v.user ∧ m ≤ n+(33*L*w+23) ∧
      Exec body packedPublicationProgram (mk v S) m (mk v' S') ∧
      S'.R 220 = gatherControls A (packedBoundaryGaps B a w)++S.R 220 := by
  obtain ⟨v₂,S₂,hu₂,he₂,hproject,hframe⟩ := packedPublicationScan_lift v S v₁ X n hu smallBody hbody he
  obtain ⟨hc₂,hs₂⟩ := packedPublication_inputs S₂ X hproject _ _ hc hs
  obtain ⟨v₃,m,hu₃,hm,he₃⟩ := packedPublicationProgram_of_scan B a L w hB hwpos
    borrowed v v₂ S S₂ n hu₂ he₂ hc₂ hs₂ hframe hw hz
  refine ⟨v₃,_,m,hu₃,hm,he₃,?_⟩
  simp only [Function.update_self]
  rw [hframe 220 (by decide) (by decide)]

theorem packedPublicationProgram_exec {P U : Type} {Q A V w s : ℕ} [NeZero s]
    {body : P → Pr P 224 Q A U} (smallBody : P → Pr P 117 Q A U)
    (hbody : ∀ p, body p = embProg packedPublicationReg id (smallBody p))
    (B : Finset (ZMod s)) (a L : ℕ)
    (hB : ∀ i ∈ B, a ≤ i.val ∧ i.val < a+L)
    (ha : a < 2^V) (hw : w < 2^V) (hs : s < 2^V) (hsw : s*w < 2^V)
    (cs suffix : List (Fin (A+4)))
    (hlen : cs.length = ((IntegerMultBounds.NLogN.PhaseCellMatrix.bOrder s B).map ZMod.val).length)
    (v : HS 224 Q A U) (S : Stacks 224 A) (hV : ((embStk packedPublicationReg S).R 115).length = V)
    (hmeta : ∀ i, (embStk packedPublicationReg S).R (packedAdvanceSource i) = binSyms V (packedAdvanceValues a w (packedAdvanceSource i)))
    (hblank : ∀ r, (embStk packedPublicationReg S).R (advanceReg r) = []) (hc : (embStk packedPublicationReg S).R 116 = cs)
    (hsrc : (embStk packedPublicationReg S).R 109 = ((IntegerMultBounds.NLogN.PhaseCellMatrix.bOrder s B).map ZMod.val).flatMap (binSyms V)++suffix)
    (h88 : (embStk packedPublicationReg S).R 88 = []) (h89 : (embStk packedPublicationReg S).R 89 = []) (h90 : (embStk packedPublicationReg S).R 90 = [])
    (hwpos : 1 ≤ w) (hwidth : (S.R 160).length = w)
    (hz : ∀ i ∈ ([184,217,201,223,208,211,215] : List (Fin 224)), S.R i = [])
    (hcount : cs = List.replicate B.card tick) :
    ∃ v' S' m, v'.user = v.user ∧
      m ≤ 40*V+41+(B.card*(3*Fast.TableVM.tblC V V+29*V+30)+8*(L*w)+11)+(38*V+39)+(33*L*w+23) ∧
      Exec body packedPublicationProgram (mk v S) m (mk v' S') ∧
      S'.R 220 = gatherControls A (packedBoundaryGaps B a w)++S.R 220 := by
  obtain ⟨v₁,X,n,hu,hn,he,hout,hzero,hi,ho,hl,hframe⟩ :=
    releasedBoundaryAdvanceControls_exec (body := smallBody) B a L hB ha hw hs hsw
      cs suffix hlen (embDn packedPublicationReg v) (embStk packedPublicationReg S)
      hV hmeta hblank hc hsrc h88 h89 h90
  have hcX : X.R 116 = List.replicate B.card tick := by
    rw [hframe 116 (by decide) (by decide),hc,hcount]
  obtain ⟨v₂,S₂,m,hu₂,hm,he₂,hout₂⟩ := packedPublicationProgram_of_small_scan B a L w hB hwpos
    ((embStk packedPublicationReg S).R 91) v S v₁ X n hu smallBody hbody he hcX hout hwidth hz
  exact ⟨v₂,S₂,m,hu₂,by omega,he₂,hout₂⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
