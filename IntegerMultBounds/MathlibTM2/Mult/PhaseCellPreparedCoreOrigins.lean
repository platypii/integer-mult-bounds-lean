module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCoreGatherStock

/-! Generate a class's origin queue and count from retained binary geometry,
then release the table. This pass does not read or move ambient coefficients. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 117 Q A U}

def coreOriginSource (i : Fin 16) : Fin 117 :=
  if i = 0 then 32 else if i = 1 then 33 else if i = 2 then 34 else if i = 3 then 35 else 36

def coreOriginBits (V : ℕ) (k : Fin 117) : ℕ := if k = 36 then 0 else V

def coreOriginValue (s width radius L : ℕ) (k : Fin 117) : ℕ :=
  if k = 32 then s else if k = 33 then width else if k = 34 then radius else if k = 35 then L else 0

def preparedCoreOriginsFor (halo : Bool) : Pr P 117 Q A U :=
  .seq (chirpBankLoad originReg coreOriginSource 37 37)
    (.seq (generatedCoreCountedHostFor halo) releaseOriginBank)

def preparedCoreOriginsCost (V s width radius L : ℕ) : ℕ :=
  (112*V+137)+((18*((s+width-1)/width)+9)*tblC V V+
    (coreGatherIndices s width radius L).length*(8*V+6)+6)+(62*V+63)

theorem preparedCoreOriginsFor_native (halo : Bool) :
    mnNativePushBound 3 (preparedCoreOriginsFor (P := P) (Q := Q) (A := A) (U := U) halo) := by
  simp only [preparedCoreOriginsFor,generatedCoreCountedHostFor,countedOriginHost,mnNativePushBound]
  refine ⟨chirpBankLoad_native _ _ _ _,⟨tblCompile_native _ _,?_,?_⟩,clearWords_native_three _⟩
  all_goals simp [countWords,countWordsBody,moveR,moveStep,whileR,peekR,
    transfer,transferAct,scanR,drainR,popDo,keepIn,pushN,
    mnNativePushBound,mnActPush]

theorem preparedCoreOriginsFor_exec_within (halo : Bool) {V s width radius L : ℕ}
    (hwidth : 0 < width) (hwide : s+width+2*radius < 2^V) (hLfit : L < 2^V)
    (hA : 4 ≤ A) (hV : 0 < V) (v : HS 117 Q A U) (S : Stacks 117 A)
    (h37 : (S.R 37).length = V)
    (hs : S.R 32 = binSyms V s) (hw : S.R 33 = binSyms V width)
    (hr : S.R 34 = binSyms V radius) (hL : S.R 35 = binSyms V L) (hz : S.R 36 = [])
    (hblank : ∀ k : Fin 117, k.val < 31 → S.R k = [])
    (h104 : S.R 104 = []) (h106 : S.R 106 = []) (h116 : S.R 116 = []) (depth : ℕ) :
    ∃ v' n, v'.user = v.user ∧ n ≤ preparedCoreOriginsCost V s width radius L ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+
        3*preparedCoreOriginsCost V s width radius L) depth (preparedCoreOriginsFor halo) (Host.mk v S) n
        (Host.mk v' {S with R := (Function.update (Function.update S.R 109
          ((coreGatherIndices s width radius L).flatMap (fun k => binSyms V (coreStart width k-(if halo then radius else 0)))++S.R 109))
          116 (List.replicate (coreGatherIndices s width radius L).length tick))}) := by
  let value := coreOriginValue s width radius L
  let bits := coreOriginBits V
  have hoff (k : Fin 117) (hk : 31 ≤ k.val) : ∀ r, originReg r ≠ k := by
    intro r he
    have hh := originReg_range r
    rw [he] at hh
    omega
  have hinput : ∀ i r, originReg r ≠ coreOriginSource i := by
    intro i; apply hoff
    simp only [coreOriginSource]; split_ifs <;> decide
  have hfit : ∀ i, value (coreOriginSource i) < 2^bits (coreOriginSource i) := by
    intro i
    simp only [coreOriginSource]
    split_ifs <;> simp [value,bits,coreOriginValue,coreOriginBits] <;> omega
  have hbits : ∀ i, bits (coreOriginSource i) ≤ V := by
    intro i; simp [bits,coreOriginBits]; split_ifs <;> omega
  have hsrc : ∀ i, S.R (coreOriginSource i) = binSyms (bits (coreOriginSource i)) (value (coreOriginSource i)) := by
    intro i
    simp only [coreOriginSource]
    split_ifs <;> simp [value,bits,coreOriginValue,coreOriginBits,hs,hw,hr,hL,hz,binSyms]
  have hb : ∀ r, S.R (originReg r) = [] := fun r => hblank _ (originReg_range r)
  obtain ⟨v₁,hu₁,he₁⟩ := chirpBankLoad_exec (body := body) originReg originReg_injective coreOriginSource
    37 37 (hoff 37 (by decide)) (hoff 37 (by decide)) hinput V V bits value hfit hbits v S h37 h37 hsrc hb
  let B : Stacks 117 A := {S with R := chirpBankLoadR originReg coreOriginSource V V value S.R}
  let st : TblSt 16 A := ⟨fun i => value (coreOriginSource i),[]⟩
  have hh : tblHolds originReg B (tblRho V (List.replicate V tick) (List.replicate V tick) st) :=
    chirpBankLoad_holds originReg originReg_injective coreOriginSource V V value S hb
  have hframe (k : Fin 117) (hk : 31 ≤ k.val) : B.R k = S.R k :=
    chirpBankLoad_off originReg coreOriginSource V V value S.R k (fun r => (hoff k hk r).symm)
  obtain ⟨v₂,F,n₂,st₂,hu₂,hn₂,he₂,hqueue,hcount,hholds,hbound,hin,hout,hleft,hrest⟩ :=
    generatedCoreCountedHostFor_exec (body := body) (W := V) (V := V) (s := s) (width := width) (radius := radius) (L := L) halo st
      (by simp [st,value,coreOriginSource,coreOriginValue])
      (by simp [st,value,coreOriginSource,coreOriginValue])
      (by simp [st,value,coreOriginSource,coreOriginValue])
      (by simp [st,value,coreOriginSource,coreOriginValue]) hwidth hwide (by omega) le_rfl hA hV
      (fun i => (hfit i).trans_le (Nat.pow_le_pow_right (by decide) (hbits i))) rfl v₁ B hh
      (by rw [hframe 104 (by decide)]; exact h104)
      (by rw [hframe 106 (by decide)]; exact h106)
      (by rw [hframe 116 (by decide)]; exact h116)
  obtain ⟨v₃,n₃,hu₃,hn₃,he₃⟩ := releaseOriginBank_width_exec (body := body) V V le_rfl st₂.val v₂ F hholds
  have hcost : chirpBankLoadCost originReg coreOriginSource V V bits = 112*V+137 := by
    simp [chirpBankLoadCost,chirpBankCopiesCost,chirpBankInputAssignments,coreOriginSource,bits,coreOriginBits,List.ofFn_succ]
    ring
  rw [hcost] at he₁
  have hwhole := Exec.seq he₁ (Exec.seq he₂ he₃)
  have hend : {F with R := fun k => if k.val < 31 then [] else F.R k} =
      {S with R := (Function.update (Function.update S.R 109
        ((coreGatherIndices s width radius L).flatMap (fun k => binSyms V (coreStart width k-(if halo then radius else 0)))++S.R 109))
        116 (List.replicate (coreGatherIndices s width radius L).length tick))} := by
    refine Stacks.ext hin hout hleft ?_
    funext k
    by_cases hk : k.val < 31
    · have h109 : k ≠ 109 := by intro he; subst k; norm_num at hk
      have h116 : k ≠ 116 := by intro he; subst k; norm_num at hk
      simp [hk,h109,h116,hblank k hk]
    · by_cases h109 : k = 109
      · subst k; simpa [hframe 109 (by decide)] using hqueue
      · by_cases h116 : k = 116
        · subst k; simpa using hcount
        · have hf := hrest k h109 h116 (hoff k (by omega))
          simp [hk,h109,h116,hf,hframe k (by omega)]
  rw [hend] at hwhole
  refine ⟨v₃,(112*V+137)+(n₂+n₃),hu₃.trans (hu₂.trans hu₁),?_,?_⟩
  · dsimp only [preparedCoreOriginsCost]; omega
  · exact mn_native_exec_within hwhole 3 (preparedCoreOriginsFor_native halo) depth _ (by
      have ht : (112*V+137)+(n₂+n₃) ≤ preparedCoreOriginsCost V s width radius L := by
        dsimp only [preparedCoreOriginsCost]; omega
      have hm := Nat.mul_le_mul_left 3 ht
      omega)

def preparedCoreOrigins : Pr P 117 Q A U :=
  .seq (chirpBankLoad originReg coreOriginSource 37 37)
    (.seq generatedCoreCountedHost releaseOriginBank)


@[simp] theorem preparedCoreOriginsFor_halo : preparedCoreOriginsFor (P := P) (Q := Q) (A := A) (U := U) true = preparedCoreOrigins := rfl

theorem preparedCoreOrigins_native :
    mnNativePushBound 3 (preparedCoreOrigins (P := P) (Q := Q) (A := A) (U := U)) := by
  exact preparedCoreOriginsFor_native true

theorem preparedCoreOrigins_exec_within {V s width radius L : ℕ}
    (hwidth : 0 < width) (hwide : s+width+2*radius < 2^V) (hLfit : L < 2^V)
    (hA : 4 ≤ A) (hV : 0 < V) (v : HS 117 Q A U) (S : Stacks 117 A)
    (h37 : (S.R 37).length = V)
    (hs : S.R 32 = binSyms V s) (hw : S.R 33 = binSyms V width)
    (hr : S.R 34 = binSyms V radius) (hL : S.R 35 = binSyms V L) (hz : S.R 36 = [])
    (hblank : ∀ k : Fin 117, k.val < 31 → S.R k = [])
    (h104 : S.R 104 = []) (h106 : S.R 106 = []) (h116 : S.R 116 = []) (depth : ℕ) :
    ∃ v' n, v'.user = v.user ∧ n ≤ preparedCoreOriginsCost V s width radius L ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+
        3*preparedCoreOriginsCost V s width radius L) depth preparedCoreOrigins (Host.mk v S) n
        (Host.mk v' {S with R := (Function.update (Function.update S.R 109
          ((coreGatherIndices s width radius L).flatMap (fun k => binSyms V (coreStart width k-radius))++S.R 109))
          116 (List.replicate (coreGatherIndices s width radius L).length tick))}) := by
  simpa using preparedCoreOriginsFor_exec_within true hwidth hwide hLfit hA hV v S h37 hs hw hr hL hz hblank h104 h106 h116 depth

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
