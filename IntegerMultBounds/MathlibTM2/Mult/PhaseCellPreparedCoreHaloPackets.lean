module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCoreHaloPacketHost
public import IntegerMultBounds.MathlibTM2.Mult.ChirpBankLoad

/-! Load the packet controller from retained binary geometry, generate the
origin/length stream and release its complete table workspace. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellMatrix

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 168 Q A U}

def coreHaloTableReg (r : TblR 16) : Fin 168 := coreHaloPacketReg (originReg r)

theorem coreHaloTableReg_range (r : TblR 16) : (coreHaloTableReg r).val < 31 := by
  have hr := originReg_range r
  have hn : originReg r ≠ 109 := by
    intro he; have hv := congrArg (fun k : Fin 117 => k.val) he; norm_num at hv; omega
  simpa [coreHaloTableReg,coreHaloPacketReg,hn] using hr

def coreHaloPacketSource (i : Fin 16) : Fin 168 :=
  if i = 0 then 145 else if i = 1 then 150 else if i = 2 then 152 else 154

def coreHaloPacketBits (V : ℕ) (k : Fin 168) : ℕ := if k = 154 then 0 else V

def coreHaloPacketValue (s width radius : ℕ) (k : Fin 168) : ℕ :=
  if k = 145 then s else if k = 150 then width else if k = 152 then radius else 0

def preparedCoreHaloPackets : Pr P 168 Q A U :=
  .seq (chirpBankLoad coreHaloTableReg coreHaloPacketSource 163 163) generatedCoreHaloPacketHost

theorem coreHaloPacketLoad_cost (V : ℕ) :
    chirpBankLoadCost coreHaloTableReg coreHaloPacketSource V V (coreHaloPacketBits V) = 110*V+137 := by
  simp [chirpBankLoadCost,chirpBankCopiesCost,chirpBankInputAssignments,
    coreHaloPacketSource,coreHaloPacketBits,List.ofFn_succ]
  ring

theorem preparedCoreHaloPackets_exec {V s width band n : ℕ}
    (hwidth : 0 < width) (hwide : s+width+n*band < 2^V) (hA : 4 ≤ A)
    (v : HS 168 Q A U) (S : Stacks 168 A)
    (hV : (S.R 163).length = V)
    (hs : S.R 145 = binSyms V s) (hw : S.R 150 = binSyms V width)
    (hr : S.R 152 = binSyms V (n*band)) (hz : S.R 154 = [])
    (hblank : ∀ k : Fin 168, k.val < 31 → S.R k = []) :
    ∃ v' m, v'.user = v.user ∧
      m ≤ 110*V+137+((17*((s+width-1)/width)+9)*tblC V V+
        (4*((s+width-1)/width)+62)*V+65) ∧
      Exec body preparedCoreHaloPackets (mk v S) m
        (mk v' {S with R := (Function.update S.R 159
          ((coreHaloPacketValues s width band n).flatMap (binSyms V)++S.R 159))}) := by
  let value := coreHaloPacketValue s width (n*band)
  let bits := coreHaloPacketBits V
  have hreg : Function.Injective coreHaloTableReg :=
    coreHaloPacketReg_injective.comp originReg_injective
  have hoff (k : Fin 168) (hk : 31 ≤ k.val) : ∀ r, coreHaloTableReg r ≠ k := by
    intro r he
    have hh := coreHaloTableReg_range r
    rw [he] at hh
    omega
  have hinput : ∀ i r, coreHaloTableReg r ≠ coreHaloPacketSource i := by
    intro i
    apply hoff
    simp only [coreHaloPacketSource]; split_ifs <;> decide
  have hfit : ∀ i, value (coreHaloPacketSource i) < 2^bits (coreHaloPacketSource i) := by
    intro i
    simp only [coreHaloPacketSource]
    split_ifs <;> simp [value,bits,coreHaloPacketValue,coreHaloPacketBits] <;> omega
  have hbits : ∀ i, bits (coreHaloPacketSource i) ≤ V := by
    intro i
    simp [bits,coreHaloPacketBits]
    split_ifs <;> omega
  have hsrc : ∀ i, S.R (coreHaloPacketSource i) =
      binSyms (bits (coreHaloPacketSource i)) (value (coreHaloPacketSource i)) := by
    intro i
    simp only [coreHaloPacketSource]
    split_ifs <;> simp [value,bits,coreHaloPacketValue,coreHaloPacketBits,hs,hw,hr,hz,binSyms]
  have hb : ∀ r, S.R (coreHaloTableReg r) = [] := fun r => hblank _ (coreHaloTableReg_range r)
  obtain ⟨v₁,hu₁,he₁⟩ := chirpBankLoad_exec (body := body) coreHaloTableReg hreg coreHaloPacketSource
    163 163 (hoff 163 (by decide)) (hoff 163 (by decide)) hinput V V bits value hfit hbits v S
    hV hV hsrc hb
  let B : Stacks 168 A := {S with R := chirpBankLoadR coreHaloTableReg coreHaloPacketSource V V value S.R}
  have hh := chirpBankLoad_holds coreHaloTableReg hreg coreHaloPacketSource V V value S hb
  let st : TblSt 16 A := ⟨fun i => value (coreHaloPacketSource i),[]⟩
  have hbnd : ∀ i, st.val i < 2^V := by
    intro i
    exact (hfit i).trans_le (Nat.pow_le_pow_right (by decide) (hbits i))
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := generatedCoreHaloPacketHost_exec (body := body) st
    (by simp [st,value,coreHaloPacketSource,coreHaloPacketValue])
    (by simp [st,value,coreHaloPacketSource,coreHaloPacketValue])
    (by simp [st,value,coreHaloPacketSource,coreHaloPacketValue]) hwidth hwide hbnd rfl hA v₁ B hh
  have hframe (k : Fin 168) (hk : 31 ≤ k.val) : B.R k = S.R k :=
    chirpBankLoad_off coreHaloTableReg coreHaloPacketSource V V value S.R k (fun r => (hoff k hk r).symm)
  refine ⟨v₂,110*V+137+m₂,hu₂.trans hu₁,Nat.add_le_add_left hm₂ _,
    (Exec.seq (he₁.cast (coreHaloPacketLoad_cost V) rfl) he₂).cast rfl ?_⟩
  apply congrArg (mk v₂)
  refine Stacks.ext rfl rfl rfl ?_
  funext k
  by_cases hk : k.val < 31
  · have hn : k ≠ 159 := by intro he; subst k; norm_num at hk
    simp [hk,hn,hblank k hk]
  · have hge : 31 ≤ k.val := by omega
    by_cases h159 : k = 159
    · subst k; simp [hframe 159 (by decide)]
    · simp [hk,h159,hframe k hge]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
