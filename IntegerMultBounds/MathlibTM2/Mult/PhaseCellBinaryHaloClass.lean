module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReleasedHaloClass
public import IntegerMultBounds.MathlibTM2.Mult.ChirpBankLoad

/-! Generate the existing halo-class packets/count from retained binary words.
The loaded table and scratch are released, and every source is restored. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 117 Q A U}

def haloClassBinarySource (i : Fin 16) : Fin 117 :=
  if i = 0 then 97 else if i = 1 then 98 else if i = 2 then 100 else if i = 3 then 102 else
  if i = 13 then 111 else if i = 14 then 113 else 107

def haloClassBinaryValue (s t band a b L : ℕ) (k : Fin 117) : ℕ :=
  if k = 97 then s else if k = 98 then t else if k = 100 then band else if k = 102 then L else
  if k = 111 then a else if k = 113 then b else 0

def binaryHaloClass : Pr P 117 Q A U :=
  .seq (chirpBankLoad originReg haloClassBinarySource 115 115) releasedHaloClass

def binaryHaloClassCost (V s t band a b L : ℕ) : ℕ :=
  136*V+137+releasedHaloClassCost V s t band a b L

theorem binaryHaloClass_exec {V s t band a b L : ℕ}
    (hs : 0 < s) (hst : s < t) (hband : band ≤ s) (hab : a ≤ b) (hb : b ≤ s)
    (hL : 0 < L) (hLs : L ≤ s) (hA : 4 ≤ A) (hwide : 8*(t+1)^2+2*band+8 < 2^V)
    (v : HS 117 Q A U) (S : Stacks 117 A) (hV : (S.R 115).length = V)
    (hmeta : ∀ i, S.R (haloClassBinarySource i) = binSyms V
      (haloClassBinaryValue s t band a b L (haloClassBinarySource i)))
    (hblank : ∀ r, S.R (originReg r) = [])
    (h104 : S.R 104 = []) (h106 : S.R 106 = []) (h116 : S.R 116 = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ binaryHaloClassCost V s t band a b L ∧
      Exec body binaryHaloClass (mk v S) m
        (mk v' {S with R := (Function.update (Function.update S.R
          109 (haloOriginPackets A V s t band a b L++S.R 109))
          116 (List.replicate (haloLengthGroup s t band a b L).length tick))}) := by
  let value := haloClassBinaryValue s t band a b L
  have hstate : (⟨fun i => value (haloClassBinarySource i),[]⟩ : TblSt 16 A) = haloClassRawState A s t band a b L := by
    congr 1
    funext i
    fin_cases i <;> simp [value,haloClassBinaryValue,haloClassBinarySource,haloClassRawState]
  have hfit : ∀ i, value (haloClassBinarySource i) < 2^V := by
    intro i
    have hh := haloClassRawState_bounded (A := A) (hab.trans hb) hb hLs hst hband hwide i
    rw [← hstate] at hh
    exact hh
  have hoff (k : Fin 117) (hk : 31 ≤ k.val) : ∀ r, originReg r ≠ k := by
    intro r he; have hr := originReg_range r; rw [he] at hr; omega
  have hinput : ∀ i r, originReg r ≠ haloClassBinarySource i := by
    intro i
    apply hoff
    simp only [haloClassBinarySource]; split_ifs <;> decide
  obtain ⟨v₀,hu₀,he₀⟩ := chirpBankLoad_exec (body := body) originReg originReg_injective
    haloClassBinarySource 115 115 (hoff 115 (by decide)) (hoff 115 (by decide)) hinput
    V V (fun _ => V) value hfit (fun _ => le_rfl) v S hV hV hmeta hblank
  let S₀ : Stacks 117 A := {S with R := chirpBankLoadR originReg haloClassBinarySource V V value S.R}
  have hholds := chirpBankLoad_holds originReg originReg_injective haloClassBinarySource V V value S hblank
  rw [hstate] at hholds
  have hpass (k : Fin 117) (hk : 31 ≤ k.val) : S₀.R k = S.R k :=
    chirpBankLoad_off originReg haloClassBinarySource V V value S.R k (fun r => (hoff k hk r).symm)
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := releasedHaloClass_exec (body := body)
    hs hst hband hab hb hL hLs hA hwide v₀ S₀ hholds
    ((hpass 104 (by decide)).trans h104) ((hpass 106 (by decide)).trans h106)
    ((hpass 116 (by decide)).trans h116)
  have hcost : chirpBankLoadCost originReg haloClassBinarySource V V (fun _ => V) = 136*V+137 := by
    simp [chirpBankLoadCost,chirpBankCopiesCost,chirpBankInputAssignments]
    ring
  refine ⟨v₁,136*V+137+m₁,hu₁.trans hu₀,Nat.add_le_add_left hm₁ _,
    (Exec.seq he₀ he₁).cast (by rw [hcost]) ?_⟩
  apply congrArg (mk v₁)
  refine Stacks.ext rfl rfl rfl ?_
  funext k
  by_cases hk : k.val < 31
  · obtain ⟨r,hr⟩ := originReg_covers k hk
    have hz : S.R k = [] := hr ▸ hblank r
    have h109 : k ≠ 109 := by intro he; have hh := congrArg Fin.val he; norm_num at hh; omega
    have h116' : k ≠ 116 := by intro he; have hh := congrArg Fin.val he; norm_num at hh; omega
    simp [hk,h109,h116',hz]
  · have hf := hpass k (by omega)
    by_cases h109 : k = 109
    · subst k; simp [hf]
    by_cases h116' : k = 116
    · subst k; simp
    · simp [hk,h109,h116',hf]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
