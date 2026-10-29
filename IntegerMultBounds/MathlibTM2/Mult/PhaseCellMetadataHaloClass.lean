module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBinaryHaloClass
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCouplingIntervalMetadata
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedHaloGroups

/-! Canonical binary halo geometry supplies generated native batch controls.
The selected positive length is a binary word on 157, outside the live payload. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry ScalarPlacement

/-- Sources use canonical binary geometry; outputs remain native 109 and 116. -/
def haloClassMetadataPlacement (i : Fin 117) : Fin 168 :=
  if i = 97 then 145 else if i = 98 then 146 else if i = 100 then 147 else if i = 102 then 157 else
  if i = 111 then 149 else if i = 113 then 151 else if i = 107 then 154 else if i = 115 then 163 else ⟨i.val,by omega⟩

private def haloClassMetadataBack (j : Fin 168) : Fin 117 :=
  if j = 145 then 97 else if j = 146 then 98 else if j = 147 then 100 else if j = 157 then 102 else
  if j = 149 then 111 else if j = 151 then 113 else if j = 154 then 107 else if j = 163 then 115 else
  if h : j.val < 117 then ⟨j.val,h⟩ else 0

private theorem haloClassMetadataBack_place (i : Fin 117) :
    haloClassMetadataBack (haloClassMetadataPlacement i) = i := by
  by_cases h97 : i = 97
  · subst i; rfl
  by_cases h98 : i = 98
  · subst i; rfl
  by_cases h100 : i = 100
  · subst i; rfl
  by_cases h102 : i = 102
  · subst i; rfl
  by_cases h111 : i = 111
  · subst i; rfl
  by_cases h113 : i = 113
  · subst i; rfl
  by_cases h107 : i = 107
  · subst i; rfl
  by_cases h115 : i = 115
  · subst i; rfl
  have hoff (n : ℕ) (hn : 117 ≤ n) : i.val ≠ n := by have hi := i.isLt; omega
  simp [haloClassMetadataPlacement,h97,h98,h100,h102,h111,h113,h107,h115,haloClassMetadataBack,
    Fin.ext_iff,hoff 145 (by decide),hoff 146 (by decide),hoff 147 (by decide),hoff 157 (by decide),
    hoff 149 (by decide),hoff 151 (by decide),hoff 154 (by decide),hoff 163 (by decide),i.isLt]

theorem haloClassMetadataPlacement_injective : Function.Injective haloClassMetadataPlacement := by
  intro i j he
  have hh := congrArg haloClassMetadataBack he
  simpa only [haloClassMetadataBack_place] using hh

theorem haloClassMetadataPlacement_low (i : Fin 117) (hi : i.val < 97) :
    haloClassMetadataPlacement i = ⟨i.val,by omega⟩ := by
  have hn (j : Fin 117) (hj : 97 ≤ j.val) : i ≠ j := by intro he; have hh := congrArg Fin.val he; omega
  simp [haloClassMetadataPlacement,hn 97 (by decide),hn 98 (by decide),hn 100 (by decide),hn 102 (by decide),
    hn 111 (by decide),hn 113 (by decide),hn 107 (by decide),hn 115 (by decide)]

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 168 Q A U}

def metadataHaloClass : Pr P 168 Q A U := embProg haloClassMetadataPlacement Empty.elim (binaryHaloClass (P := Empty))

theorem metadataHaloClass_exec {V s t band a b origin N L : ℕ}
    (hs : 0 < s) (hst : s < t) (hband : band ≤ s) (hab : a ≤ b) (hb : b ≤ s)
    (hL : 0 < L) (hLs : L ≤ s) (hA : 4 ≤ A) (hwide : 8*(t+1)^2+2*band+8 < 2^V)
    (v : HS 168 Q A U) (S : Stacks 168 A)
    (hmeta : CouplingIntervalMetadata V s t band a b origin N S) (h157 : S.R 157 = binSyms V L)
    (hblank : ∀ k : Fin 168, k.val < 31 → S.R k = [])
    (h104 : S.R 104 = []) (h106 : S.R 106 = []) (h116 : S.R 116 = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ binaryHaloClassCost V s t band a b L ∧
      Exec body metadataHaloClass (mk v S) m
        (mk v' {S with R := (Function.update (Function.update S.R
          109 (haloOriginPackets A V s t band a b L++S.R 109))
          116 (List.replicate (haloLengthGroup s t band a b L).length tick))}) := by
  have hsrc : ∀ i, (embStk haloClassMetadataPlacement S).R (haloClassBinarySource i) =
      binSyms V (haloClassBinaryValue s t band a b L (haloClassBinarySource i)) := by
    intro i
    simp only [haloClassBinarySource]
    split_ifs
    · simpa [embStk,haloClassMetadataPlacement,haloClassBinaryValue,couplingIntervalValue] using
        hmeta.encoded 145 (by decide)
    · simpa [embStk,haloClassMetadataPlacement,haloClassBinaryValue,couplingIntervalValue] using
        hmeta.encoded 146 (by decide)
    · simpa [embStk,haloClassMetadataPlacement,haloClassBinaryValue,couplingIntervalValue] using
        hmeta.encoded 147 (by decide)
    · simpa [embStk,haloClassMetadataPlacement,haloClassBinaryValue] using h157
    · simpa [embStk,haloClassMetadataPlacement,haloClassBinaryValue,couplingIntervalValue] using
        hmeta.encoded 149 (by decide)
    · simpa [embStk,haloClassMetadataPlacement,haloClassBinaryValue,couplingIntervalValue] using
        hmeta.encoded 151 (by decide)
    · simpa [embStk,haloClassMetadataPlacement,haloClassBinaryValue,couplingIntervalValue] using
        hmeta.encoded 154 (by decide)
  have hblank' : ∀ r, (embStk haloClassMetadataPlacement S).R (originReg r) = [] := by
    intro r
    have hr := originReg_range r
    have hp := haloClassMetadataPlacement_low (originReg r) (by omega)
    simpa only [embStk,Function.comp_apply,hp] using
      hblank ⟨(originReg r).val,by omega⟩ hr
  obtain ⟨v₁,m,hu₁,hm,he⟩ := binaryHaloClass_exec (body := fun p : Empty => nomatch p)
    hs hst hband hab hb hL hLs hA hwide (embDn haloClassMetadataPlacement v) (embStk haloClassMetadataPlacement S)
    (by simpa [embStk,haloClassMetadataPlacement] using hmeta.width) hsrc hblank'
    (by simpa [embStk,haloClassMetadataPlacement] using h104)
    (by simpa [embStk,haloClassMetadataPlacement] using h106)
    (by simpa [embStk,haloClassMetadataPlacement] using h116)
  obtain ⟨v₂,hv₂,hu₂,he₂⟩ := exec_emb_ovr (ι := Empty.elim) (body' := body)
    haloClassMetadataPlacement_injective (fun p => nomatch p) he v rfl S rfl
  refine ⟨v₂,m,hu₂.trans hu₁,hm,he₂.cast rfl ?_⟩
  apply congrArg (mk v₂)
  let T₀ := embStk haloClassMetadataPlacement S
  let T₁ : Stacks 117 A := {T₀ with R := Function.update T₀.R 109 (haloOriginPackets A V s t band a b L++T₀.R 109)}
  let T₂ : Stacks 117 A := {T₁ with R := Function.update T₁.R 116 (List.replicate (haloLengthGroup s t band a b L).length tick)}
  change embOvr haloClassMetadataPlacement T₂.get S = _
  dsimp only [T₂]
  rw [embOvr_updR haloClassMetadataPlacement_injective]
  dsimp only [T₁,T₀]
  rw [embOvr_updR haloClassMetadataPlacement_injective,embOvr_stk]
  rfl

/-- The controller's ambient packets are exactly the packed batch's origin stream. -/
theorem haloOriginPackets_eq_packed (A V s t band a b L : ℕ) :
    haloOriginPackets A V s t band a b L =
      ((haloPackedOffsets s t band a b L).map (a+·)).flatMap (binSyms V) := by
  have horigins : (haloPackedOffsets s t band a b L).map (a+·) = haloOrigins s t band a b L := by
    simp only [haloPackedOffsets,List.map_map]
    calc
      _ = (haloOrigins s t band a b L).map id := by
        apply List.map_congr_left
        intro p hp
        exact Nat.add_sub_of_le (haloOrigins_bounds s t band a b L p hp).1
      _ = _ := List.map_id _
  rw [horigins]
  simp only [haloOriginPackets,haloOrigins,List.flatMap_map]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
