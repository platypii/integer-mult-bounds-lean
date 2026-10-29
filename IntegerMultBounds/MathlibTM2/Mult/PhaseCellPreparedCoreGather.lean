module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedCoreGather
public import IntegerMultBounds.MathlibTM2.Mult.ChirpBankLoad
public import IntegerMultBounds.MathlibTM2.Host.Embed

/-! Build the core controller from retained binary geometry, then execute the
restoring sweep. No initialized controller table or origin stream is supplied. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellMatrix

variable {Q A : ℕ} {U P : Type} {body : P → Pr P 168 Q A U}

def coreGatherReg : Fin 117 → Fin 168 := Fin.castLE (by decide)

theorem coreGatherReg_injective : Function.Injective coreGatherReg := by
  intro i j he
  exact Fin.ext (congrArg (fun k : Fin 168 => k.val) he)

def coreGatherTableReg (r : TblR 16) : Fin 168 := coreGatherReg (originReg r)

theorem coreGatherTableReg_range (r : TblR 16) : (coreGatherTableReg r).val < 31 :=
  originReg_range r

def coreGatherSource (i : Fin 16) : Fin 168 :=
  if i = 0 then 145 else if i = 1 then 150 else if i = 2 then 152 else
    if i = 3 then 165 else 154

def coreGatherBits (V : ℕ) (k : Fin 168) : ℕ := if k = 154 then 0 else V

def coreGatherValue (s width radius L : ℕ) (k : Fin 168) : ℕ :=
  if k = 145 then s else if k = 150 then width else if k = 152 then radius else
    if k = 165 then L else 0

def preparedCoreGather : Pr P 168 Q A U :=
  .seq (chirpBankLoad coreGatherTableReg coreGatherSource 163 163)
    (embProg coreGatherReg Empty.elim (generatedCoreGather (P := Empty)))

theorem coreGatherLoad_cost (V : ℕ) :
    chirpBankLoadCost coreGatherTableReg coreGatherSource V V (coreGatherBits V) = 112*V+137 := by
  simp [chirpBankLoadCost, chirpBankCopiesCost, chirpBankInputAssignments,
    coreGatherSource, coreGatherBits, List.ofFn_succ]
  ring

theorem preparedCoreGather_exec {V s width radius L w : ℕ}
    (hwidth : 0 < width) (hwide : s+width+2*radius < 2^V) (hLfit : L < 2^V)
    (hwV : w < 2^V) (hvol : s*w < 2^V) (hA : 4 ≤ A) (hVpos : 0 < V)
    (hgroup : 0 < (coreGatherIndices s width radius L).length)
    (v : HS 168 Q A U) (S : Stacks 168 A)
    (h163 : (S.R 163).length = V) (h115 : (S.R 115).length = V)
    (hs : S.R 145 = binSyms V s) (hw : S.R 150 = binSyms V width)
    (hr : S.R 152 = binSyms V radius) (hL : S.R 165 = binSyms V L) (hz : S.R 154 = [])
    (hblank : ∀ k : Fin 168, k.val < 31 → S.R k = [])
    (h104 : S.R 104 = []) (h106 : S.R 106 = []) (h116 : S.R 116 = [])
    (E : List (Fin (A+4))) (hlen : E.length = s*w) (hsource : S.R 110 = E)
    (hrows : (S.R 103).length = L) (hword : (S.R 94).length = w) (hcontrol : S.R 91 = [])
    (hclean : ∀ k ∈ [(92 : Fin 168), 93, 95, 96, 97, 98, 99, 100, 101, 102], S.R k = [])
    (hfresh : ∀ k ∈ [(88 : Fin 168), 89, 90], S.R k = []) :
    ∃ v' F n, v'.user = v.user ∧
      n ≤ (112*V+137) + ((18*((s+width-1)/width)+9)*tblC V V +
        (coreGatherIndices s width radius L).length*(8*V+6)+6 + (62*V+63) +
        preparedOriginAdvanceCost V s w (coreGatherIndices s width radius L).length +
        ((coreGatherIndices s width radius L).length*(14*L*w+25)+12*s*w+6*L*w+9*L+29)) ∧
      Exec body preparedCoreGather (mk v S) n (mk v' F) ∧
      F.inp = S.inp ∧ F.out = S.out ∧ F.L = S.L ∧
      F.R 108 = (coreGatherOrigins s width radius L w).flatMap
        (fun a => (E.drop a).take (L*w)) ++ S.R 108 ∧
      F.R 91 = coreGatherControls A s width radius L w ∧
      F.R 109 = (coreGatherIndices s width radius L).flatMap
        (fun k => binSyms V (coreStart width k-radius)) ++ S.R 109 ∧
      F.R 116 = List.replicate (coreGatherIndices s width radius L).length tick ∧
      ∀ k, k ≠ 108 → k ≠ 91 → k ≠ 109 → k ≠ 116 → F.R k = S.R k := by
  let value := coreGatherValue s width radius L
  let bits := coreGatherBits V
  have hinj : Function.Injective coreGatherTableReg :=
    coreGatherReg_injective.comp originReg_injective
  have hoff (k : Fin 168) (hk : 31 ≤ k.val) : ∀ r, coreGatherTableReg r ≠ k := by
    intro r he
    have hh := coreGatherTableReg_range r
    rw [he] at hh
    omega
  have hinput : ∀ i r, coreGatherTableReg r ≠ coreGatherSource i := by
    intro i
    apply hoff
    simp only [coreGatherSource]; split_ifs <;> decide
  have hfit : ∀ i, value (coreGatherSource i) < 2^bits (coreGatherSource i) := by
    intro i
    simp only [coreGatherSource]
    split_ifs <;> simp [value, bits, coreGatherValue, coreGatherBits] <;> omega
  have hbits : ∀ i, bits (coreGatherSource i) ≤ V := by
    intro i
    simp [bits, coreGatherBits]
    split_ifs <;> omega
  have hsrc : ∀ i, S.R (coreGatherSource i) =
      binSyms (bits (coreGatherSource i)) (value (coreGatherSource i)) := by
    intro i
    simp only [coreGatherSource]
    split_ifs <;> simp [value, bits, coreGatherValue, coreGatherBits, hs, hw, hr, hL, hz, binSyms]
  have hb : ∀ r, S.R (coreGatherTableReg r) = [] := fun r => hblank _ (coreGatherTableReg_range r)
  obtain ⟨v₁, hu₁, he₁⟩ := chirpBankLoad_exec (body := body) coreGatherTableReg hinj coreGatherSource
    163 163 (hoff 163 (by decide)) (hoff 163 (by decide)) hinput V V bits value hfit hbits
    v S h163 h163 hsrc hb
  let B : Stacks 168 A := {S with R := chirpBankLoadR coreGatherTableReg coreGatherSource V V value S.R}
  let st : TblSt 16 A := ⟨fun i => value (coreGatherSource i), []⟩
  have hh : tblHolds originReg (embStk coreGatherReg B)
      (tblRho V (List.replicate V tick) (List.replicate V tick) st) :=
    chirpBankLoad_holds coreGatherTableReg hinj coreGatherSource V V value S hb
  have hframe (k : Fin 168) (hk : 31 ≤ k.val) : B.R k = S.R k :=
    chirpBankLoad_off coreGatherTableReg coreGatherSource V V value S.R k (fun r => (hoff k hk r).symm)
  have hlow (k : Fin 117) : 31 ≤ k.val → (embStk coreGatherReg B).R k = S.R (coreGatherReg k) :=
    hframe (coreGatherReg k)
  have hreg91 : coreGatherReg 91 = 91 := by decide
  have hreg94 : coreGatherReg 94 = 94 := by decide
  have hreg103 : coreGatherReg 103 = 103 := by decide
  have hreg104 : coreGatherReg 104 = 104 := by decide
  have hreg106 : coreGatherReg 106 = 106 := by decide
  have hreg108 : coreGatherReg 108 = 108 := by decide
  have hreg109 : coreGatherReg 109 = 109 := by decide
  have hreg110 : coreGatherReg 110 = 110 := by decide
  have hreg115 : coreGatherReg 115 = 115 := by decide
  have hreg116 : coreGatherReg 116 = 116 := by decide
  obtain ⟨vi, Fsmall, m, hui, hm, hei, hii, hoi, hli, h108, hR⟩ :=
    generatedCoreGather_exec (body := fun p : Empty => nomatch p) st
      (by simp [st, value, coreGatherSource, coreGatherValue])
      (by simp [st, value, coreGatherSource, coreGatherValue])
      (by simp [st, value, coreGatherSource, coreGatherValue])
      (by simp [st, value, coreGatherSource, coreGatherValue]) hwidth hwide hwV (by omega) hvol
      le_rfl hA hVpos (fun i => (hfit i).trans_le (Nat.pow_le_pow_right (by decide) (hbits i))) rfl
      hgroup (embDn coreGatherReg v₁) (embStk coreGatherReg B) hh
      (by simpa only [hlow 115 (by decide), hreg115] using h115)
      (by simpa only [hlow 94 (by decide), hreg94] using hword)
      (by simpa only [hlow 104 (by decide), hreg104] using h104)
      (by simpa only [hlow 106 (by decide), hreg106] using h106)
      (by simpa only [hlow 116 (by decide), hreg116] using h116)
      E hlen (by simpa only [hlow 110 (by decide), hreg110] using hsource)
      (by simpa only [hlow 103 (by decide), hreg103] using hrows)
      (by simpa only [hlow 91 (by decide), hreg91] using hcontrol)
      (by
        intro k hk
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          rw [hlow _ (by decide)] <;> apply hclean <;> simp [coreGatherReg])
      (by
        intro k hk
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl <;>
          rw [hlow _ (by decide)] <;> apply hfresh <;> simp [coreGatherReg])
  obtain ⟨v₂, F, he₂, hv₂, hu₂, hview, hbig⟩ := exec_emb coreGatherReg_injective
    (ι := Empty.elim) (body' := body) (fun p => nomatch p) hei v₁ rfl B rfl
  have hget (k : Fin 117) : F.R (coreGatherReg k) = Fsmall.R k :=
    congrArg (fun D : Stacks 117 A => D.R k) hview
  have hrest (k : Fin 117) (hk108 : k ≠ 108) : F.R (coreGatherReg k) =
      if k.val < 31 then [] else if k = 91 then coreGatherControls A s width radius L w ++ B.R 91 else
      if k = 109 then (coreGatherIndices s width radius L).flatMap
        (fun i => binSyms V (coreStart width i-radius)) ++ B.R 109 else
      if k = 116 then List.replicate (coreGatherIndices s width radius L).length tick else B.R (coreGatherReg k) := by
    rw [hget k, hR k hk108]
    rfl
  refine ⟨v₂, F, (112*V+137)+m, hu₂.trans (hui.trans hu₁), Nat.add_le_add_left hm _,
    Exec.seq (he₁.cast (coreGatherLoad_cost V) rfl) he₂,
    (congrArg (fun D : Stacks 117 A => D.inp) hview).trans hii,
    (congrArg (fun D : Stacks 117 A => D.out) hview).trans hoi, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · funext k
    by_cases hk : k.val < 117
    · let i : Fin 117 := ⟨k.val, hk⟩
      have heq : coreGatherReg i = k := Fin.ext rfl
      rw [← heq]
      exact (congrArg (fun D : Stacks 117 A => D.L i) hview).trans (congrFun hli i)
    · exact (hbig k (by intro i he; have hv := congrArg Fin.val he; have hi := i.isLt; change i.val = k.val at hv; omega)).1
  · simpa only [embStk, Function.comp_apply, hreg108, hframe 108 (by decide)] using (hget 108).trans h108
  · simpa [hreg91, hframe 91 (by decide), hcontrol] using hrest 91 (by decide)
  · simpa only [show ¬(109 : Fin 117).val < 31 by decide, show (109 : Fin 117) ≠ 91 by decide,
      ite_false, ite_true, hreg109, hframe 109 (by decide)] using hrest 109 (by decide)
  · simpa only [show ¬(116 : Fin 117).val < 31 by decide, show (116 : Fin 117) ≠ 91 by decide,
      show (116 : Fin 117) ≠ 109 by decide, ite_false, ite_true, hreg116] using hrest 116 (by decide)
  · intro k hk108 hk91 hk109 hk116
    by_cases hk : k.val < 117
    · let i : Fin 117 := ⟨k.val, hk⟩
      have heq : coreGatherReg i = k := Fin.ext rfl
      have hi108 : i ≠ 108 := by intro he; apply hk108; apply Fin.ext; exact congrArg (fun j : Fin 117 => j.val) he
      have hi91 : i ≠ 91 := by intro he; apply hk91; apply Fin.ext; exact congrArg (fun j : Fin 117 => j.val) he
      have hi109 : i ≠ 109 := by intro he; apply hk109; apply Fin.ext; exact congrArg (fun j : Fin 117 => j.val) he
      have hi116 : i ≠ 116 := by intro he; apply hk116; apply Fin.ext; exact congrArg (fun j : Fin 117 => j.val) he
      have hh := hrest i hi108
      rw [heq] at hh
      by_cases h31 : k.val < 31
      · simpa [i, h31, hblank k h31] using hh
      · simpa [i, h31, hi91, hi109, hi116, hframe k (by omega)] using hh
    · exact ((hbig k (by intro i he; have hv := congrArg Fin.val he; have hi := i.isLt; change i.val = k.val at hv; omega)).2).trans
        (hframe k (by omega))

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
