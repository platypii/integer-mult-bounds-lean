module

public import IntegerMultBounds.Schoenhage.RingLemmaHeader
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import IntegerMultBounds.MathlibTM2.Fast.CMulPass
public import IntegerMultBounds.MathlibTM2.Host.WordCmd

/-!
# The vendored ring product as a host subroutine: program, costs and formats

The vendored signed ring product (`Schoenhage/RingLemma`: header decoder `decodeHeader3`,
constants, one packed Schönhage–Strassen product per record pair) is the word program
`pwCoreWith decodeHeader3` over 91 word tapes; it runs on any number of record pairs.

**The word program** (`runs_pwCoreWith`). Tape `zH` holds the header `Γ(p)Γ(r)Γ(w)`
(`header p r w`, `r = 2^l`), tapes `zF`, `zG` the arrays `array w fs`, `array w gs` of `M`
records each (`Spec.SignedRingProduct.array`: each coefficient as the real then the imaginary
numerator, both signed `w`-bit two's-complement words, most significant bit first), each as a
single word; every other tape is empty. For `1 ≤ p`, `p + 2 ≤ w` and disk-grid records it ends
within `pwCost p 0 l 0 w H M X` steps with `array w (zipWith (prodRec p) fs gs)` on `zO`: record
`n` is `Q_p(f_n g_n / r)` (`prodRec`). `pwCost` charges
`M (r (56 w + 400) + ringCost W r w (p + l) (W r) + 204)` for the records, `W = wOf p l w`, with
`ringCost` the bound of the packed product (`ringProgram`, truncation by `s = p + l` bits).
`rpTime` is `pwCost` plus a sealing allowance.

**On the host** (`rpHost`, `rpHost_exec`). The header and the operands are raw bit words on the
registers `ι 0`, `ι 1`, `ι 2` (empty left stacks), the output register `ι 3` and the registers
`ι j`, `j ≥ 4`, are empty. `rpSeal` appends a separator below each input word, so the registers
hold the placed start bank with the data tapes `zH`, `zF`, `zG`, `zO` on `ι 0`–`ι 3`
(`ι ∘ dataSwap`); `tcompile` runs the word program (`rpStates = cmdStates`); `rpUnseal` drops the
separators again. At most `3 · rpTime p l w M` steps, the output array on `ι 3`, every other
stack and the `user` component unchanged.

**Formats.** `rpLsb w v` are the `w` low bits of `v`, least significant first;
`msbBits w v = (rpLsb w v).reverse`. A host coefficient `csyms A w z` carries the bits
`rpLsb w (red w z).1.val` and `rpLsb w (red w z).2.val` as pair symbols; a vendored coefficient
is `rpChunk w z = compWord w z.re ++ compWord w z.im`, the two reversed bit lists
(`rp_compWord_eq_rev`). `rp_array_eq_chunks`: an array is the chunks of its coefficients in order
(`rpCoeffs`).

**Automata.** `rpEncAuto` copies a pair symbol and splits it into its real and imaginary bit
symbols, `rpCpyAuto` copies, `rpZipAuto` pairs two bit symbols; all are stateless, so a word's
outputs are the symbolwise images of its input columns (`rp_runWord_stateless`,
`rp_cols_one`, `rp_cols_two`).
-/

@[expose] public section


set_option maxRecDepth 10000

namespace IntegerMultBounds.MathlibTM2.Fast

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer
open IntegerMultBounds.Spec.SignedRingProduct

noncomputable section

/-! ### The ring product on host stacks -/

section Host

open IntegerMultBounds.Schoenhage (WTape Cmd cells emp startBank pwCoreWith pwCost decodeHeader3
  runs_pwCoreWith hdrDecodes_decodeHeader3 dataSwap)
open IntegerMultBounds.Schoenhage.Tp (zH zF zG zO)
open IntegerMultBounds.MathlibTM2.Host.WordCmd (regs regs_L_at regs_R_at regs_L_off regs_R_off
  regs_set moveRL moveRL_exec moveLR moveLR_exec pushL pushL_run place place_L_at place_R_at
  place_L_off place_R_off place_self lcells cells_cons' bitSymbol_ne_sep cmdStates tcompile
  tcompile_runs)

/-- The time bound of the ring product on `M` record pairs of `2^l` coefficients: the word-level
bound `pwCost` and the cost of sealing and unsealing the four data registers. -/
def rpTime (p l w M : ℕ) : ℕ :=
  pwCost p 0 l 0 w (header p (2 ^ l) w).length M (2 * 2 ^ l * w * M) +
    4 * ((header p (2 ^ l) w).length + 3 * (2 * 2 ^ l * w * M)) + 60

/-- The control-state count of the ring product's word program. -/
abbrev rpStates : ℕ := cmdStates (pwCoreWith decodeHeader3)

variable {T Q A : ℕ} {U P : Type} (body : P → Pr P T Q A U)

/-- Append a separator below the bit word on the right stack of `r`. -/
def rpSeal (r : Fin T) : Pr P T Q A U :=
  .seq (moveRL r (fun _ => true)) (.seq (.act (pushL r [separator])) (moveLR r (fun _ => true)))

/-- Drop the separator below the bit word on the right stack of `r`. -/
def rpUnseal (r : Fin T) : Pr P T Q A U :=
  .seq (moveRL r (· != separator))
    (.seq (.act (.pop (.rt r) (fun v _ => v) .done)) (moveLR r (fun _ => true)))

/-- The ring product on the registers `ι`: seal the header and the operands on `ι 0`, `ι 1`,
`ι 2`, run the word program with its data tapes `zH`, `zF`, `zG`, `zO` on `ι 0`–`ι 3`, unseal. -/
def rpHost (ι : Fin 91 → Fin T) : Pr P T Q A U :=
  .seq (rpSeal (ι 0)) <| .seq (rpSeal (ι 1)) <| .seq (rpSeal (ι 2)) <|
  .seq (tcompile (ι ∘ dataSwap) (pwCoreWith decodeHeader3)) <|
  .seq (rpUnseal (ι 3)) <| .seq (rpUnseal (ι 0)) <| .seq (rpUnseal (ι 1)) (rpUnseal (ι 2))

lemma rp_regs_one (S : Stacks T A) (r : Fin T) (F : Fin 1 → WordCmd.LR A) :
    regs S (fun _ => r) F = { S with
      L := Function.update S.L r (F 0).1
      R := Function.update S.R r (F 0).2 } := by
  have hj : Function.Injective (fun _ : Fin 1 => r) := Function.injective_of_subsingleton _
  ext1
  · rfl
  · rfl
  all_goals
    funext r'
    by_cases h : r' = r
    · subst h
      first | simpa using regs_L_at hj S F 0 | simpa using regs_R_at hj S F 0
    · have hoff : ∀ x : Fin 1, (fun _ => r) x ≠ r' := fun _ e => h e.symm
      first | simpa [h] using regs_L_off S F hoff | simpa [h] using regs_R_off S F hoff

lemma rp_update_one {α : Type} (F : Fin 1 → α) (a : α) : Function.update F 0 a = fun _ => a := by
  funext y
  rw [Subsingleton.elim y 0, Function.update_self]

/-- `moveRL_exec` on a raw register. -/
lemma rp_moveRL_exec (r : Fin T) (p : Fin (A + 4) → Bool) (l rest : List (Fin (A + 4)))
    (v : HS T Q A U) (S : Stacks T A) (hl : ∀ e ∈ l, p e = true)
    (hrest : (rest.head?.map p).getD false = false) (hS : S.R r = l ++ rest) :
    ∃ v', v'.user = v.user ∧ Exec body (moveRL r p) (mk v S) (2 * l.length + 2)
      (mk v' { S with
        L := Function.update S.L r (l.reverse ++ S.L r)
        R := Function.update S.R r rest }) := by
  have hj : Function.Injective (fun _ : Fin 1 => r) := Function.injective_of_subsingleton _
  have e : S = regs S (fun _ : Fin 1 => r) (fun _ : Fin 1 => (S.L r, S.R r)) := by
    rw [rp_regs_one]; simp
  obtain ⟨v', hu, he⟩ := moveRL_exec body hj S 0 p l rest (fun _ : Fin 1 => (S.L r, S.R r)) v hl
    hrest hS
  refine ⟨v', hu, ?_⟩
  rw [e]
  refine Exec.cast he rfl ?_
  rw [rp_update_one, rp_regs_one, rp_regs_one]
  simp

/-- Sealing a bit word: `4 |w| + 7` steps. -/
theorem rpSeal_exec (r : Fin T) (w : List Bool) (v : HS T Q A U) (S : Stacks T A)
    (hL : S.L r = []) (hR : S.R r = w.map bitSymbol) :
    ∃ v', v'.user = v.user ∧ Exec body (rpSeal r) (mk v S) (4 * w.length + 7)
      (mk v' { S with R := Function.update S.R r (cells [w]) }) := by
  obtain ⟨v₁, hu₁, he₁⟩ := rp_moveRL_exec body r (fun _ => true) (w.map bitSymbol) [] v S
    (fun _ _ => rfl) rfl (by rw [hR, List.append_nil])
  set S₁ : Stacks T A := { S with
    L := Function.update S.L r ((w.map bitSymbol).reverse ++ S.L r)
    R := Function.update S.R r [] }
  set S₂ : Stacks T A := { S with
    L := Function.update S.L r (separator :: (w.map bitSymbol).reverse)
    R := Function.update S.R r [] }
  have h₂ : (pushL r [separator] : Act T Q A U).run (mk v₁ S₁) = mk v₁ S₂ := by
    rw [pushL_run]
    simp [S₁, S₂, hL]
  obtain ⟨v₃, hu₃, he₃⟩ := moveLR_exec body r (fun _ => true)
    (separator :: (w.map bitSymbol).reverse) [] v₁ S₂ (fun _ _ => rfl) rfl (by simp [S₂])
  refine ⟨v₃, hu₃.trans hu₁, Exec.cast (Exec.seq he₁ (Exec.seq
    (h₂ ▸ Exec.act (body := body) (pushL r [separator]) (mk v₁ S₁)) he₃)) (by simp; ring) ?_⟩
  congr 1
  simp only [S₂, Function.update_self, Function.update_idem, List.reverse_cons,
    List.reverse_reverse, List.append_nil, cells_cons']
  rw [show Function.update S.L r [] = S.L from Function.update_eq_self_iff.2 hL.symm]
  rfl

/-- Unsealing a bit word: `4 |w| + 5` steps. -/
theorem rpUnseal_exec (r : Fin T) (w : List Bool) (v : HS T Q A U) (S : Stacks T A)
    (hL : S.L r = []) (hR : S.R r = cells [w]) :
    ∃ v', v'.user = v.user ∧ Exec body (rpUnseal r) (mk v S) (4 * w.length + 5)
      (mk v' { S with R := Function.update S.R r (w.map bitSymbol) }) := by
  obtain ⟨v₁, hu₁, he₁⟩ := rp_moveRL_exec body r (· != separator) (w.map bitSymbol) [separator] v S
    (fun e he => by
      obtain ⟨b, -, rfl⟩ := List.mem_map.1 he
      simpa using bitSymbol_ne_sep b)
    (by simp) (by rw [hR, cells_cons']; rfl)
  set S₁ : Stacks T A := { S with
    L := Function.update S.L r ((w.map bitSymbol).reverse ++ S.L r)
    R := Function.update S.R r [separator] }
  set S₂ : Stacks T A := { S with
    L := Function.update S.L r (w.map bitSymbol).reverse
    R := Function.update S.R r [] }
  have h₂ : (.pop (.rt r) (fun v _ => v) .done : Act T Q A U).run (mk v₁ S₁) = mk v₁ S₂ := by
    simp [Action.run, S₁, S₂, hL, update_rt]
  obtain ⟨v₃, hu₃, he₃⟩ := moveLR_exec body r (fun _ => true) (w.map bitSymbol).reverse [] v₁ S₂
    (fun _ _ => rfl) rfl (by simp [S₂])
  refine ⟨v₃, hu₃.trans hu₁, Exec.cast (Exec.seq he₁ (Exec.seq
    (h₂ ▸ Exec.act (body := body) (.pop (.rt r) (fun v _ => v) .done) (mk v₁ S₁)) he₃))
    (by simp; ring) ?_⟩
  congr 1
  simp only [S₂, Function.update_self, Function.update_idem, List.reverse_reverse, List.append_nil]
  rw [show Function.update S.L r [] = S.L from Function.update_eq_self_iff.2 hL.symm]

/-- Placing a bank that differs from a placed bank in one tape. -/
lemma rp_place_update {t : ℕ} {ι : Fin t → Fin T} (hι : Function.Injective ι) (S : Stacks T A)
    (σ : Fin t → WTape) (x : Fin t) (τ : WTape) :
    place S ι (Function.update σ x τ) = { place S ι σ with
      L := Function.update (place S ι σ).L (ι x) (lcells τ.left)
      R := Function.update (place S ι σ).R (ι x) (cells τ.right) } := by
  ext1
  · rfl
  · rfl
  all_goals
    funext r
    by_cases h : ∃ y, ι y = r
    · obtain ⟨y, rfl⟩ := h
      by_cases hy : y = x
      · subst hy
        simp [place_L_at hι, place_R_at hι]
      · have hne : ι y ≠ ι x := fun e => hy (hι e)
        simp [place_L_at hι, place_R_at hι, hne, hy]
    · have hoff : ∀ y, ι y ≠ r := fun y e => h ⟨y, e⟩
      have hne : r ≠ ι x := fun e => hoff x e.symm
      simp [place_L_off _ _ hoff, place_R_off _ _ hoff, hne]

lemma rp_dataSwap_ge {x : Fin 91} (h0 : x ≠ zH) (h1 : x ≠ zF) (h2 : x ≠ zG) (h3 : x ≠ zO) :
    4 ≤ (dataSwap x).val := by
  have e : ∀ k : Fin 91, dataSwap x = k ↔ x = dataSwap.symm k :=
    fun _ => (Equiv.eq_symm_apply dataSwap).symm
  have n0 : dataSwap x ≠ 0 := fun h => h0 ((e 0).1 h)
  have n1 : dataSwap x ≠ 1 := fun h => h1 ((e 1).1 h)
  have n2 : dataSwap x ≠ 2 := fun h => h2 ((e 2).1 h)
  have n3 : dataSwap x ≠ 3 := fun h => h3 ((e 3).1 h)
  simp only [ne_eq, Fin.ext_iff] at n0 n1 n2 n3
  omega

set_option maxRecDepth 1000 in
/-- A sealed host bank is exactly the word program's placed initial bank.
The layout proof is structural over an arbitrary injective placement. -/
lemma rp_place_start {ι : Fin 91 → Fin T} (hι : Function.Injective ι)
    (S : Stacks T A) (hdr F G : List Bool)
    (hL : ∀ j, S.L (ι j) = []) (h0 : S.R (ι 0) = cells [hdr])
    (h1 : S.R (ι 1) = cells [F]) (h2 : S.R (ι 2) = cells [G])
    (h3 : S.R (ι 3) = []) (hpriv : ∀ j : Fin 91, 4 ≤ j.val → S.R (ι j) = []) :
    place S (ι ∘ dataSwap) (startBank hdr F G) = S := by
  have he : Function.Injective (ι ∘ dataSwap) := hι.comp dataSwap.injective
  refine place_self he (fun x => ?_) (fun x => ?_)
  · have hx : (startBank hdr F G x).left = [] := by
      simp only [startBank,Function.update_apply]; split_ifs <;> rfl
    rw [hx]
    exact hL _
  · by_cases x0 : x = zH
    · subst x
      simpa only [Function.comp_apply,show dataSwap zH = 0 from rfl,startBank,
        Function.update_of_ne (by decide : zH ≠ zG),Function.update_of_ne (by decide : zH ≠ zF),
        Function.update_self,Schoenhage.reg] using h0
    by_cases x1 : x = zF
    · subst x
      simpa only [Function.comp_apply,show dataSwap zF = 1 from rfl,startBank,
        Function.update_of_ne (by decide : zF ≠ zG),Function.update_self,Schoenhage.reg] using h1
    by_cases x2 : x = zG
    · subst x
      simpa only [Function.comp_apply,show dataSwap zG = 2 from rfl,startBank,
        Function.update_self,Schoenhage.reg] using h2
    have hx : startBank hdr F G x = emp := by simp [startBank,x0,x1,x2]
    rw [hx]
    by_cases x3 : x = zO
    · subst x
      simpa only [Function.comp_apply,show dataSwap zO = 3 from rfl,emp,Schoenhage.cells,Schoenhage.syms,List.flatMap_nil,List.map_nil] using h3
    exact hpriv _ (rp_dataSwap_ge x0 x1 x2 x3)

/-- The ring product on host stacks: the header and the operand arrays as bit words on `ι 0`,
`ι 1`, `ι 2`, the output array onto the empty `ι 3`, within `3 · rpTime` steps. -/
theorem rpHost_exec {ι : Fin 91 → Fin T} (hι : Function.Injective ι) (hQ : rpStates ≤ Q)
    {p l w : ℕ} {fs gs : List (Rec (2 ^ l))} (hp : 1 ≤ p) (hw : p + 2 ≤ w)
    (hlen : fs.length = gs.length) (hf : ∀ f ∈ fs, DiskGrid p f.1 f.2)
    (hg : ∀ g ∈ gs, DiskGrid p g.1 g.2) (v : HS T Q A U) (S : Stacks T A)
    (hL : ∀ j, S.L (ι j) = []) (h0 : S.R (ι 0) = (header p (2 ^ l) w).map bitSymbol)
    (h1 : S.R (ι 1) = (array w fs).map bitSymbol) (h2 : S.R (ι 2) = (array w gs).map bitSymbol)
    (h3 : S.R (ι 3) = []) (hpriv : ∀ j : Fin 91, 4 ≤ j.val → S.R (ι j) = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ 3 * rpTime p l w fs.length ∧
      Exec body (rpHost ι) (mk v S) n (mk v' { S with
        R := Function.update S.R (ι 3) ((array w (List.zipWith (prodRec p) fs gs)).map bitSymbol) }) := by
  set hdr := header p (2 ^ l) w
  set F := array w fs
  set G := array w gs
  set out := array w (List.zipWith (prodRec p) fs gs)
  have n01 : ι 0 ≠ ι 1 := fun e => absurd (hι e) (by decide)
  have n02 : ι 0 ≠ ι 2 := fun e => absurd (hι e) (by decide)
  have n03 : ι 0 ≠ ι 3 := fun e => absurd (hι e) (by decide)
  have n12 : ι 1 ≠ ι 2 := fun e => absurd (hι e) (by decide)
  have n13 : ι 1 ≠ ι 3 := fun e => absurd (hι e) (by decide)
  have n23 : ι 2 ≠ ι 3 := fun e => absurd (hι e) (by decide)
  -- seal the header and the operands
  obtain ⟨v₁, hu₁, he₁⟩ := rpSeal_exec body (ι 0) hdr v S (hL 0) h0
  set S₁ : Stacks T A := { S with R := Function.update S.R (ι 0) (cells [hdr]) }
  obtain ⟨v₂, hu₂, he₂⟩ := rpSeal_exec body (ι 1) F v₁ S₁ (hL 1) (by simp [S₁, n01.symm, h1])
  set S₂ : Stacks T A := { S₁ with R := Function.update S₁.R (ι 1) (cells [F]) }
  obtain ⟨v₃, hu₃, he₃⟩ := rpSeal_exec body (ι 2) G v₂ S₂ (hL 2)
    (by simp [S₂, S₁, n02.symm, n12.symm, h2])
  set S₃ : Stacks T A := { S₂ with R := Function.update S₂.R (ι 2) (cells [G]) }
  -- the sealed stacks are the placed start bank
  have hι' : Function.Injective (ι ∘ dataSwap) := hι.comp dataSwap.injective
  have hS₃ : place S₃ (ι ∘ dataSwap) (startBank hdr F G) = S₃ := by
    apply rp_place_start hι S₃ hdr F G hL
    · simp [S₃,S₂,S₁,n02,n01]
    · simp [S₃,S₂,S₁,n12]
    · simp [S₃]
    · simpa [S₃,S₂,S₁,n03.symm,n13.symm,n23.symm] using h3
    · intro j hj
      have n0 : ι j ≠ ι 0 := hι.ne (by intro e; subst j; norm_num at hj)
      have n1 : ι j ≠ ι 1 := hι.ne (by intro e; subst j; norm_num at hj)
      have n2 : ι j ≠ ι 2 := hι.ne (by intro e; subst j; norm_num at hj)
      simpa [S₃,S₂,S₁,n0,n1,n2] using hpriv j hj
  -- the word program
  obtain ⟨σ', hσ', v₄, m₄, hu₄, hm₄, he₄⟩ := tcompile_runs (body := body) hι'
    (runs_pwCoreWith (hdrDecodes_decodeHeader3 (l := l) hp (by omega)) hw hlen hf hg) hQ v₃ S₃
  rw [hS₃] at he₄
  subst hσ'
  have hzO : (ι ∘ dataSwap) zO = ι 3 := rfl
  have hS₄ : place S₃ (ι ∘ dataSwap) (Function.update (startBank hdr F G) zO (Schoenhage.reg out)) =
      { S₃ with R := Function.update S₃.R (ι 3) (cells [out]) } := by
    rw [rp_place_update hι', hS₃, hzO]
    simp only [Schoenhage.reg, lcells]
    rw [show Function.update S₃.L (ι 3) [] = S₃.L from Function.update_eq_self_iff.2 (hL 3).symm]
  rw [hS₄] at he₄
  set S₄ : Stacks T A := { S₃ with R := Function.update S₃.R (ι 3) (cells [out]) }
  -- unseal the four data registers
  obtain ⟨v₅, hu₅, he₅⟩ := rpUnseal_exec body (ι 3) out v₄ S₄ (hL 3) (by simp [S₄])
  set S₅ : Stacks T A := { S₄ with R := Function.update S₄.R (ι 3) (out.map bitSymbol) }
  obtain ⟨v₆, hu₆, he₆⟩ := rpUnseal_exec body (ι 0) hdr v₅ S₅ (hL 0)
    (by simp [S₅, S₄, S₃, S₂, S₁, n03, n02, n01])
  set S₆ : Stacks T A := { S₅ with R := Function.update S₅.R (ι 0) (hdr.map bitSymbol) }
  obtain ⟨v₇, hu₇, he₇⟩ := rpUnseal_exec body (ι 1) F v₆ S₆ (hL 1)
    (by simp [S₆, S₅, S₄, S₃, S₂, S₁, n01.symm, n13, n12])
  set S₇ : Stacks T A := { S₆ with R := Function.update S₆.R (ι 1) (F.map bitSymbol) }
  obtain ⟨v₈, hu₈, he₈⟩ := rpUnseal_exec body (ι 2) G v₇ S₇ (hL 2)
    (by simp [S₇, S₆, S₅, S₄, S₃, S₂, S₁, n02.symm, n12.symm, n23])
  refine ⟨v₈, _, hu₈.trans (hu₇.trans (hu₆.trans (hu₅.trans (hu₄.trans (hu₃.trans (hu₂.trans hu₁)))))),
    ?_, Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃ (Exec.seq he₄ (Exec.seq he₅
      (Exec.seq he₆ (Exec.seq he₇ (Exec.cast he₈ rfl ?_)))))))⟩
  · have hF : (array w fs).length = 2 * 2 ^ l * w * fs.length := by rw [length_array]
    have hG : (array w gs).length = 2 * 2 ^ l * w * fs.length := by rw [length_array, hlen]
    have hO : (array w (List.zipWith (prodRec p) fs gs)).length = 2 * 2 ^ l * w * fs.length := by
      rw [length_array, List.length_zipWith, hlen, min_self]
    simp only [hdr, F, G, out, rpTime, hF, hG, hO] at hm₄ ⊢
    omega
  · congr 1
    ext1
    · rfl
    · rfl
    · rfl
    funext r
    by_cases r0 : r = ι 0
    · subst r0; simp [S₇, S₆, S₅, S₄, S₃, S₂, S₁, n01, n02, n03, h0, hdr]
    by_cases r1 : r = ι 1
    · subst r1; simp [S₇, S₆, S₅, S₄, S₃, S₂, S₁, n12, n13, h1, F]
    by_cases r2 : r = ι 2
    · subst r2; simp [S₇, S₆, S₅, S₄, S₃, S₂, S₁, n23, h2, G]
    by_cases r3 : r = ι 3
    · subst r3; simp [S₇, S₆, S₅, S₄, S₃, S₂, S₁, n03.symm, n13.symm, n23.symm]
    simp [S₇, S₆, S₅, S₄, S₃, S₂, S₁, r0, r1, r2, r3]

end Host

/-! ### Bit formats -/

lemma rp_bitSymbol_ne_blank {A : ℕ} (b : Bool) : (bitSymbol b : Fin (A + 4)) ≠ blank := by
  cases b <;> simp [bitSymbol, blank, Fin.ext_iff]

/-- The `w` low bits of `v`, least significant first. -/
def rpLsb (w v : ℕ) : List Bool := List.ofFn fun t : Fin w => v.testBit t

@[simp] lemma length_rpLsb (w v : ℕ) : (rpLsb w v).length = w := by simp [rpLsb]

/-- Most significant bit first is the reverse of least significant bit first. -/
lemma rp_msbBits_eq_rev (w v : ℕ) : msbBits w v = (rpLsb w v).reverse := by
  induction w with
  | zero => rfl
  | succ n ih =>
      have e : rpLsb (n + 1) v = rpLsb n v ++ [v.testBit n] := by
        simp only [rpLsb, List.ofFn_succ', List.concat_eq_append, Fin.val_castSucc, Fin.val_last]
      rw [msbBits, ih, e, List.reverse_append]
      simp [Nat.testBit_eq_decide_div_mod_eq]

/-- A two's-complement word is the reversed low bits of the residue. -/
lemma rp_compWord_eq_rev (w : ℕ) (x : ℤ) :
    compWord w x = (rpLsb w (x : ZMod (2 ^ w)).val).reverse := by
  rw [compWord, rp_msbBits_eq_rev]
  congr 2
  have h := ZMod.val_intCast (n := 2 ^ w) x
  push_cast at h
  omega

/-- The vendored chunk of a coefficient: its real then its imaginary numerator. -/
def rpChunk (w : ℕ) (z : GaussianInt) : List Bool := compWord w z.re ++ compWord w z.im

@[simp] lemma length_rpChunk (w : ℕ) (z : GaussianInt) : (rpChunk w z).length = 2 * w := by
  simp [rpChunk, compWord]; ring

/-- The coefficients of a list of records, in order. -/
def rpCoeffs {r : ℕ} (fs : List (Rec r)) : List GaussianInt :=
  fs.flatMap fun f => List.ofFn fun c => (⟨f.1 c, f.2 c⟩ : GaussianInt)

/-- An array is the chunks of its coefficients. -/
lemma rp_array_eq_chunks {r : ℕ} (w : ℕ) (fs : List (Rec r)) :
    array w fs = (rpCoeffs fs).flatMap (rpChunk w) := by
  simp only [array, record, rpCoeffs, List.flatMap_assoc, rpChunk, List.ofFn_eq_map,
    List.flatMap_map]

/-- The real bits of a host coefficient. -/
lemma rp_csyms_map_re {A : ℕ} (hA : 4 ≤ A) (w : ℕ) (z : GaussianInt) :
    (csyms A w z).map (fun x => (bitSymbol (pairRe x) : Fin (A + 4))) =
      (rpLsb w (z.re : ZMod (2 ^ w)).val).map bitSymbol := by
  simp [csyms, coeffSyms, rpLsb, List.map_ofFn, Function.comp_def, pairRe_pairSym hA, red]

/-- The imaginary bits of a host coefficient. -/
lemma rp_csyms_map_im {A : ℕ} (hA : 4 ≤ A) (w : ℕ) (z : GaussianInt) :
    (csyms A w z).map (fun x => (bitSymbol (pairIm x) : Fin (A + 4))) =
      (rpLsb w (z.im : ZMod (2 ^ w)).val).map bitSymbol := by
  simp [csyms, coeffSyms, rpLsb, List.map_ofFn, Function.comp_def, pairIm_pairSym hA, red]

/-- Pairing the real and imaginary bits gives the host coefficient. -/
lemma rp_zip_csyms {A : ℕ} (w : ℕ) (z : GaussianInt) :
    List.zipWith (fun x y : Fin (A + 4) => pairSym A (symBit x) (symBit y))
      ((rpLsb w (z.re : ZMod (2 ^ w)).val).map bitSymbol)
      ((rpLsb w (z.im : ZMod (2 ^ w)).val).map bitSymbol) = csyms A w z := by
  apply List.ext_getElem (by simp)
  intro i h₁ h₂
  simp [csyms, coeffSyms, rpLsb, red]

/-! ### Stateless automata -/

section Autos

variable {A : ℕ}

/-- Copy a pair symbol and split it into its real and imaginary bit symbols. -/
def rpEncAuto (A : ℕ) : Auto A 1 3 where
  init := blank
  step s c := (s, ![c 0, bitSymbol (pairRe (c 0)), bitSymbol (pairIm (c 0))])

/-- Copy a symbol. -/
def rpCpyAuto (A : ℕ) : Auto A 1 1 where
  init := blank
  step s c := (s, fun _ => c 0)

/-- Pair a real and an imaginary bit symbol. -/
def rpZipAuto (A : ℕ) : Auto A 2 1 where
  init := blank
  step s c := (s, fun _ => pairSym A (symBit (c 0)) (symBit (c 1)))

/-- A stateless automaton maps each input column. -/
lemma rp_runWord_stateless {ni no : ℕ} (M : Auto A ni no) (hM : ∀ s c, (M.step s c).1 = s) :
    ∀ (s : Fin (A + 4)) (cs : List (Fin ni → Fin (A + 4))),
      M.runWord s cs = cs.map fun c => (M.step s c).2 := by
  intro s cs
  induction cs with
  | nil => rfl
  | cons c cs ih => simp [Auto.runWord, hM, ih]

/-- The columns of a word, mapped through the symbol of one register, read off that register. -/
lemma rp_cols_one {ni : ℕ} {β : Type} (L : Fin ni → List (Fin (A + 4))) (i : Fin ni)
    (c rest : List (Fin (A + 4))) (hL : L i = c ++ rest) {len : ℕ} (hc : c.length = len)
    (f : (Fin ni → Fin (A + 4)) → β) (g : Fin (A + 4) → β) (hf : ∀ col, f col = g (col i)) :
    (Auto.cols L len 0).map f = c.map g := by
  subst hc
  apply List.ext_getElem (by simp [Auto.cols])
  intro t h₁ h₂
  simp only [List.length_map] at h₂
  simp [Auto.cols, hf, hL, List.getD_eq_getElem?_getD, List.getElem?_append_left h₂,
    List.getElem?_eq_getElem h₂]

/-- The columns of a word, mapped through the symbols of two registers, read off both. -/
lemma rp_cols_two {ni : ℕ} {β : Type} (L : Fin ni → List (Fin (A + 4))) (i i' : Fin ni)
    (c c' rest rest' : List (Fin (A + 4))) (hL : L i = c ++ rest) (hL' : L i' = c' ++ rest')
    {len : ℕ} (hc : c.length = len) (hc' : c'.length = len)
    (f : (Fin ni → Fin (A + 4)) → β) (g : Fin (A + 4) → Fin (A + 4) → β)
    (hf : ∀ col, f col = g (col i) (col i')) :
    (Auto.cols L len 0).map f = List.zipWith g c c' := by
  subst hc
  apply List.ext_getElem (by simp [Auto.cols, hc'])
  intro t h₁ h₂
  simp only [List.length_map, Auto.cols, List.length_range] at h₁
  have h₃ : t < c'.length := by omega
  simp [Auto.cols, hf, hL, hL', List.getD_eq_getElem?_getD, List.getElem?_append_left h₁,
    List.getElem?_append_left h₃, List.getElem?_eq_getElem h₁, List.getElem?_eq_getElem h₃]

end Autos

end

end IntegerMultBounds.MathlibTM2.Fast
