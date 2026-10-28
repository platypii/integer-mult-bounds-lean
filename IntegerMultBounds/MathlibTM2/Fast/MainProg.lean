module

public import IntegerMultBounds.MathlibTM2.Fast.MainRegs
public import IntegerMultBounds.MathlibTM2.StackResources
public import IntegerMultBounds.MathlibTM2.Fast.SrcDirectStage
public import IntegerMultBounds.MathlibTM2.Cost.Total
public import IntegerMultBounds.MathlibTM2.Fast.ParamMachine
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein

/-!
# The top-level host program of the fast multiplier

`mnFast distP fwdP oppP` is the single host program of the fast multiplier (`docs/fast-pipeline`,
stages F1–F11) on the register file of `Fast/MainRegs`. Its two abstract parts are the
parameter distribution `distP` and the synthetic transforms `fwdP`, `oppP` (inside the source
transforms); their contracts are `MnDistSpec` and `SynFwdSpec`/`SynOppSpec` (`Fast/ConvSpec`).

## Program

1. `mnRead`: F1, `readInput` onto `io .rx`, `io .ry` (LSB first).
2. `mnLen`: the unary input length on `io .uN` (copies of `rx` and `ry`).
3. `mnParams`: F2, `pmParams` on the layout `pm`, the streams onto `io .oT`, `io .oS`, and the
   unary copies `mnUs` of `b`, `p`, `S` for the digit, rounding and output stages.
4. `distP`: the parameter distribution (`MnDistSpec`).
5. `mnChain fwdP oppP`: F3 on `x`, `srcDirectP` (F4, F5), the result parked on `io .hx`; F3 on `y`,
   `srcDirectP` (F6); both boxes onto the convolution's product registers `src (.v (.cm .xs))`,
   `src (.v (.cm .ys))`; F7, the pointwise product (`cmulStream`); the operands cleared and the
   product moved onto `src (.x .sb)`; `oppDirectP` (F8, F9); the coefficient stream onto `rnd .src`;
   F10 (`roundStage`); the words onto `out .dat`.
6. `mnOut`: F11, `carryOut`.
7. `mnClear`: every register emptied (`emptyR`, `2 |R i| + 2` steps each).
8. `mnReset`: the local state set back to `mnV₀`.

## The distribution contract

`MnDistSpec body distP n w E σ c`: from any store with empty left stacks and multiplier
registers in which the parameter layout, the streams `oT`, `oS` and the unary length `uN` are as
`pmParams` leaves them and the source and reserved layer registers are empty (`MnPostParam`),
`distP` runs within `c` steps to a store with

* the source registers holding the file `E` (`MnDistOut.src`) and the reserved layer registers
  holding `σ` (the transforms' parameter registers);
* the unary `w` on `io .dwn` and `rnd .wn`, the rounding operand width `mnMw n w`, `topN` of it
  and the word size `mnWo n` on `rnd .mn`, `rnd .nn`, `rnd .wo`, `out .wr`, and `S²` in binary
  on `rnd .sq`;
* every register of `mnDistKeep` (the operand bits, the unary copies of `mnUs`, all scratch
  registers of the later stages) unchanged, the left stacks, the multiplier registers, `inp` and
  `out` unchanged.

The parameter layout, `uN`, `ct`, `oT`, `oS`, `tx`, `ty` and the reserved layer registers are
the distribution's to use.

## Hypotheses

`MnSyn K Lb w σ` bundles the transforms: programs `fwdP`, `oppP` meeting `SynFwdSpec`,
`SynOppSpec` on `src (.v .io)` for every main program, from stores meeting `mnSynPre σ` (empty left
stacks and multiplier registers, the reserved layer registers holding `σ n`), with a record order
`π`, step bounds `cF`, `cO` and `cF + cO = O(totConv)`, over an alphabet with
`prime + K ≥ 96`. `MnDist K Lb w σ` bundles the
distribution: `distP` meeting `MnDistSpec`, the file `E n` it produces with `SrcBase` for three
runs over base files `V₀ n`, `σ₀ n` and `SrcCrtBase`, the table word size `Wt`, the width
conditions of the stages, the lengths of the registers the first loaders clear, and
`cost n ≤ C n + C (b n + 1)^k`.

## Costs

`mnPreCost D Y n` is the sum of the stage bounds before the cleanup; `mnTime D Y c n =
mnPreCost + 2 (n + c · mnPreCost) + 2 mnT + 4`, where `c = mnPushC body` bounds the symbols one action
of the program pushes, so that the registers hold at most `n + c · mnPreCost` symbols before the
cleanup.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Fast.Main

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Src IntegerMultBounds.MathlibTM2.Fast.ResampA IntegerMultBounds.MathlibTM2.Fast.ChirpSt IntegerMultBounds.MathlibTM2.Fast.ConvSt
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.MathlibTM2.Mult.Sizes IntegerMultBounds.MathlibTM2.Mult.Pipeline
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open IntegerMultBounds.Schoenhage.Schedule (topN)
open Filter


noncomputable section

variable {A : ℕ}

/-! ### Registers by name -/

/-- A glue register. -/
abbrev mnIo (r : MnIO) : Fin mnT := mnRg (.io r)

/-- A source-transform register. -/
abbrev mnSrc (r : SrcR 6) : Fin mnT := mnRg (.src r)

/-- The layout of the parameter machine. -/
abbrev mnPm (r : TblR pmNV) : Fin mnT := mnRg (.pm r)

/-- The layout of the rounding stage. -/
abbrev mnRnd (r : RndReg) : Fin mnT := mnRg (.rnd r)

/-- The layout of the output stage. -/
abbrev mnOutR (r : OReg) : Fin mnT := mnRg (.out r)

/-- The complex-product registers of the convolution, used by the pointwise product. -/
abbrev mnCm (x : CR) : Fin mnT := mnRg (.src (.v (.cm x)))

/-! ### Widths of the last stages -/

/-- The operand width of the rounding products: `S² < 2^m` and `w ≤ m`. -/
def mnMw (n w : ℕ) : ℕ := w + 2 * Nat.size (S n)

/-- The word size of the coefficients of the product: every coefficient is below `2^Wo`. -/
def mnWo (n : ℕ) : ℕ := 2 * b n + 2 * Nat.size (S n) + 6

/-! ### The stages -/

/-- F1: read the input. -/
def mnRead : MnPr A := readInput (mnIo .tx) (mnIo .ty) (mnIo .rx) (mnIo .ry)

/-- The unary input length on `uN`: copies of the bits of both operands. -/
def mnLen : MnPr A :=
  .seq (copyR (mnIo .rx) (mnIo .uN) (mnIo .ct) id) (copyR (mnIo .ry) (mnIo .uN) (mnIo .ct) id)

/-- The unary copies of the parameter machine: `b`, `p`, `S` for the digit stage, `b`, `p` for
the rounding stage, `b` for the output stage. -/
def mnUs : List (Fin pmNV × Fin mnT) :=
  [(pmIb, mnIo .dbn), (pmIp, mnIo .dpn), (pmIS, mnIo .dsn), (pmIb, mnRnd .bn), (pmIp, mnRnd .pn),
    (pmIb, mnOutR .br)]

/-- F2: the parameter machine. -/
def mnParams : MnPr A := pmParams mnPm (mnIo .uN) (mnIo .oT) (mnIo .oS) mnUs

/-- F3: the digit records of the bits on `src` onto the CRT register `src (.c .str)`. -/
def mnDigits (src : MnIO) : MnPr A :=
  digitRecords (mnIo src) (mnIo .dbn) (mnIo .dpn) (mnIo .dwn) (mnIo .dsn) (mnIo .tpl) (mnIo .tmp)
    (mnIo .stmp) (mnIo .acc) (mnSrc (.c .str))

/-- A forward transfer through the spare `io .sp`. -/
def mnMv (a b : MnR) : MnPr A := srcMv mnRg a b (.io .sp)

/-- F7: the pointwise product on the convolution's complex-product registers. -/
def mnPoint : MnPr A := cmulStream mnCm (cmulOne mnι mnι_inj mnT_ge_64 mnQ_ss mnCm)

/-- F10: the rounding stage. -/
def mnRound : MnPr A := roundStage mnRnd mnι mnι_inj mnT_ge_64 mnQ_ss

/-- F11: the carries and the output. -/
def mnOut : MnPr A := carryOut mnOutR

/-- F3 to F10 on the register file between the distribution and the output. -/
def mnChain {K : ℕ} (fwdP oppP : MnPr (prime + K)) : MnPr (prime + K) :=
  .seq (mnDigits .rx) <| .seq (srcDirectP mnM fwdP oppP) <|
  .seq (mnMv (.src (.x .sb)) (.io .hx)) <|
  .seq (mnDigits .ry) <| .seq (srcDirectP mnM fwdP oppP) <|
  .seq (mnMv (.io .hx) (.src (.v (.cm .xs)))) <| .seq (mnMv (.src (.x .sb)) (.src (.v (.cm .ys)))) <|
  .seq mnPoint <| .seq (uclear (mnCm .xs)) <| .seq (uclear (mnCm .ys)) <|
  .seq (mnMv (.src (.v (.cm .out))) (.src (.x .sb))) <|
  .seq (oppDirectP mnM fwdP oppP) <|
  .seq (mnMv (.src (.c .str)) (.rnd .src)) <|
  .seq mnRound (mnMv (.rnd .dst) (.out .dat))

/-- Empty every register. -/
def mnClear : MnPr A := Prog.seqList ((List.finRange mnT).map emptyR)

/-- The local state at the start and at the end. -/
def mnV₀ : HS mnT mnQ A Unit :=
  ⟨false, none, ⟨0, mnQ_pos⟩, fun _ => blank, none, ()⟩

/-- Restore the local state. -/
def mnReset : MnPr A := .act (.load (fun _ => mnV₀) .done)

/-- The stages before the cleanup: F1, the length, F2, the distribution, F3 to F10, F11. -/
def mnPre {K : ℕ} (distP fwdP oppP : MnPr (prime + K)) : MnPr (prime + K) :=
  .seq (.seq mnRead mnLen) <| .seq mnParams <| .seq distP <| .seq (mnChain fwdP oppP) mnOut

/-- **The fast multiplier.** -/
def mnFast {K : ℕ} (distP fwdP oppP : MnPr (prime + K)) : MnPr (prime + K) :=
  .seq (mnPre distP fwdP oppP) (.seq mnClear mnReset)

/-! ### Pushes per action -/



/-! ### The distribution contract -/

/-- The registers the distribution keeps: the operand bits, the unary copies of `mnUs` and every
scratch register of the later stages. -/
def mnDistKeep : MnR → Prop
  | .src _ => False
  | .pm _ => False
  | .io r => r ≠ .tx ∧ r ≠ .ty ∧ r ≠ .uN ∧ r ≠ .ct ∧ r ≠ .oT ∧ r ≠ .oS ∧ r ≠ .dwn
  | .rnd r => r ≠ .wn ∧ r ≠ .mn ∧ r ≠ .nn ∧ r ≠ .sq ∧ r ≠ .wo
  | .out r => r ≠ .wr

/-- The registers the distribution fills with the parameters of the rounding and output stages:
the unary `w` on `io .dwn` and `rnd .wn`, the operand width, `topN` of it, `S²` and the word size
on `rnd .mn`, `rnd .nn`, `rnd .sq`, `rnd .wo`, the word size on `out .wr`. -/
def mnRndRegs : List MnR := [.io .dwn, .rnd .wn, .rnd .mn, .rnd .nn, .rnd .sq, .rnd .wo, .out .wr]

/-- The registers after the parameter machine at `n`, as far as the distribution reads them,
with the source and reserved layer registers and the registers `mnRndRegs` empty. -/
structure MnPostParam (R : Fin mnT → List (Fin (A + 4))) (n : ℕ) : Prop where
  var : ∀ i, R (mnPm (.v i)) = binSyms (pmW n) (pmVals n i)
  wr : R (mnPm .wr) = pmTicks A (pmW n)
  wn : R (mnPm .wn) = pmTicks A (pmW n)
  acc : R (mnPm .acc) = []
  z : ∀ j, R (mnPm (.z j)) = []
  oT : R (mnIo .oT) = pmTStream A (pmW n) n
  oS : R (mnIo .oS) = pmSStream A (pmW n) n
  uN : (R (mnIo .uN)).length = n
  src : ∀ r, R (mnSrc r) = []
  lay : ∀ x, R (mnLay x) = []
  rndEmpty : ∀ r ∈ mnRndRegs, R (mnRg r) = []

/-- The registers the distribution writes: the source file `E`, the transforms' parameter
registers `σ`, and the unary and binary parameters of the digit, rounding and output stages. -/
structure MnDistOut (R : Fin mnT → List (Fin (A + 4))) (n w : ℕ) (E : SrcF 6 A)
    (σ : LReg SXReg → List (Fin (A + 4))) : Prop where
  src : ∀ r, R (mnSrc r) = E.get r
  lay : ∀ x, R (mnLay x) = σ x
  dwn : (R (mnIo .dwn)).length = w
  rwn : (R (mnRnd .wn)).length = w
  rmn : (R (mnRnd .mn)).length = mnMw n w
  rnn : (R (mnRnd .nn)).length = topN (mnMw n w)
  rsq : R (mnRnd .sq) = binSyms (mnMw n w) (S n * S n)
  rwo : (R (mnRnd .wo)).length = mnWo n
  owr : (R (mnOutR .wr)).length = mnWo n

/-- **The distribution contract** at `n`, coefficient width `w`, output file `E`, transform
parameters `σ`, within `c` steps. -/
def MnDistSpec (body : MnProc → MnPr A) (distP : MnPr A) (n w : ℕ) (E : SrcF 6 A)
    (σ : LReg SXReg → List (Fin (A + 4))) (c : ℕ) : Prop :=
  ∀ (v : HS mnT mnQ A Unit) (S : Stacks mnT A), (∀ y, S.L y = []) → (∀ j, S.R (mnι j) = []) →
    MnPostParam S.R n →
    ∃ (v' : HS mnT mnQ A Unit) (S' : Stacks mnT A) (m : ℕ), m ≤ c ∧
      Exec body distP (mk v S) m (mk v' S') ∧
      S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧ (∀ j, S'.R (mnι j) = []) ∧
      MnDistOut S'.R n w E σ ∧ ∀ r, mnDistKeep r → S'.R (mnRg r) = S.R (mnRg r)

/-! ### The hypotheses -/

/-- The precondition of the transforms: empty left stacks and multiplier registers, and the
reserved layer registers holding `σ`. -/
def mnSynPre (σ : LReg SXReg → List (Fin (A + 4))) (S : Stacks mnT A) : Prop :=
  (∀ y, S.L y = []) ∧ (∀ j, S.R (mnι j) = []) ∧ ∀ x, S.R (mnLay x) = σ x

/-- **The synthetic transforms**: programs meeting the transform contracts of `Fast/ConvSpec` on
`src (.v .io)` for every main program, from stores meeting `mnSynPre (σ n)`, with record order `π n`
and step bounds `cF n`, `cO n`, `cF + cO = O(totConv)`, over an alphabet `prime + K ≥ 96`. -/
structure MnSyn (K : ℕ) (Lb : LProc → MnPr (prime + K)) (w : ℕ → ℕ)
    (σ : ℕ → LReg SXReg → List (Fin (prime + K + 4))) where
  fwdP : MnPr (prime + K)
  oppP : MnPr (prime + K)
  π : ℕ → ℕ → ℕ
  cF : ℕ → ℕ
  cO : ℕ → ℕ
  spec : ∀ᶠ n in atTop, ∀ mainP : MnPr (prime + K),
    SynFwdSpec (mnBody Lb mainP) fwdP (mnSrc (.v .io)) (mnSynPre (σ n)) (w n) (p n) (ℓ n)
        (cvAx (t n)) (π n) (cF n) ∧
      SynOppSpec (mnBody Lb mainP) oppP (mnSrc (.v .io)) (mnSynPre (σ n)) (w n) (p n) (ℓ n)
        (cvAx (t n)) (π n) (cO n) ∧
      ∀ m < cvM (cvAx (t n)), π n m < cvM (cvAx (t n))
  cost : ∃ C : ℝ, ∀ᶠ n in atTop, ((cF n + cO n : ℕ) : ℝ) ≤ C * IntegerMultBounds.MathlibTM2.Cost.totConv n
  alpha : 96 ≤ prime + K

/-- **The parameter distribution**: `distP` meeting `MnDistSpec` with output file `E n`, a
`SrcBase` for three runs over the base files `V₀ n`, `σ₀ n` and a `SrcCrtBase`, the box,
CRT and result registers empty, the table word size `Wt`, the width conditions of the stages,
the lengths of the registers the first loaders clear, and the cost bound. -/
structure MnDist (K : ℕ) (Lb : LProc → MnPr (prime + K)) (w : ℕ → ℕ)
    (σ : ℕ → LReg SXReg → List (Fin (prime + K + 4))) where
  distP : MnPr (prime + K)
  Wt : ℕ → ℕ
  E : ℕ → SrcF 6 (prime + K)
  V₀ : ℕ → RsaV (RsaX 6) (prime + K)
  σ₀ : ℕ → RsbR ⊕ RsbX 6 → List (Fin (prime + K + 4))
  restA : ℕ → List (Fin (prime + K + 4))
  restB : ℕ → List (Fin (prime + K + 4))
  axsA : ℕ → List (Fin (prime + K + 4))
  axsB : ℕ → List (Fin (prime + K + 4))
  cost : ℕ → ℕ
  spec : ∀ᶠ n in atTop, ∀ mainP : MnPr (prime + K),
    MnDistSpec (mnBody Lb mainP) distP n (w n) (E n) (σ n) (cost n)
  base : ∀ᶠ n in atTop, ∀ hd0 : 0 < d n,
    SrcBase mnM (E n) n (w n) (Wt n) hd0 (V₀ n) (σ₀ n)
      (preRecsA n (Wt n) hd0 0 ++ (preRecsA n (Wt n) hd0 0 ++ restA n))
      (preRecsB n (Wt n) hd0 0 ++ (preRecsB n (Wt n) hd0 0 ++ restB n)) (axsA n) (axsB n)
  crt : ∀ᶠ n in atTop, SrcCrtBase (E n).c (E n).cb n (w n)
  ln : ∀ᶠ n in atTop, (E n).a .ln = []
  str : ∀ᶠ n in atTop, (E n).c .str = []
  sb : ∀ᶠ n in atTop, (E n).x .sb = []
  clrA : ∀ᶠ n in atTop, ∀ x ∈ preClrA crtHd, ((V₀ n).get x).length ≤ T n * w n
  clrB : ∀ᶠ n in atTop, ∀ r ∈ bandClrB crtHd, (σ₀ n r).length ≤ T n * w n
  widths : ∀ᶠ n in atTop, p n + Chirp.chirpGuard (d n) + 3 ≤ w n ∧ w n < Wt n ∧
    (∀ i : Fin (d n), alpha n ^ 2 * ((s n i + t n i) * (windowA (p n) (alpha n) + 1)) ^ 2 *
      2 ^ (13 * p n + 8) < 2 ^ Wt n) ∧
    (9 * p n + 2 ≤ w n ∧ ∀ i : Fin (d n), alpha n ^ 2 * ((s n i + t n i) *
      (8 * FastB0.fastWindow (p n) (alpha n) + 1)) ^ 2 * 2 ^ (65 * p n + 8) < 2 ^ Wt n) ∧
    (∀ k, s n k * t n k * t n k < 2 ^ Wt n) ∧
    (∀ k, 8 * (p n + Chirp.chirpGuard (d n)) + Nat.size (t n k) + 80 ≤ Wt n)
  ratio : ∃ cw cW : ℕ, ∀ᶠ n in atTop, w n ≤ cw * p n ∧ Wt n ≤ cW * p n
  costBound : ∃ C k : ℕ, ∀ᶠ n in atTop, cost n ≤ C * n + C * (b n + 1) ^ k

/-! ### Costs -/

section Costs

variable {K : ℕ} {Lb : LProc → MnPr (prime + K)} {w : ℕ → ℕ}
  {σ : ℕ → LReg SXReg → List (Fin (prime + K + 4))}

/-- The base file of `Ã` for the second run. -/
def mnV₁ (D : MnDist K Lb w σ) (n : ℕ) (hd0 : 0 < d n) : RsaV (RsaX 6) (prime + K) :=
  preCfgA (D.V₀ n) crtHd n (w n) (D.Wt n) hd0
    (preRecsA n (D.Wt n) hd0 0 ++ (preRecsA n (D.Wt n) hd0 0 ++ D.restA n)) (d n - 1)

/-- The base file of `Ã` for the third run. -/
def mnV₂ (D : MnDist K Lb w σ) (n : ℕ) (hd0 : 0 < d n) : RsaV (RsaX 6) (prime + K) :=
  preCfgA (mnV₁ D n hd0) crtHd n (w n) (D.Wt n) hd0 (preRecsA n (D.Wt n) hd0 0 ++ D.restA n)
    (d n - 1)

/-- The base file of `B̃₀` for the second run. -/
def mnσ₁ (D : MnDist K Lb w σ) (n : ℕ) (hd0 : 0 < d n) : RsbR ⊕ RsbX 6 → List (Fin (prime + K + 4)) :=
  bandCfgB (D.σ₀ n) crtHd n (w n) (D.Wt n) hd0
    (preRecsB n (D.Wt n) hd0 0 ++ (preRecsB n (D.Wt n) hd0 0 ++ D.restB n)) (d n - 1)

/-- The base file of `B̃₀` for the third run. -/
def mnσ₂ (D : MnDist K Lb w σ) (n : ℕ) (hd0 : 0 < d n) : RsbR ⊕ RsbX 6 → List (Fin (prime + K + 4)) :=
  bandCfgB (mnσ₁ D n hd0) crtHd n (w n) (D.Wt n) hd0 (preRecsB n (D.Wt n) hd0 0 ++ D.restB n)
    (d n - 1)

/-- The step bounds of the three source-transform runs. -/
def mnRuns (D : MnDist K Lb w σ) (Y : MnSyn K Lb w σ) (n : ℕ) : ℕ :=
  if hd0 : 0 < d n then
    srcDirectPCost mnM n (w n) (D.Wt n) (Y.cF n) (Y.cO n) hd0 (D.V₀ n) (D.σ₀ n)
        (preRecsA n (D.Wt n) hd0 0 ++ (preRecsA n (D.Wt n) hd0 0 ++ D.restA n))
        (preRecsB n (D.Wt n) hd0 0 ++ (preRecsB n (D.Wt n) hd0 0 ++ D.restB n)) +
      srcDirectPCost mnM n (w n) (D.Wt n) (Y.cF n) (Y.cO n) hd0 (mnV₁ D n hd0) (mnσ₁ D n hd0)
        (preRecsA n (D.Wt n) hd0 0 ++ D.restA n) (preRecsB n (D.Wt n) hd0 0 ++ D.restB n) +
      oppDirectPCost mnM n (w n) (D.Wt n) (Y.cF n) (Y.cO n) hd0 (mnV₂ D n hd0) (mnσ₂ D n hd0)
        (D.restA n) (D.restB n)
  else 0

/-- The step bounds of the glue between the runs: four transfers of a box (`x .sb` to the hold
register and to `cm .ys`, the hold register to `cm .xs`, `cm .out` to `x .sb`), two clears of a
box, the pointwise product. -/
def mnGlue (n w : ℕ) : ℕ :=
  4 * (4 * ((∏ i, t n i) * w) + 4) + 2 * (2 * ((∏ i, t n i) * w) + 2) +
    ((∏ i, t n i) * (cmulCost w + 6 * w + 2) + 8)

/-- The step bounds of the last stages: the coefficient stream onto the rounding stage, the
rounding stage, the words onto the output stage, the output stage. -/
def mnTail (n w : ℕ) : ℕ :=
  (4 * (S n * w) + 4) + roundStageCost (mnMw n w) w (b n) (p n) (mnWo n) (S n) +
    (4 * (S n * mnWo n) + 4) + carryOutCost (mnWo n) (b n) (S n)

/-- The sum of the stage bounds before the cleanup, at input length `n`. -/
def mnPreCost (D : MnDist K Lb w σ) (Y : MnSyn K Lb w σ) (n : ℕ) : ℕ :=
  (4 * n + 6) + (4 * n + 8) + pmCost n mnUs + D.cost n +
    2 * digitCost (b n) (p n) (w n) (S n) + mnRuns D Y n + mnGlue n (w n) + mnTail n (w n)

/-- **The time bound** of the fast multiplier at input length `n`, with push constant `c`: the
stages, the cleanup of at most `n + c · mnPreCost` symbols on `mnT` registers, the reset, and the
two steps of the compiled machine. -/
def mnTime (D : MnDist K Lb w σ) (Y : MnSyn K Lb w σ) (c n : ℕ) : ℕ :=
  mnPreCost D Y n + 2 * (n + c * mnPreCost D Y n) + 2 * mnT + 4

/-- The procedure table of the fast multiplier. -/
def mnTable (D : MnDist K Lb w σ) (Y : MnSyn K Lb w σ) : MnProc → MnPr (prime + K) :=
  mnBody Lb (mnFast D.distP Y.fwdP Y.oppP)

/-- The push constant of the fast multiplier. -/
def mnC (D : MnDist K Lb w σ) (Y : MnSyn K Lb w σ) : ℕ := mnPushC (mnTable D Y)

end Costs

end

end IntegerMultBounds.MathlibTM2.Fast.Main
