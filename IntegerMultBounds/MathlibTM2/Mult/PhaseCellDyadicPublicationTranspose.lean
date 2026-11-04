module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDyadicRowTranspose
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPaddedArchiveTileData
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCoefficientPaddingData

/-! The fixed-bank publication transpose accepts arbitrary computed job counts
with whole-job prefix padding. Every real row survives at its shifted index. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Layer
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
namespace PackedTranspose
noncomputable section
open FixedStreamedBank
variable {Q K N : ℕ} {P U : Type}

theorem padded_rows_exec_within (body : P → Pr P tapeCount Q (prime+K) U)
    (hstates : FixedStreamedBank.stateCount ≤ Q) (a b L w V : ℕ)
    (hpacket : 0 < L*w) (hbits : a+b < V) (hfit : (L*w)*2^(a+b) < 2^V) (hA : 4 ≤ prime+K)
    (hcapacity : N ≤ 2^a)
    (rows : Fin N → Fin (2^b) → List GaussianInt)
    (hlen : ∀ i j, (rows i j).length = L) (depth : ℕ)
    (v : HS tapeCount Q (prime+K) U) (S : Stacks tapeCount (prime+K))
    (ha : S.R (base (callerGenerator 97)) = binSyms V a)
    (hb : S.R (base (callerGenerator 98)) = binSyms V b)
    (hseed : S.R (base (callerGenerator 102)) = binSyms V (L*w))
    (hz : S.R (base (callerGenerator 106)) = [])
    (hwidth : (S.R (base (callerGenerator 115))).length = V)
    (hblank : ∀ r, S.R (base (callerGenerator (originReg r))) = [])
    (hstageCount : S.R (base (callerGenerator 116)) = []) (hL : ∀ i, S.L i = [])
    (hfresh : ∀ i, i ≠ workerReg (reg pay) → i ≠ FixedStreamedBank.control 7 → S.R (base (callerWorker i)) = [])
    (hsrc : S.R (extra 1) = tilePrefixPad (2^a*(2^b*(L*w))) (pairSym (prime+K) false false)
      ((List.ofFn fun i => (List.ofFn fun j => cstream (prime+K) w (rows i j)).flatten).flatten))
    (hcount : S.R (extra 4) = [])
    (hcodec : ∀ i ∈ [planeReg false,planeReg true,extra 2,extra 3,extra 5,extra 6], S.R i = []) :
    ∃ paddedRows : Fin (2^a) → Fin (2^b) → List GaussianInt,
      (∀ i j, (paddedRows i j).length = L) ∧
      (∀ i j, paddedRows (paddedCoreIndex hcapacity i) j = rows i j) ∧
      ∃ v' n, v'.user = v.user ∧ n ≤ 26*(2^a*(2^b*(L*w)))+24+2*restoringTimeCost hstates a b (L*w) V ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
        (40*(2^a*(2^b*(L*w)))+38+restoringStockAllowance hstates a b (L*w) V)) depth
        (program hstates) (mk v S) n
        (mk v' {S with L := (fun _ => []), R := (Function.update S.R (extra 1)
          ((List.ofFn fun j => cstream (prime+K) w (List.ofFn fun i => paddedRows i j).flatten).flatten))}) := by
  let f := fun i j (k : Fin L) => (rows i j)[k.val]'(by rw [hlen]; exact k.isLt)
  obtain ⟨g,hpad,hinput,_⟩ := coefficientPadding_view (prime+K) w (2^a) f hcapacity
  let paddedRows := fun i j => List.ofFn (g i j)
  have hp : ∀ i j, (paddedRows i j).length = L := by intro i j; simp [paddedRows]
  have hg : (fun i j (k : Fin L) => (paddedRows i j)[k.val]'(by rw [hp]; exact k.isLt)) = g := by
    funext i j k
    simp only [paddedRows,List.getElem_ofFn]
  have hin := archiveRows_cstream (A := prime+K) w paddedRows hp
  rw [hg] at hin
  rw [archiveRows_cstream w rows hlen] at hinput
  have he := rows_exec_within body hstates a b L w V hpacket hbits hfit hA paddedRows hp depth v S
    ha hb hseed hz hwidth hblank hstageCount hL hfresh (hsrc.trans (hinput.symm.trans hin)) hcount hcodec
  refine ⟨paddedRows,hp,?_,he⟩
  intro i j
  have hh : g (paddedCoreIndex hcapacity i) j = f i j := by
    funext k
    exact paddedCore_entry hcapacity 0 f g hpad i j k
  change List.ofFn (g (paddedCoreIndex hcapacity i) j) = rows i j
  rw [hh]
  exact archiveRow_ofFn rows hlen i j

end
end PackedTranspose
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
