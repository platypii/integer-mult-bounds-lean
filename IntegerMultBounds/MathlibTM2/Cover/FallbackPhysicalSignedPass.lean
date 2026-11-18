module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackSignedPass
public import IntegerMultBounds.MathlibTM2.Cover.FallbackPhysicalScanData

/-! Run the signed pass with the physical residual archive and its residue table. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host LabelTraversal
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
variable [M8.Machine.Net] {T K Q d r w W : ℕ} {P U : Type}
local notation "N" => rowSwapBlock.tapes+35

open Record RecursiveInterchangeLayout
local notation "M" => prime^(w+1)
local instance : NeZero M := ⟨pow_ne_zero _ Networks.Shared50ModularControl.prime_prime.ne_zero⟩

theorem physicalSignedResidualPass (regs : Fin 6 ↪ Fin T) (anchor : Fin (size d+T) ↪ Fin K)
    (ports : Fin (N+2) ↪ Fin K) (ext : Fin 6 ↪ Fin K) (off : ∀ i k, ports i ≠ ext k)
    (banks : ∀ i k, anchor i ≠ ports k) (external : ∀ i k, k ≠ 2 → anchor i ≠ ext k)
    (shared : anchor (port d regs 1) = ext 2)
    (capacity : (anchorProgram d true).1+(anchorProgram d false).1+1 ≤ Q)
    (e : (Fin r ⊕ Fin r) ≃ Fin (d+1)) (proj : Matrix (Fin r) (Fin r) ℚ)
    (idempotent : proj*proj = proj) (admissible : IntegerMultBounds.Swap.Modular.Admissible prime proj)
    (α α' : Fin r → ZMod M) (inverse : ∀ i, α i * α' i = 1)
    (body : P → Pr P K Q prime U) (rs : List (Pair (size d+T))) (hk : rs.length = r*r)
    (parents saved : Fin (size d+T)) (layout : (parents :: saved :: (slots rs ++ [port d regs 4])).Nodup)
    (cap : columnCapacity ≤ Q) (cs : List (Pair K)) (sizeC : cs.length = r*r) (parentsC savedC : Fin K)
    (maskRegs : (parentsC :: savedC :: (slots cs ++ [ext 0])).Nodup)
    (pivotRegs : (parentsC :: savedC :: (slots cs ++ [ports (Fin.last N).castSucc])).Nodup)
    (separate : ∀ k ∈ parentsC :: savedC :: slots cs, ∀ i, anchor i ≠ k) :
    ∃ prog, ∀ (v : Descriptor) (B : ℕ) (base : ScanData r d w W) (inputs : ℕ → Record.Array d 1 (w+1) W)
      (u : HS K Q prime U) (S : Stacks K prime),
      let a := base.physical e proj α α'
      v.beforeH = B*prime^(r*((w+1)*r)) →
      a.records = LabelMask.records v → 0 < W →
      let D := embStk anchor S
      Ready d 1 (w+1) W D → ready (prime^w) D.R rs → D.R saved = [] →
      (D.R parents).length = v.beforeRows*v.rows*B →
      (D.R (port d regs 0)).length = ActualAffineScaling.modulus (w+1)^((d+1)*1)*W →
      a.signed = (List.range a.records).map inputs →
      (∀ i ∈ ([2,3,4,5] : List (Fin 6)), D.R (port d regs i) = []) →
      let archive := ports (archivePorts 0 (columnBank 34))
      S.R archive = (List.range a.records).flatMap (fun j =>
        if LabelStock.live r (w+1) 1 j then matrixWords prime a.H
          (projectorResidual e (IntegerMultBounds.Swap.Modular.reduce M proj) α α' (physicalLabel r (w+1) j))
        else matrixWords prime a.H (1 : Matrix (Fin (d+1)) (Fin (d+1)) (ZMod M))) →
      ScanReady a ports ext 0 (preparedPivots a (ports (Fin.last N).castSucc)
        {S with R := Function.update S.R archive (a.matrices 0)}) →
      M < 2^a.H → W < 2^a.J → a.outputTail = [] → S.R (ext 0) = [] →
      ready (prime^w) S.R cs → S.R savedC = [] → (S.R parentsC).length = v.beforeRows*v.rows*B →
      (∀ j < a.records, Record.scalarArray (inputs j) = SparseRoleCircuit.encode ∘ a.input j) →
      (∀ j < a.records, LabelStock.live r (w+1) 1 j = false →
      ∃ symbol, Record.scalarArray (inputs j) = fun _ => symbol) →
      let ins := signedInputs a.table (w+1) a.records inputs
    let output := (List.range a.records).flatMap (outputRecord (LabelStock.live r (w+1) 1) a.matrix a.input)
    ∃ z F n, z.user = u.user ∧ F.R (ext 2) = output ++ a.inputTail ∧ F.R (ext 5) = [] ∧
      F.R (ext 0) = [] ∧ F.R (ports (Fin.last N).castSucc) = a.pivotTail ∧
      F.R (ports (archivePorts 0 (columnBank 34))) = a.matrixTail ∧
      n ≤ (1+((v.beforeRows*v.rows*B)*(time (prime^w) (r*r) 1+5)+4 +
          ((ins.map (fun x => cost d T 1 (w+1) W x.1 + 2)).sum + 2) +
          (2*(a.records*(ActualAffineScaling.modulus (w+1)^((d+1)*1)*W))+2))) + (2*((v.beforeRows*v.rows*B)*(time (prime^w) (r*r) 1+5)+4) + (1+(((List.range a.records).map fun j => a.recordTime U j + 4).sum + 2 + (2*(a.records*(M^(d+1)*W))+2)))) ∧
      Exec body prog (mk u S) n (mk z F) := by
  let φ := LabelRing.res prime (w+1) (by omega)
  let table := projectorResidual e (IntegerMultBounds.Swap.Modular.reduce prime proj) (φ ∘ α) (φ ∘ α')
  obtain ⟨prog,run⟩ := signedResidualPass (w := w) (W := W) regs anchor ports ext off banks external shared
    capacity table body rs hk parents saved layout cap cs sizeC parentsC savedC maskRegs pivotRegs separate
  refine ⟨prog,?_⟩
  intro v B base inputs u S a shape records hW D neutral radix free count width unsigned clean archive generated start hm hw
    fresh empty radixC freeC countC encoded padding
  have archiveEq : S.R archive = a.matrices 0 := generated.trans (base.physical_archive e proj α α').symm
  rw [← archiveEq,Function.update_eq_self] at start
  exact run v B a inputs u S shape records hW neutral radix free count width unsigned clean start
    rfl hm hw fresh empty radixC freeC countC encoded
    (fun j _ live => base.physical_live e proj idempotent admissible α α' inverse j live) padding

end IntegerMultBounds.MathlibTM2.Cover.Fallback
