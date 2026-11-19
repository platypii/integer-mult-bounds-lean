module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackPhysicalSignedPass
public import IntegerMultBounds.MathlibTM2.Cover.FallbackConjugationQueue

/-! Compose residual queue generation and the signed pass on their shared archive register. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host LabelTraversal
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
variable [M8.Machine.Net] {T K Q d r w W : ℕ} {P U : Type}
local notation "N" => rowSwapBlock.tapes+35

open Record RecursiveInterchangeLayout
local notation "M" => prime^(w+1)
local instance : NeZero M := ⟨pow_ne_zero _ Networks.Shared50ModularControl.prime_prime.ne_zero⟩

theorem generatedSignedResidualPass (regs : Fin 6 ↪ Fin T) (anchor : Fin (size d+T) ↪ Fin K)
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
    ∃ pass, ∀ (generate : Pr P K Q prime U) (mask directory : Fin K) (tail : List (Fin (prime+4)))
      (setupCost : ℕ), ∀ (v : Descriptor) (B : ℕ) (base : ScanData r d w W) (inputs : ℕ → Record.Array d 1 (w+1) W)
      (u : HS K Q prime U) (S : Stacks K prime),
      let a := base.physical e proj α α'
      let archive := ports (archivePorts 0 (columnBank 34))
      let G := queueResult S mask directory archive tail (a.matrices 0)
      (∃ y t, y.user = u.user ∧ t ≤ setupCost ∧ Exec body generate (mk u S) t (mk y G)) →
      v.beforeH = B*prime^(r*((w+1)*r)) →
      a.records = LabelMask.records v → 0 < W →
      let D := embStk anchor G
      Ready d 1 (w+1) W D → ready (prime^w) D.R rs → D.R saved = [] →
      (D.R parents).length = v.beforeRows*v.rows*B →
      (D.R (port d regs 0)).length = ActualAffineScaling.modulus (w+1)^((d+1)*1)*W →
      a.signed = (List.range a.records).map inputs →
      (∀ i ∈ ([2,3,4,5] : List (Fin 6)), D.R (port d regs i) = []) →
      ScanReady a ports ext 0 (preparedPivots a (ports (Fin.last N).castSucc)
        G) →
      M < 2^a.H → W < 2^a.J → a.outputTail = [] → G.R (ext 0) = [] →
      ready (prime^w) G.R cs → G.R savedC = [] → (G.R parentsC).length = v.beforeRows*v.rows*B →
      (∀ j < a.records, Record.scalarArray (inputs j) = SparseRoleCircuit.encode ∘ a.input j) →
      (∀ j < a.records, LabelStock.live r (w+1) 1 j = false →
      ∃ symbol, Record.scalarArray (inputs j) = fun _ => symbol) →
      let ins := signedInputs a.table (w+1) a.records inputs
    let output := (List.range a.records).flatMap (outputRecord (LabelStock.live r (w+1) 1) a.matrix a.input)
    ∃ z F n, z.user = u.user ∧ F.R (ext 2) = output ++ a.inputTail ∧ F.R (ext 5) = [] ∧
      F.R (ext 0) = [] ∧ F.R (ports (Fin.last N).castSucc) = a.pivotTail ∧
      F.R (ports (archivePorts 0 (columnBank 34))) = a.matrixTail ∧
      n ≤ setupCost + ((1+((v.beforeRows*v.rows*B)*(time (prime^w) (r*r) 1+5)+4 +
          ((ins.map (fun x => cost d T 1 (w+1) W x.1 + 2)).sum + 2) +
          (2*(a.records*(ActualAffineScaling.modulus (w+1)^((d+1)*1)*W))+2))) + (2*((v.beforeRows*v.rows*B)*(time (prime^w) (r*r) 1+5)+4) + (1+(((List.range a.records).map fun j => a.recordTime U j + 4).sum + 2 + (2*(a.records*(M^(d+1)*W))+2))))) ∧
      Exec body (.seq generate pass) (mk u S) n (mk z F) := by
  obtain ⟨pass,run⟩ := physicalSignedResidualPass (w := w) (W := W) regs anchor ports ext off banks external shared
    capacity e proj idempotent admissible α α' inverse body rs hk parents saved layout cap cs sizeC
    parentsC savedC maskRegs pivotRegs separate
  refine ⟨pass,?_⟩
  intro generate mask directory tail setupCost v B base inputs u S a archive G made shape records hW D
    neutral radix free count width unsigned clean start hm hw fresh empty radixC freeC countC encoded padding
  obtain ⟨y,t,hy,ht,generateRun⟩ := made
  have installed : G.R archive = a.matrices 0 := Function.update_self ..
  have prep : Function.update G.R archive (a.matrices 0) = G.R := by rw [← installed,Function.update_eq_self]
  obtain ⟨z,E,n,hz,queue,acc,maskDone,pivots,archiveDone,hn,exec⟩ :=
    run v B base inputs y G shape records hW neutral radix free count width unsigned clean
      (installed.trans (base.physical_archive e proj α α')) (by change ScanReady a ports ext 0 (preparedPivots a _ {G with R := Function.update G.R archive (a.matrices 0)}); rw [prep]; exact start)
      hm hw fresh empty radixC freeC countC encoded padding
  exact ⟨z,E,_,hz.trans hy,queue,acc,maskDone,pivots,archiveDone,Nat.add_le_add ht hn,Exec.seq generateRun exec⟩

end IntegerMultBounds.MathlibTM2.Cover.Fallback
