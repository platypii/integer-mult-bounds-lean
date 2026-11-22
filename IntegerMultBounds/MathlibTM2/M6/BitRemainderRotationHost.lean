module

public import IntegerMultBounds.MathlibTM2.M6.BitRemainderRotationLayout

/-! Physical entry and exit banks of an ordinary remainder label rotation. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine Stack Host
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open FlatCoordinateSchedule (bits)

private theorem tapes_ext {t a : ℕ} {v w : Tapes t a} (h : v.head = w.head) (f : v.tape = w.tape) : v = w := by
  cases v; cases w; congr

/-- The two data tapes share a position. The descriptor and loop banks flank them. -/
noncomputable def rotationBank (descriptors : Tapes 10 0) (controls : Tapes 2 0)
    (pos : ℤ) (src dst : ℤ → Fin (prime+4)) : Tapes 14 prime :=
  let enc := CountedLoopReuseAlphabet.encoding prime
  ((Alphabet.mapTapes enc descriptors).append
    (⟨fun _ => pos,![src,dst]⟩ : Tapes 2 prime)).append (Alphabet.mapTapes enc controls)

theorem ordinaryRotation_exec {P U : Type} {Q B N W : ℕ} [NeZero N]
    (body : P → Pr P 14 Q prime U) (fits : 235 ≤ Q) (hw : 0 < W) (src dst : Fin N)
    (row : Fin B → Fin W → ZMod 2) (x y : Fin ((B*N)*W) → ZMod 2)
    (hx : ∀ b j k, x (finProdFinEquiv (finProdFinEquiv (b,j),k)) = if j = src then row b k else 0)
    (hy : ∀ b j k, y (finProdFinEquiv (finProdFinEquiv (b,j),k)) = if j = dst then row b k else 0) :
    let a := (dst-src).val
    let tape := fun f : Fin ((B*N)*W) → ZMod 2 =>
      putWord (fun _ => blank) 0 (List.ofFn (fun j => SparseRoleCircuit.encode (a := prime) (f j)))
    let start := rotationBank (TranslationDescriptors.initial (bits W) (bits N) (bits a))
      (CountedLoopReuse.controls (fun _ => blank) (CountedCopyReuse.binary (bits B)) 0 1)
      0 (tape x) (fun _ => blank)
    let finish := rotationBank (TranslationDescriptors.bank (fun _ => []) (bits W) (bits N) (bits a)
      (fun _ => blank) 0) (CountedLoopReuse.controls CountedCopyReuse.empty (CountedCopyReuse.binary (bits B)) 1 1)
      (B*(N*W) : ℕ) (tape x) (tape y)
    let machine := liftQ (Alphabet.program (CountedLoopReuseAlphabet.encoding prime) TranslationStream.program) fits
    ∀ u S, RepT start S.L S.R → ∃ v D t, Exec body (foreign machine) (mk u S) t (mk v D) ∧
      t ≤ (461*(B*(N*W))+25)*19+6 ∧ v.user = u.user ∧ RepT finish D.L D.R ∧
      D.inp = S.inp ∧ D.out = S.out ∧ ∀ i, (D.L i).length+(D.R i).length ≤
        (S.L i).length+(S.R i).length+2*(461*(B*(N*W))+25) := by
  intro a tape start finish machine u S live
  let enc := CountedLoopReuseAlphabet.encoding prime
  let zeros := List.replicate W (SparseRoleCircuit.encode (a := 0) 0)
  let payload := fun (g : Fin N) b (j : ℕ) => if j = g.val then rotationRecord row b else zeros
  have mapped (g : Fin N) (f : Fin ((B*N)*W) → ZMod 2)
      (cell : ∀ b j k, f (finProdFinEquiv (finProdFinEquiv (b,j),k)) = if j = g then row b k else 0) :
      (fun z => enc.encode (putWord (fun _ => blank) 0 (TranslationStream.fibers N B (payload g)).flatten z))
        = tape f := by
    exact (RowPaddingConstructedAlphabet.map_putWord _ _ _).trans
      (congrArg (putWord (fun _ => blank) 0) (rotationStream_word g row f cell))
  have entry : Alphabet.mapTapes enc (TranslationStream.input N B (fun _ => blank) (fun _ => blank)
      0 0 (bits W) (bits N) (bits a) (bits B) (payload src)) = start := by
    apply tapes_ext
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> first | rfl | exact mapped src x hx
  obtain ⟨v,D,t,run,time,user,rep,inp,out,stock,written⟩ := labelRotationStream_exec body fits B src dst
    hw (rotationRecord row) zeros (rotationRecord_length row) (List.length_replicate) (fun _ => blank)
    (fun _ => blank) 0 0 u S (entry ▸ live)
  refine ⟨v,D,t,run,time,user,?_,inp.symm,out.symm,stock⟩
  apply Eq.mp (congrArg (fun bank => RepT bank D.L D.R) ?_) rep
  apply tapes_ext
  · funext i
    fin_cases i <;> first | rfl | exact zero_add _
  · funext i
    fin_cases i <;> first | rfl | exact mapped src x hx | exact (congrArg (fun f : ℤ → Fin 4 => fun z => enc.encode (f z)) written).trans (mapped dst y hy)

end IntegerMultBounds.MathlibTM2.M6.BitNode
