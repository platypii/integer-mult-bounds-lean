import IntegerMultBounds.Machine.RecursiveShiftRoleBank
import IntegerMultBounds.Machine.SparseRoleCircuit

/-! Actual XOR on the same permanent role/scratch/six-header bank as the
heterogeneous shifts and scalings. A reusable XOR clock and the canonical stream
length descriptor occupy the first two auxiliary tapes. Their construction is
explicitly outside this adapter; both are preserved exactly by every gate. -/
namespace IntegerMultBounds.Machine.RecursiveXorRoleBank
noncomputable section
open Networks
open Shared50ModularControl (prime)
open RecursiveShiftRoleBank (common)
variable {t u n : ℕ}

def controls (bs : List Bool) : Tapes 2 prime :=
  CountedLoopReuseAlphabet.controls CountedLoopReuseAlphabet.empty (CountedLoopReuseAlphabet.binary bs) 1 1

def commonPorts (g : PointwiseRoleGate.Gate t) : Fin 4 → Fin (t+(7+(2+u))) :=
  ![Fin.castAdd (7+(2+u)) g.src,Fin.castAdd (7+(2+u)) g.dst,
    Fin.natAdd t (Fin.natAdd 7 (Fin.castAdd u 0)),Fin.natAdd t (Fin.natAdd 7 (Fin.castAdd u 1))]

theorem commonPorts_injective (g : PointwiseRoleGate.Gate t) : Function.Injective (commonPorts (u := u) g) := by
  intro i j h
  have hv := congrArg Fin.val h
  have hne : g.src.val ≠ g.dst.val := fun h => g.distinct (Fin.ext h)
  have hs := g.src.isLt
  have hd := g.dst.isLt
  fin_cases i <;> fin_cases j <;> simp_all [commonPorts,Fin.ext_iff] <;> omega

def word (xs : Fin n → Fin (prime+4)) : ℤ → Fin (prime+4) :=
  putWord (fun _ => blank) 0 (List.ofFn xs)

def updated (roles : Tapes t prime) (g : PointwiseRoleGate.Gate t) (xs : Fin n → Fin (prime+4)) :=
  SharedPlacementAlphabet.setTape roles g.dst (word xs) 0

def program (g : PointwiseRoleGate.Gate t) :=
  Placement.placed (PointwiseBinaryNormalized.program (PointwiseBinary.xorSymbol (a := prime)))
    (CleanSubbank.placement (id : Fin 4 → Fin 4) (commonPorts (u := u) g) (commonPorts_injective g))

private theorem common_payload (g : PointwiseRoleGate.Gate t) (roles : Tapes t prime)
    (hs : Fin 6 → List Bool) (bs : List Bool) (aux : Tapes u prime) (x y : Fin n → Fin (prime+4))
    (hhx : roles.head g.src = 0) (hhy : roles.head g.dst = 0)
    (htx : roles.tape g.src = word x) (hty : roles.tape g.dst = word y) :
    SharedBank.payload (common roles hs ((controls bs).append aux)) (commonPorts g) =
      PointwiseBinaryNormalized.bank
        (PointwiseBinaryNormalized.pair (fun _ => blank) (fun _ => blank) 0 0 x y) bs := by
  apply congrArg₂ Tapes.mk
  · funext i
    fin_cases i <;> simp [common,commonPorts,Tapes.append,Fin.addCases,hhx,hhy,
      PointwiseBinaryNormalized.pair,
      controls,CountedLoopReuseAlphabet.controls,StackPop.bank] <;> omega
  · funext i
    fin_cases i <;> simp [common,commonPorts,Tapes.append,Fin.addCases,htx,hty,word,
      PointwiseBinaryNormalized.pair,
      controls,CountedLoopReuseAlphabet.controls,StackPop.bank] <;> omega

private theorem common_frame (g : PointwiseRoleGate.Gate t) (roles : Tapes t prime)
    (hs : Fin 6 → List Bool) (bs : List Bool) (aux : Tapes u prime) (x : Fin n → Fin (prime+4)) :
    SharedBank.strip (common roles hs ((controls bs).append aux)) (commonPorts g) =
      SharedBank.strip (common (updated roles g x) hs ((controls bs).append aux)) (commonPorts g) := by
  have selected : ∃ j, commonPorts (u := u) g j = Fin.castAdd (7+(2+u)) g.dst := ⟨1,rfl⟩
  apply congrArg₂ Tapes.mk
  · funext i
    induction i using Fin.addCases with
    | left i =>
      by_cases hi : i = g.dst
      · subst i; simp [selected]
      · simp only [common,Tapes.append,Fin.addCases_left,updated,SharedPlacementAlphabet.setTape,
          Function.update_of_ne hi]
    | right i => simp only [common,Tapes.append,Fin.addCases_right]
  · funext i
    induction i using Fin.addCases with
    | left i =>
      by_cases hi : i = g.dst
      · subst i; simp [selected]
      · simp only [common,Tapes.append,Fin.addCases_left,updated,SharedPlacementAlphabet.setTape,
          Function.update_of_ne hi]
    | right i => simp only [common,Tapes.append,Fin.addCases_right]

/-- Fixed physical XOR on the original source/destination roles. Headers,
clock, stream-length descriptor, scratch, spectators and auxiliary tapes survive. -/
theorem realizes (g : PointwiseRoleGate.Gate t) (roles : Tapes t prime)
    (hs : Fin 6 → List Bool) (bs : List Bool) (aux : Tapes u prime) (x y : Fin n → Fin (prime+4))
    (hhx : roles.head g.src = 0) (hhy : roles.head g.dst = 0)
    (htx : roles.tape g.src = word x) (hty : roles.tape g.dst = word y)
    (hn : Counter.value bs = n) :
    HoareTime (program (u := u) g)
      (fun w => w = CleanSubbank.bank (common roles hs ((controls bs).append aux)))
      (fun w => w = CleanSubbank.bank
        (common (updated roles g (fun i => PointwiseBinary.xorSymbol (x i) (y i))) hs ((controls bs).append aux)))
      (14*n+14*bs.length+33) := by
  apply CleanSubbank.realizes _ id (commonPorts g) Function.injective_id (commonPorts_injective g)
    _ _ (PointwiseBinaryNormalized.bank (PointwiseBinaryNormalized.pair (fun _ => blank) (fun _ => blank) 0 0 x y) bs)
    (PointwiseBinaryNormalized.bank (PointwiseBinaryNormalized.pair (fun _ => blank) (fun _ => blank) 0 0 x
      (fun i => PointwiseBinary.xorSymbol (x i) (y i))) bs) _
  · exact (SharedBankFrames.payload_identity _).trans (common_payload g roles hs bs aux x y hhx hhy htx hty).symm
  · exact (SharedBankFrames.payload_identity _).trans (common_payload g _ hs bs aux x _
      (by simpa [updated,SharedPlacementAlphabet.setTape,Function.update_of_ne g.distinct] using hhx)
      (by simp [updated,SharedPlacementAlphabet.setTape])
      (by simpa [updated,SharedPlacementAlphabet.setTape,Function.update_of_ne g.distinct] using htx)
      (by simp [updated,SharedPlacementAlphabet.setTape])).symm
  · exact SharedBankFrames.strip_identity _
  · exact SharedBankFrames.strip_identity _
  · exact common_frame g roles hs bs aux _
  · exact PointwiseBinaryNormalized.array_hoare PointwiseBinary.xorSymbol _ _ 0 0 x y bs hn

/-- On encoded binary field streams, the physical operation is the literal
one-source gate `destination ← destination + source`. -/
theorem realizes_bits (g : PointwiseRoleGate.Gate t) (roles : Tapes t prime)
    (hs : Fin 6 → List Bool) (bs : List Bool) (aux : Tapes u prime) (x y : Fin n → ZMod 2)
    (hhx : roles.head g.src = 0) (hhy : roles.head g.dst = 0)
    (htx : roles.tape g.src = word (fun i => SparseRoleCircuit.encode (x i)))
    (hty : roles.tape g.dst = word (fun i => SparseRoleCircuit.encode (y i)))
    (hn : Counter.value bs = n) :
    HoareTime (program (u := u) g)
      (fun w => w = CleanSubbank.bank (common roles hs ((controls bs).append aux)))
      (fun w => w = CleanSubbank.bank
        (common (updated roles g (fun i => SparseRoleCircuit.encode (y i+x i))) hs ((controls bs).append aux)))
      (14*n+14*bs.length+33) := by
  simpa only [SparseRoleCircuit.encode_add] using realizes g roles hs bs aux
    (fun i => SparseRoleCircuit.encode (x i)) (fun i => SparseRoleCircuit.encode (y i)) hhx hhy htx hty hn

end
end IntegerMultBounds.Machine.RecursiveXorRoleBank
