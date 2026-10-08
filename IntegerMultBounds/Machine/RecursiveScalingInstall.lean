import IntegerMultBounds.Machine.FlatAffineScalingInputLayout
import IntegerMultBounds.Machine.RecursiveInterchangeScaling
import IntegerMultBounds.Machine.BinaryDescriptorInstallList

/-! Physical installation of all affine-scaling dimension descriptors from one
preserved sixteen-tape dimension bank. The copy schedule depends only on coefficient. -/
namespace IntegerMultBounds.Machine.RecursiveScalingInstall
open FlatAffineScalingInputLayout (Kind kinds bank word)
open BinaryDescriptorInstallList
variable (target : RecursiveInterchangeScaling.Target)

abbrev LocalTapes (a d : ℕ) := SignedScalingDimensionsStream.TapeCount a d
abbrev TapeCount (a d : ℕ) := 16+LocalTapes a d

def isDescriptor : Kind → Bool
  | .block | .count | .prefix => true
  | _ => false

def sourceSlot : Kind → Fin 16
  | .block => match target with | .h => 14 | .d => 8
  | .prefix => match target with | .h => 11 | .d => 15
  | _ => 9

def instruction (a d : ℕ) (i : Fin (LocalTapes a d)) : Instruction (TapeCount a d) where
  source := Fin.castAdd _ (sourceSlot target (kinds a d i))
  dest := Fin.natAdd 16 i
  distinct := by intro h; have := congrArg Fin.val h; have := (sourceSlot target (kinds a d i)).isLt; simp only [Fin.val_castAdd,Fin.val_natAdd] at *; omega

def destinations (a d : ℕ) : List (Fin (LocalTapes a d)) :=
  (List.finRange _).filter (fun i => isDescriptor (kinds a d i))

def instructions (a d : ℕ) : List (Instruction (TapeCount a d)) :=
  (destinations a d).map (instruction target a d)

theorem mem_destinations (a d : ℕ) (i : Fin (LocalTapes a d)) :
    i ∈ destinations a d ↔ isDescriptor (kinds a d i) = true := by simp [destinations]

theorem disjoint (a d : ℕ) : Disjoint (instructions target a d) := by
  rintro x hx y hy he
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp hx
  obtain ⟨j,_,rfl⟩ := List.mem_map.mp hy
  have hv := congrArg Fin.val he
  have hj := (sourceSlot target (kinds a d j)).isLt
  simp only [instruction,Fin.val_castAdd,Fin.val_natAdd] at hv
  omega

theorem unique (a d : ℕ) : Unique (instructions target a d) := by
  unfold BinaryDescriptorInstallList.Unique instructions
  rw [List.map_map]
  apply List.Nodup.map
  · intro i j h
    apply Fin.ext
    have hv := congrArg Fin.val h
    change 16+i.val = 16+j.val at hv
    omega
  · exact (List.nodup_finRange _).filter _

def sourceWords (bs qs ns : List Bool) : Fin 16 → List Bool :=
  fun i => if i = sourceSlot target .block then bs else if i = sourceSlot target .prefix then ns else qs

private theorem sourceWords_kind (bs qs ns : List Bool) (k : Kind) :
    sourceWords target bs qs ns (sourceSlot target k) =
      (match k with | .block => bs | .prefix => ns | _ => qs) := by
  cases target <;> cases k <;> rfl

def liftedBank (radix a d : ℕ) (source : ℤ → Fin 4) (bs qs ns : List Bool) : Tapes (LocalTapes a d) radix :=
  Alphabet.mapTapes (RadixToBinary.binaryEncoding (q := radix)) (bank a d source bs qs ns)

@[simp] theorem lifted_head (radix a d : ℕ) (source : ℤ → Fin 4) (bs qs ns : List Bool)
    (i : Fin (LocalTapes a d)) : (liftedBank radix a d source bs qs ns).head i = 0 := rfl

private theorem encode_raw (radix : ℕ) (xs : List Bool) :
    (fun z => (RadixToBinary.binaryEncoding (q := radix)).encode (BinaryDescriptorInstallRaw.rawWord 0 xs z)) =
      BinaryDescriptorInstallRaw.rawWord radix xs := by
  funext z
  by_cases hz : z = 0
  · simp [hz,BinaryDescriptorInstallRaw.rawWord,RadixToBinary.binaryEncoding,blank]
  · simp [hz,BinaryDescriptorInstallRaw.rawWord,RadixZeroFill.encodedBinary,RadixToBinary.binaryEncoding]

private theorem raw_nil (radix : ℕ) : BinaryDescriptorInstallRaw.rawWord radix [] = fun _ => blank := by
  funext z
  by_cases hz : z = 0 <;>
    simp [BinaryDescriptorInstallRaw.rawWord,RadixZeroFill.encodedBinary,RadixToBinary.binaryEncoding,
      CountedCopyReuse.binary,CountedCopyReuse.empty,putBits,hz,blank]

private theorem lifted_descriptor (radix a d : ℕ) (source : ℤ → Fin 4) (bs qs ns : List Bool)
    (i : Fin (LocalTapes a d)) (hi : isDescriptor (kinds a d i) = true) :
    (liftedBank radix a d source bs qs ns).tape i =
      BinaryDescriptorInstallRaw.rawWord radix (sourceWords target bs qs ns (sourceSlot target (kinds a d i))) := by
  unfold liftedBank Alphabet.mapTapes bank
  dsimp only
  cases hk : kinds a d i <;> simp only [hk,isDescriptor,Bool.false_eq_true] at hi
  all_goals first | contradiction | cases target <;> simpa [hk,word,sourceSlot,sourceWords] using encode_raw radix _

private theorem lifted_frame (radix a d : ℕ) (source : ℤ → Fin 4) (bs qs ns : List Bool)
    (i : Fin (LocalTapes a d)) (hi : isDescriptor (kinds a d i) ≠ true) :
    (liftedBank radix a d source [] [] []).tape i = (liftedBank radix a d source bs qs ns).tape i := by
  unfold liftedBank Alphabet.mapTapes bank
  dsimp only
  cases hk : kinds a d i <;> simp only [hk,isDescriptor] at hi
  all_goals first | contradiction | rfl

noncomputable def program (radix a d : ℕ) := BinaryDescriptorInstallList.program radix (by unfold TapeCount; omega : 0 < TapeCount a d) (instructions target a d)

def allWords (a d : ℕ) (bs qs ns : List Bool) : Fin (TapeCount a d) → List Bool :=
  Fin.addCases (sourceWords target bs qs ns) (fun _ => [])

private theorem result_exact (radix a d : ℕ) (v : Tapes 16 radix) (source : ℤ → Fin 4)
    (bs qs ns : List Bool) :
    result (instructions target a d) (allWords target a d bs qs ns) (v.append (liftedBank radix a d source [] [] [])) =
      v.append (liftedBank radix a d source bs qs ns) := by
  have point (i : Fin (TapeCount a d)) :
      (result (instructions target a d) (allWords target a d bs qs ns) (v.append (liftedBank radix a d source [] [] []))).head i =
        (v.append (liftedBank radix a d source bs qs ns)).head i ∧
      (result (instructions target a d) (allWords target a d bs qs ns) (v.append (liftedBank radix a d source [] [] []))).tape i =
        (v.append (liftedBank radix a d source bs qs ns)).tape i := by
    induction i using Fin.addCases with
    | left i =>
      have hf := result_frame (instructions target a d) (allWords target a d bs qs ns)
        (v.append (liftedBank radix a d source [] [] [])) (Fin.castAdd _ i) (by
          rintro op hop he
          obtain ⟨j,_,rfl⟩ := List.mem_map.mp hop
          have hv := congrArg Fin.val he
          have hi := i.isLt
          simp only [instruction,Fin.val_natAdd,Fin.val_castAdd] at hv
          omega)
      simpa only [Tapes.append,Fin.addCases_left] using hf
    | right i =>
      by_cases hi : isDescriptor (kinds a d i) = true
      · have hm : instruction target a d i ∈ instructions target a d :=
          List.mem_map.mpr ⟨i,(mem_destinations a d i).mpr hi,rfl⟩
        have hf := result_dest (instructions target a d) (unique target a d) (allWords target a d bs qs ns)
          (v.append (liftedBank radix a d source [] [] [])) (instruction target a d i) hm
        simp only [instruction,allWords,Fin.addCases_left] at hf
        simpa only [Tapes.append,Fin.addCases_right,lifted_head,lifted_descriptor target radix a d source bs qs ns i hi]
          using hf
      · have hf := result_frame (instructions target a d) (allWords target a d bs qs ns)
          (v.append (liftedBank radix a d source [] [] [])) (Fin.natAdd 16 i) (by
            rintro op hop he
            obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hop
            have hij : i = j := by
              apply Fin.ext
              have hv := congrArg Fin.val he
              change 16+i.val = 16+j.val at hv
              omega
            exact hi (hij ▸ (mem_destinations a d j).mp hj))
        simpa only [Tapes.append,Fin.addCases_right,lifted_head,lifted_frame radix a d source bs qs ns i hi] using hf
  apply congrArg₂ Tapes.mk
  · funext i; exact (point i).1
  · funext i; exact (point i).2

/-- Every descriptor is physically copied, stripped of its sentinel, and rewound;
the dimension bank and the array payload are framed. -/
theorem installs_hoare (radix a d : ℕ) (v : Tapes 16 radix) (source : ℤ → Fin 4)
    (bs qs ns : List Bool)
    (hready : ∀ k : Kind, v.head (sourceSlot target k) = 1 ∧
      v.tape (sourceSlot target k) = RadixZeroFill.encodedBinary (sourceWords target bs qs ns (sourceSlot target k))) :
    HoareTime (program target radix a d)
      (fun w => w = v.append (liftedBank radix a d source [] [] []))
      (fun w => w = v.append (liftedBank radix a d source bs qs ns))
      (cost (instructions target a d) (allWords target a d bs qs ns)) := by
  have hh := BinaryDescriptorInstallList.installs_hoare
    (by unfold TapeCount; omega : 0 < TapeCount a d) (instructions target a d) (disjoint target a d) (unique target a d)
    (allWords target a d bs qs ns) (v.append (liftedBank radix a d source [] [] []))
    (by
      rintro op hop
      obtain ⟨i,_,rfl⟩ := List.mem_map.mp hop
      simpa only [instruction,Tapes.append,allWords,Fin.addCases_left] using hready (kinds a d i))
    (by
      rintro op hop
      obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hop
      have hd := lifted_descriptor target radix a d source [] [] [] i ((mem_destinations a d i).mp hi)
      have he : sourceWords target [] [] [] (sourceSlot target (kinds a d i)) = [] := by
        cases target <;> cases kinds a d i <;> rfl
      rw [he,raw_nil] at hd
      simpa only [instruction,Tapes.append,Fin.addCases_right,lifted_head] using And.intro (rfl : (0 : ℤ) = 0) hd)
  exact hh.consequence (fun _ h => h) (fun w hw => hw.trans (result_exact target radix a d v source bs qs ns)) le_rfl

/-- Installation costs a fixed coefficient-dependent multiple of array volume. -/
theorem cost_volume (a d V : ℕ) (bs qs ns : List Bool) (hV : 0 < V)
    (hb : bs.length ≤ V) (hq : qs.length ≤ V) (hn : ns.length ≤ V) :
    cost (instructions target a d) (allWords target a d bs qs ns) ≤ 11*(LocalTapes a d)*V := by
  have hc := BinaryDescriptorInstallList.cost_le (instructions target a d) (allWords target a d bs qs ns) V (by
    rintro op hop
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hop
    simp only [instruction,allWords,Fin.addCases_left]
    cases target <;> cases kinds a d i <;> first | exact hb | exact hq | exact hn)
  have hl : (instructions target a d).length ≤ LocalTapes a d := by
    simpa only [instructions,destinations,List.length_map,List.length_finRange] using
      List.length_filter_le (fun i => isDescriptor (kinds a d i)) (List.finRange (LocalTapes a d))
  have hh := Nat.mul_le_mul_right (2*V+9) hl
  nlinarith

end IntegerMultBounds.Machine.RecursiveScalingInstall
