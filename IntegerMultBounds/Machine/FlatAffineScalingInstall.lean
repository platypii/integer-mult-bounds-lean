import IntegerMultBounds.Machine.FlatAffineScalingInputLayout
import IntegerMultBounds.Machine.BinaryDescriptorInstallList

/-! Physical installation of all affine-scaling dimension descriptors from one
preserved nine-tape dimension bank. The copy schedule depends only on coefficient. -/
namespace IntegerMultBounds.Machine.FlatAffineScalingInstall
open FlatAffineScalingInputLayout (Kind kinds bank word)
open BinaryDescriptorInstallList

abbrev LocalTapes (a d : ℕ) := SignedScalingDimensionsStream.TapeCount a d
abbrev TapeCount (a d : ℕ) := 9+LocalTapes a d

def isDescriptor : Kind → Bool
  | .block | .count | .prefix => true
  | _ => false

def sourceSlot : Kind → Fin 9
  | .block => 7
  | .prefix => 5
  | _ => 4

def instruction (a d : ℕ) (i : Fin (LocalTapes a d)) : Instruction (TapeCount a d) where
  source := Fin.castAdd _ (sourceSlot (kinds a d i))
  dest := Fin.natAdd 9 i
  distinct := by intro h; have := congrArg Fin.val h; have := (sourceSlot (kinds a d i)).isLt; simp only [Fin.val_castAdd,Fin.val_natAdd] at *; omega

def destinations (a d : ℕ) : List (Fin (LocalTapes a d)) :=
  (List.finRange _).filter (fun i => isDescriptor (kinds a d i))

def instructions (a d : ℕ) : List (Instruction (TapeCount a d)) :=
  (destinations a d).map (instruction a d)

theorem mem_destinations (a d : ℕ) (i : Fin (LocalTapes a d)) :
    i ∈ destinations a d ↔ isDescriptor (kinds a d i) = true := by simp [destinations]

theorem disjoint (a d : ℕ) : Disjoint (instructions a d) := by
  rintro x hx y hy he
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp hx
  obtain ⟨j,_,rfl⟩ := List.mem_map.mp hy
  have hv := congrArg Fin.val he
  have hj := (sourceSlot (kinds a d j)).isLt
  simp only [instruction,Fin.val_castAdd,Fin.val_natAdd] at hv
  omega

theorem unique (a d : ℕ) : Unique (instructions a d) := by
  unfold BinaryDescriptorInstallList.Unique instructions
  rw [List.map_map]
  apply List.Nodup.map
  · intro i j h
    apply Fin.ext
    have hv := congrArg Fin.val h
    change 9+i.val = 9+j.val at hv
    omega
  · exact (List.nodup_finRange _).filter _

def sourceWords (bs qs ns : List Bool) : Fin 9 → List Bool :=
  fun i => if i = 7 then bs else if i = 5 then ns else qs

private theorem sourceWords_kind (bs qs ns : List Bool) (k : Kind) :
    sourceWords bs qs ns (sourceSlot k) =
      (match k with | .block => bs | .prefix => ns | _ => qs) := by
  cases k <;> rfl

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
      BinaryDescriptorInstallRaw.rawWord radix (sourceWords bs qs ns (sourceSlot (kinds a d i))) := by
  unfold liftedBank Alphabet.mapTapes bank
  dsimp only
  cases hk : kinds a d i <;> simp only [hk,isDescriptor,Bool.false_eq_true] at hi
  all_goals first | contradiction | simpa [hk,word,sourceSlot,sourceWords] using encode_raw radix _

private theorem lifted_frame (radix a d : ℕ) (source : ℤ → Fin 4) (bs qs ns : List Bool)
    (i : Fin (LocalTapes a d)) (hi : isDescriptor (kinds a d i) ≠ true) :
    (liftedBank radix a d source [] [] []).tape i = (liftedBank radix a d source bs qs ns).tape i := by
  unfold liftedBank Alphabet.mapTapes bank
  dsimp only
  cases hk : kinds a d i <;> simp only [hk,isDescriptor] at hi
  all_goals first | contradiction | rfl

noncomputable def program (radix a d : ℕ) := BinaryDescriptorInstallList.program radix (by unfold TapeCount; omega : 0 < TapeCount a d) (instructions a d)

def allWords (a d : ℕ) (bs qs ns : List Bool) : Fin (TapeCount a d) → List Bool :=
  Fin.addCases (sourceWords bs qs ns) (fun _ => [])

private theorem result_exact (radix a d : ℕ) (v : Tapes 9 radix) (source : ℤ → Fin 4)
    (bs qs ns : List Bool) :
    result (instructions a d) (allWords a d bs qs ns) (v.append (liftedBank radix a d source [] [] [])) =
      v.append (liftedBank radix a d source bs qs ns) := by
  have point (i : Fin (TapeCount a d)) :
      (result (instructions a d) (allWords a d bs qs ns) (v.append (liftedBank radix a d source [] [] []))).head i =
        (v.append (liftedBank radix a d source bs qs ns)).head i ∧
      (result (instructions a d) (allWords a d bs qs ns) (v.append (liftedBank radix a d source [] [] []))).tape i =
        (v.append (liftedBank radix a d source bs qs ns)).tape i := by
    induction i using Fin.addCases with
    | left i =>
      have hf := result_frame (instructions a d) (allWords a d bs qs ns)
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
      · have hm : instruction a d i ∈ instructions a d :=
          List.mem_map.mpr ⟨i,(mem_destinations a d i).mpr hi,rfl⟩
        have hf := result_dest (instructions a d) (unique a d) (allWords a d bs qs ns)
          (v.append (liftedBank radix a d source [] [] [])) (instruction a d i) hm
        simp only [instruction,allWords,Fin.addCases_left] at hf
        simpa only [Tapes.append,Fin.addCases_right,lifted_head,lifted_descriptor radix a d source bs qs ns i hi]
          using hf
      · have hf := result_frame (instructions a d) (allWords a d bs qs ns)
          (v.append (liftedBank radix a d source [] [] [])) (Fin.natAdd 9 i) (by
            rintro op hop he
            obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hop
            have hij : i = j := by
              apply Fin.ext
              have hv := congrArg Fin.val he
              change 9+i.val = 9+j.val at hv
              omega
            exact hi (hij ▸ (mem_destinations a d j).mp hj))
        simpa only [Tapes.append,Fin.addCases_right,lifted_head,lifted_frame radix a d source bs qs ns i hi] using hf
  apply congrArg₂ Tapes.mk
  · funext i; exact (point i).1
  · funext i; exact (point i).2

/-- Every descriptor is physically copied, stripped of its sentinel, and rewound;
the dimension bank and the array payload are framed. -/
theorem installs_hoare (radix a d : ℕ) (v : Tapes 9 radix) (source : ℤ → Fin 4)
    (bs qs ns : List Bool)
    (hready : ∀ k : Kind, v.head (sourceSlot k) = 1 ∧
      v.tape (sourceSlot k) = RadixZeroFill.encodedBinary (sourceWords bs qs ns (sourceSlot k))) :
    HoareTime (program radix a d)
      (fun w => w = v.append (liftedBank radix a d source [] [] []))
      (fun w => w = v.append (liftedBank radix a d source bs qs ns))
      (cost (instructions a d) (allWords a d bs qs ns)) := by
  have hh := BinaryDescriptorInstallList.installs_hoare
    (by unfold TapeCount; omega : 0 < TapeCount a d) (instructions a d) (disjoint a d) (unique a d)
    (allWords a d bs qs ns) (v.append (liftedBank radix a d source [] [] []))
    (by
      rintro op hop
      obtain ⟨i,_,rfl⟩ := List.mem_map.mp hop
      simpa only [instruction,Tapes.append,allWords,Fin.addCases_left] using hready (kinds a d i))
    (by
      rintro op hop
      obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hop
      have hd := lifted_descriptor radix a d source [] [] [] i ((mem_destinations a d i).mp hi)
      have he : sourceWords [] [] [] (sourceSlot (kinds a d i)) = [] := by
        cases kinds a d i <;> rfl
      rw [he,raw_nil] at hd
      simpa only [instruction,Tapes.append,Fin.addCases_right,lifted_head] using And.intro (rfl : (0 : ℤ) = 0) hd)
  exact hh.consequence (fun _ h => h) (fun w hw => hw.trans (result_exact radix a d v source bs qs ns)) le_rfl

/-- Installation costs a fixed coefficient-dependent multiple of array volume. -/
theorem cost_volume (a d V : ℕ) (bs qs ns : List Bool) (hV : 0 < V)
    (hb : bs.length ≤ V) (hq : qs.length ≤ V) (hn : ns.length ≤ V) :
    cost (instructions a d) (allWords a d bs qs ns) ≤ 11*(LocalTapes a d)*V := by
  have hc := BinaryDescriptorInstallList.cost_le (instructions a d) (allWords a d bs qs ns) V (by
    rintro op hop
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hop
    simp only [instruction,allWords,Fin.addCases_left]
    cases kinds a d i <;> first | exact hb | exact hq | exact hn)
  have hl : (instructions a d).length ≤ LocalTapes a d := by
    simpa only [instructions,destinations,List.length_map,List.length_finRange] using
      List.length_filter_le (fun i => isDescriptor (kinds a d i)) (List.finRange (LocalTapes a d))
  have hh := Nat.mul_le_mul_right (2*V+9) hl
  nlinarith

end IntegerMultBounds.Machine.FlatAffineScalingInstall
