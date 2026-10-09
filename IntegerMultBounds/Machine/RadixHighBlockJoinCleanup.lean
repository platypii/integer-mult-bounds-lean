import IntegerMultBounds.Machine.RadixHighBlockJoinInitialize

/-! Paid erasure of working high-block descriptors, preserving the source,
original shape descriptors, rho, and the complete outer-loop clock. -/
namespace IntegerMultBounds.Machine.RadixHighBlockJoinCleanup
noncomputable section
open RadixHighBlockJoinSetup
open RecursiveChildQuotientsConstant (bits)
variable {q a : ℕ}

def prefixProgram := BinaryDescriptorCleanupList.oneProgram (a := a) (prefixSlot (q := q))
def suffixProgram := BinaryDescriptorCleanupList.oneProgram (a := a) (suffixSlot (q := q))
def baseProgram := BinaryDescriptorCleanupList.oneProgram (a := a) (baseSlot (q := q))
def program := seq (seq (prefixProgram (q := q) (a := a)) suffixProgram) baseProgram

theorem prefix_hoare (source : ℤ → Fin (a+4)) (ss op oe : List Bool)
    (ps : List Bool) (es ws : Option (List Bool)) (ctrl : Tapes 2 a) :
    HoareTime (prefixProgram (q := q) (a := a))
      (fun v => v = bank source ss op oe (some ps) es ws ctrl)
      (fun v => v = bank source ss op oe none es ws ctrl) (2*ps.length+4) := by
  have h := BinaryDescriptorCleanupList.one_hoare (prefixSlot (q := q))
    (bank source ss op oe (some ps) es ws ctrl) ps
    (by simp only [prefixSlot,read_head,read_tape]; simp (disch := omega) [read_head,read_tape,optionHead,optionTape,
      RadixHighBlockJoinBank.prefixSlot,RadixHighBlockJoinBank.suffixSlot,RadixHighBlockJoinBank.baseSlot,
      RadixHighBlockJoinBank.spectatorSlot,RadixHighBlockJoinBank.originalPrefixSlot,RadixHighBlockJoinBank.originalSuffixSlot,
      ite_eq_right,ite_eq_left,-Fin.val_eq_zero_iff]; exact (encoded_binary _).symm.trans (encoded_descriptor _))
    (by simp only [prefixSlot,read_head,read_tape]; simp (disch := omega) [read_head,read_tape,optionHead,optionTape,
      RadixHighBlockJoinBank.prefixSlot,RadixHighBlockJoinBank.suffixSlot,RadixHighBlockJoinBank.baseSlot,
      RadixHighBlockJoinBank.spectatorSlot,RadixHighBlockJoinBank.originalPrefixSlot,RadixHighBlockJoinBank.originalSuffixSlot,
      ite_eq_right,ite_eq_left,-Fin.val_eq_zero_iff])
  apply h.consequence (fun _ h => h) _ le_rfl
  rintro v rfl
  exact clear_prefix source ss op oe _ _ _ ctrl

theorem suffix_hoare (source : ℤ → Fin (a+4)) (ss op oe : List Bool)
    (es : List Bool) (ps ws : Option (List Bool)) (ctrl : Tapes 2 a) :
    HoareTime (suffixProgram (q := q) (a := a))
      (fun v => v = bank source ss op oe ps (some es) ws ctrl)
      (fun v => v = bank source ss op oe ps none ws ctrl) (2*es.length+4) := by
  have h := BinaryDescriptorCleanupList.one_hoare (suffixSlot (q := q))
    (bank source ss op oe ps (some es) ws ctrl) es
    (by simp only [suffixSlot,read_head,read_tape]; simp (disch := omega) [read_head,read_tape,optionHead,optionTape,
      RadixHighBlockJoinBank.prefixSlot,RadixHighBlockJoinBank.suffixSlot,RadixHighBlockJoinBank.baseSlot,
      RadixHighBlockJoinBank.spectatorSlot,RadixHighBlockJoinBank.originalPrefixSlot,RadixHighBlockJoinBank.originalSuffixSlot,
      ite_eq_right,ite_eq_left,-Fin.val_eq_zero_iff]; exact (encoded_binary _).symm.trans (encoded_descriptor _))
    (by simp only [suffixSlot,read_head,read_tape]; simp (disch := omega) [read_head,read_tape,optionHead,optionTape,
      RadixHighBlockJoinBank.prefixSlot,RadixHighBlockJoinBank.suffixSlot,RadixHighBlockJoinBank.baseSlot,
      RadixHighBlockJoinBank.spectatorSlot,RadixHighBlockJoinBank.originalPrefixSlot,RadixHighBlockJoinBank.originalSuffixSlot,
      ite_eq_right,ite_eq_left,-Fin.val_eq_zero_iff])
  apply h.consequence (fun _ h => h) _ le_rfl
  rintro v rfl
  exact clear_suffix source ss op oe _ _ _ ctrl

theorem base_hoare (source : ℤ → Fin (a+4)) (ss op oe : List Bool)
    (ws : List Bool) (ps es : Option (List Bool)) (ctrl : Tapes 2 a) :
    HoareTime (baseProgram (q := q) (a := a))
      (fun v => v = bank source ss op oe ps es (some ws) ctrl)
      (fun v => v = bank source ss op oe ps es none ctrl) (2*ws.length+4) := by
  have h := BinaryDescriptorCleanupList.one_hoare (baseSlot (q := q))
    (bank source ss op oe ps es (some ws) ctrl) ws
    (by simp only [baseSlot,read_head,read_tape]; simp (disch := omega) [read_head,read_tape,optionHead,optionTape,
      RadixHighBlockJoinBank.prefixSlot,RadixHighBlockJoinBank.suffixSlot,RadixHighBlockJoinBank.baseSlot,
      RadixHighBlockJoinBank.spectatorSlot,RadixHighBlockJoinBank.originalPrefixSlot,RadixHighBlockJoinBank.originalSuffixSlot,
      ite_eq_right,ite_eq_left,-Fin.val_eq_zero_iff]; exact (encoded_binary _).symm.trans (encoded_descriptor _))
    (by simp only [baseSlot,read_head,read_tape]; simp (disch := omega) [read_head,read_tape,optionHead,optionTape,
      RadixHighBlockJoinBank.prefixSlot,RadixHighBlockJoinBank.suffixSlot,RadixHighBlockJoinBank.baseSlot,
      RadixHighBlockJoinBank.spectatorSlot,RadixHighBlockJoinBank.originalPrefixSlot,RadixHighBlockJoinBank.originalSuffixSlot,
      ite_eq_right,ite_eq_left,-Fin.val_eq_zero_iff])
  apply h.consequence (fun _ h => h) _ le_rfl
  rintro v rfl
  exact clear_base source ss op oe _ _ _ ctrl

/-- Literal descriptor widths are charged, so cleanup accepts whatever
canonical representations the repeated join/separate body actually produces. -/
theorem cleans (source : ℤ → Fin (a+4)) (ss op oe ps es : List Bool) (ctrl : Tapes 2 a) :
    HoareTime (program (q := q) (a := a))
      (fun v => v = bank source ss op oe (some ps) (some es) (some (bits q)) ctrl)
      (fun v => v = bank source ss op oe none none none ctrl)
      (2*ps.length+2*es.length+2*(bits q).length+14) := by
  have h := ((prefix_hoare (q := q) source ss op oe ps (some es) (some (bits q)) ctrl).seq
    (suffix_hoare source ss op oe es none (some (bits q)) ctrl)).seq
    (base_hoare source ss op oe (bits q) none none ctrl)
  apply h.consequence (fun _ h => h) (fun _ h => h)
  omega

def coefficient (q : ℕ) := 2*(bits q).length+22

theorem cleans_linear (source : ℤ → Fin (a+4)) (ss op oe ps es : List Bool)
    (ctrl : Tapes 2 a) (V : ℕ) (hV : 0 < V)
    (cp : GrowingCounterData.Canonical ps) (ce : GrowingCounterData.Canonical es)
    (hp : Counter.value ps ≤ V) (he : Counter.value es ≤ V) :
    HoareTime (program (q := q) (a := a))
      (fun v => v = bank source ss op oe (some ps) (some es) (some (bits q)) ctrl)
      (fun v => v = bank source ss op oe none none none ctrl) (coefficient q*V) := by
  apply (cleans (q := q) source ss op oe ps es ctrl).consequence (fun _ h => h) (fun _ h => h)
  have wp := (GrowingCounterData.canonical_width ps cp).trans
    (Nat.add_le_add_right (Nat.log2_le_self _) 1)
  have we := (GrowingCounterData.canonical_width es ce).trans
    (Nat.add_le_add_right (Nat.log2_le_self _) 1)
  have hb := Nat.le_mul_of_pos_right (2*(bits q).length+14) hV
  dsimp only [coefficient]
  nlinarith

end
end IntegerMultBounds.Machine.RadixHighBlockJoinCleanup
