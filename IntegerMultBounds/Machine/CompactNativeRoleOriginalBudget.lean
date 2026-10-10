import IntegerMultBounds.Machine.CompactNativeRoleHeaderBudget

/-! Complete native role caller budget: actual geometry synthesis, binary
row quotient, installed counts/markers, destructive transfer, source resets
and every generated-header cleanup fit fixed role-count times native volume. -/
namespace IntegerMultBounds.Machine.CompactNativeRoleOriginalBudget
noncomputable section
open CompactGadgetReservationShape (Shape)
open CompactNativeRoleOriginal (symbols erased words)
open CompactNativeRoleHeaders (prepared recordWidth)
open CompactNativeRoleTransferBudget (volume)
open ButterflyAxisHeadersArithmetic
open RecursiveChildQuotientsConstant (bits)

theorem cleanup_cost_eq (c : ℕ) (merge : Bool) (s : Shape) (rows ell p rho left count slots right source target : ℕ) :
    scheduleCost CompactNativeRoleHeaders.cleanup (prepared c merge s rows ell p rho left count slots right source target)=
      100*(s.H+s.B+s.F+s.bits+c+2^s.bits+2^ell+2^s.bits*2^ell+
        (recordWidth s p+1)+2*(recordWidth s p+1)+symbols s ell p+rows/c+
          (if merge then rows/c else rows)*symbols s ell p+13)+13 := by
  cases merge <;>
    dsimp [CompactNativeRoleHeaders.cleanup,List.map,ButterflyAxisHeadersData.cmd,scheduleCost,cost,eval,
      CompactChildHeadersArithmetic.cost,CompactChildHeadersArithmetic.eval,ActivePrefixStageHeadersOps.cost,
      ActivePrefixStageHeadersOps.eval,ActiveRepairRankHeadersCommands.cost,ActiveRepairRankHeadersCommands.eval,
      ActiveRepairRankHeadersCommands.put,prepared,CompactSpectatorLeafSetup.state,Function.update]
  all_goals simp only [Option.getD_some,symbols,CompactNativeRoleOriginal.inner]
  all_goals ring

theorem cleanup_linear (c : ℕ) (merge : Bool) (s : Shape) (rows ell p rho left count slots right source target : ℕ) (hr : 0<rows) :
    scheduleCost CompactNativeRoleHeaders.cleanup (prepared c merge s rows ell p rho left count slots right source target)≤
      (3000+100*(c+1))*volume rows s ell p := by
  have hV : 0<volume rows s ell p := Nat.mul_pos hr (CompactNativeRoleTransferBudget.symbols_pos s ell p)
  obtain ⟨hb,hp,hpow,hpoly,hinner,hwidth,hsym,hrows⟩ := CompactNativeRoleHeaderBudget.values_le s rows ell p hr
  have hH : s.H≤s.bits := by unfold Shape.bits; omega
  have hB : s.B≤s.bits := by unfold Shape.bits; omega
  have hF : s.F≤s.bits := by unfold Shape.bits; omega
  have hW := CompactNativeRoleControllerBudget.width_le_volume s rows ell p hr
  have hq := Nat.div_le_self rows c
  have he : (if merge then rows/c else rows)*symbols s ell p≤volume rows s ell p := by
    cases merge
    · exact le_rfl
    · exact Nat.mul_le_mul_right _ (Nat.div_le_self rows c)
  have hc : c≤c*volume rows s ell p := Nat.le_mul_of_pos_right _ hV
  rw [cleanup_cost_eq]
  simp only [Nat.mul_add,Nat.add_mul,Nat.mul_assoc] at *
  omega

theorem words_length (merge : Bool) (n c : ℕ) (s : Shape) (ell p : ℕ) (hc : 0<c) (hn : 0<n) :
    ∀ j,(words merge n c s ell p j).length≤volume (n*c) s ell p+1 := by
  have hr := Nat.mul_pos hn hc
  have hsym := (CompactNativeRoleHeaderBudget.values_le s (n*c) ell p hr).2.2.2.2.2.2.1
  have hrow := (CompactNativeRoleHeaderBudget.values_le s (n*c) ell p hr).2.2.2.2.2.2.2
  have hnrow := Nat.le_mul_of_pos_right n hc
  have he := CompactNativeRoleTransferBudget.erased_le merge n c s ell p hc
  have h0 := ActiveRepairRankHeadersCommands.bits_length (symbols s ell p)
  have h1 := ActiveRepairRankHeadersCommands.bits_length n
  have h2 := ActiveRepairRankHeadersCommands.bits_length (erased merge n c s ell p)
  intro j
  fin_cases j <;> simp [words]
  all_goals omega

theorem install_linear (merge : Bool) (n c : ℕ) (s : Shape) (ell p : ℕ) (hc : 0<c) (hn : 0<n) :
    BinaryDescriptorInstallMarkedList.cost (CompactNativeRoleInstall.instructions (c:=c))
      (CompactNativeRoleInstall.words (words merge n c s ell p))≤30*volume (n*c) s ell p := by
  have hV : 0<volume (n*c) s ell p := Nat.mul_pos (Nat.mul_pos hn hc) (CompactNativeRoleTransferBudget.symbols_pos s ell p)
  have hw := words_length merge n c s ell p hc hn
  have hh := BinaryDescriptorInstallMarkedList.cost_le (CompactNativeRoleInstall.instructions (c:=c))
    (CompactNativeRoleInstall.words (words merge n c s ell p)) (volume (n*c) s ell p+1) (by
      rintro op hop
      obtain ⟨j,_,rfl⟩ := List.mem_map.mp hop
      rw [CompactNativeRoleInstall.source_word]
      exact hw j)
  simp only [CompactNativeRoleInstall.instructions,List.length_map,List.length_finRange] at hh ⊢
  omega

theorem installed_cleanup_linear (merge : Bool) (n c : ℕ) (s : Shape) (ell p : ℕ) (hc : 0<c) (hn : 0<n) :
    BinaryDescriptorCleanupList.cost (CompactNativeRoleInstall.cleanupSlots (c:=c))
      (CompactNativeRoleInstall.cleanupWords (words merge n c s ell p))≤45*volume (n*c) s ell p := by
  have hV : 0<volume (n*c) s ell p := Nat.mul_pos (Nat.mul_pos hn hc) (CompactNativeRoleTransferBudget.symbols_pos s ell p)
  have hw := words_length merge n c s ell p hc hn
  have hb (i : Fin (CompactNativeRoleInstall.rawCount c)) :
      (CompactNativeRoleInstall.cleanupWords (words merge n c s ell p) i).length≤volume (n*c) s ell p+1 := by
    unfold CompactNativeRoleInstall.cleanupWords
    split_ifs
    · exact hw 0
    · exact hw 1
    · exact hw 2
    · simp
  have hh := BinaryDescriptorCleanupList.cost_le (CompactNativeRoleInstall.cleanupSlots (c:=c))
    (CompactNativeRoleInstall.cleanupWords (words merge n c s ell p)) (volume (n*c) s ell p+1) (fun i _ => hb i)
  simp only [CompactNativeRoleInstall.cleanupSlots,List.length_map,List.length_finRange] at hh ⊢
  omega

def constant (c : ℕ) := CompactNativeRoleHeaderBudget.constant c+4000+100*(c+1)

theorem cost_linear (merge : Bool) (n c : ℕ) (s : Shape) (ell p rho left count slots right source target : ℕ)
    (hc : 0<c) (hn : 0<n) (hA : 0<s.axes) (hG : 0<s.guard) (hK : 0<s.chunk) :
    CompactNativeRoleOriginal.cost merge n c s ell p rho left count slots right source target≤
      constant c*volume (n*c) s ell p := by
  have hr := Nat.mul_pos hn hc
  have hV : 0<volume (n*c) s ell p := Nat.mul_pos hr (CompactNativeRoleTransferBudget.symbols_pos s ell p)
  have h0 := CompactNativeRoleHeaderBudget.headers_linear c merge s (n*c) ell p rho left count slots right source target hr hA hG hK
  have h1 := install_linear merge n c s ell p hc hn
  have h2 := CompactNativeRoleTransferBudget.transfer_linear merge n c s ell p hc hn
  have h3 := installed_cleanup_linear merge n c s ell p hc hn
  have h4 := cleanup_linear c merge s (n*c) ell p rho left count slots right source target hr
  unfold CompactNativeRoleOriginal.cost constant
  simp only [Nat.add_mul,Nat.mul_add] at *
  omega

end
end IntegerMultBounds.Machine.CompactNativeRoleOriginalBudget
