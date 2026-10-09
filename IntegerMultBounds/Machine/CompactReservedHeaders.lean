import IntegerMultBounds.Machine.CompactReservedAxisPorts
import IntegerMultBounds.Machine.CompactGlobalRowHeaders

/-! Original node/global geometry determines both reserved intervals. Fixed
network constants c,m occur only in finite control; all counts and the high
starting ordinal are physically computed from D,K,d,G. -/
namespace IntegerMultBounds.Machine.CompactReservedHeaders
noncomputable section
open ActiveRepairRankHeadersCommands (State)
open CompactGadgetReservationCapacity (backChunks frontChunks)
open CompactGlobalRowPadding (rowAxes)

abbrev high (c m d G K : ℕ) := rowAxes c m d+frontChunks d G K
abbrev reserved (c m d G K : ℕ) := high c m d G K+backChunks d G K

def initial (D K rho ell q d G : ℕ) : State := fun i => match i.val with
  | 0 => some D | 1 => some K | 2 => some rho | 3 => some ell | 4 => some q
  | 6 => some d | 7 => some G | _ => none

def rowOps (c m : ℕ) : List CompactGlobalRowHeaderOps.Op := [
  .constant (Nat.clog 2 c) 12,
  .ordinary (.command (.copy 6 13 (by decide))),
  .ordinary (.command (.add 13 6 (by decide))),
  .logarithm m ![13,14] (by decide),
  .ordinary (.product ![12,14,8] (by decide)),
  .ordinary (.command (.erase 12)),.ordinary (.command (.erase 13)),.ordinary (.command (.erase 14))]

def rowState (c m D K rho ell q d G : ℕ) : State :=
  Function.update (initial D K rho ell q d G) 8 (some (rowAxes c m d))

theorem row_valid (c m D K rho ell q d G : ℕ) (hc : 2≤c) (hm : 2≤m) (hd : 0<d) :
    CompactGlobalRowHeaderOps.validSchedule (rowOps c m) (initial D K rho ell q d G) := by
  have hl := CompactGlobalRowHeaders.logc_positive c hc
  simp [rowOps,CompactGlobalRowHeaderOps.validSchedule,CompactGlobalRowHeaderOps.valid,
    CompactGlobalRowHeaderOps.eval,ActivePrefixStageHeadersOps.valid,ActivePrefixStageHeadersOps.eval,
    ActiveRepairRankHeadersCommands.valid,ActiveRepairRankHeadersCommands.eval,
    ActiveRepairRankHeadersCommands.put,initial,Function.update,hm,hd,hl]

theorem row_executes (c m D K rho ell q d G : ℕ) :
    CompactGlobalRowHeaderOps.execute (rowOps c m) (initial D K rho ell q d G)=rowState c m D K rho ell q d G := by
  funext i
  fin_cases i <;> simp [rowOps,CompactGlobalRowHeaderOps.execute,CompactGlobalRowHeaderOps.eval,
    ActivePrefixStageHeadersOps.eval,ActiveRepairRankHeadersCommands.eval,
    ActiveRepairRankHeadersCommands.put,initial,rowState,Function.update,rowAxes,two_mul,Nat.mul_comm]

def countOps : List CompactChildHeadersArithmetic.Op := [
  .existing (.product ![6,7,15] (by decide)), .constant 17 1,
  .existing (.command (.difference 1 17 18 (by decide))),
  .existing (.command (.copy 15 19 (by decide))), .existing (.command (.add 19 18 (by decide))),
  .quotient ![19,1,9] (by decide),
  .existing (.command (.copy 15 16 (by decide))), .existing (.command (.add 16 15 (by decide))),
  .existing (.command (.copy 16 20 (by decide))), .existing (.command (.add 20 18 (by decide))),
  .quotient ![20,1,21] (by decide),
  .existing (.command (.copy 8 10 (by decide))), .existing (.command (.add 10 21 (by decide))),
  .existing (.command (.difference 0 10 11 (by decide))), .existing (.command (.zero 5))]

def counts (c m D K rho ell q d G : ℕ) :=
  CompactChildHeadersArithmetic.execute countOps (rowState c m D K rho ell q d G)

def eraseScratch : List CompactChildHeadersArithmetic.Op :=
  ([8,15,16,17,18,19,20,21] : List (Fin 28)).map (fun i => .existing (.command (.erase i)))

def prepared (c m D K rho ell q d G i : ℕ) : State := fun s => match s.val with
  | 5 => some i | 9 => some (backChunks d G K) | 10 => some (high c m d G K)
  | 11 => some (D-high c m d G K) | _ => initial D K rho ell q d G s

theorem count_valid (c m D K rho ell q d G : ℕ) (hd : 0<d) (hK : 0<K)
    (hD : reserved c m d G K≤D) :
    CompactChildHeadersArithmetic.validSchedule countOps (rowState c m D K rho ell q d G) := by
  have he : d*G+(K-1)=d*G+K-1 := by omega
  have he' : d*G+d*G+(K-1)=2*(d*G)+K-1 := by omega
  simp [countOps,CompactChildHeadersArithmetic.validSchedule,CompactChildHeadersArithmetic.valid,
    CompactChildHeadersArithmetic.eval,ActivePrefixStageHeadersOps.valid,ActivePrefixStageHeadersOps.eval,
    ActiveRepairRankHeadersCommands.valid,ActiveRepairRankHeadersCommands.eval,
    ActiveRepairRankHeadersCommands.put,initial,rowState,Function.update,hd,hK,Nat.mul_comm G d,he,he']
  unfold reserved high CompactGadgetReservationCapacity.frontChunks CompactGadgetReservationCapacity.chunks
    CompactGadgetReservationCapacity.capacity at hD
  omega

theorem cleanup_valid (c m D K rho ell q d G : ℕ) :
    CompactChildHeadersArithmetic.validSchedule eraseScratch (counts c m D K rho ell q d G) := by
  simp [eraseScratch,counts,countOps,CompactChildHeadersArithmetic.validSchedule,CompactChildHeadersArithmetic.valid,
    CompactChildHeadersArithmetic.execute,CompactChildHeadersArithmetic.eval,ActivePrefixStageHeadersOps.valid,
    ActivePrefixStageHeadersOps.eval,ActiveRepairRankHeadersCommands.valid,ActiveRepairRankHeadersCommands.eval,
    ActiveRepairRankHeadersCommands.put,initial,rowState,Function.update]

theorem cleanup_executes (c m D K rho ell q d G : ℕ) (hK : 0<K) :
    CompactChildHeadersArithmetic.execute eraseScratch (counts c m D K rho ell q d G)=prepared c m D K rho ell q d G 0 := by
  have he : d*G+(K-1)=d*G+K-1 := by omega
  have he' : d*G+d*G+(K-1)=2*(d*G)+K-1 := by omega
  funext i
  fin_cases i <;> simp [eraseScratch,counts,countOps,CompactChildHeadersArithmetic.execute,
    CompactChildHeadersArithmetic.eval,ActivePrefixStageHeadersOps.eval,ActiveRepairRankHeadersCommands.eval,
    ActiveRepairRankHeadersCommands.put,initial,rowState,prepared,Function.update,high,
    CompactGadgetReservationCapacity.frontChunks,CompactGadgetReservationCapacity.backChunks,
    CompactGadgetReservationCapacity.chunks,CompactGadgetReservationCapacity.capacity,Nat.mul_comm G d,he,he']

def program (c m : ℕ) := seq (seq (CompactGlobalRowHeaderOps.compile (a:=2) (rowOps c m)).2
  (CompactChildHeadersArithmetic.compile countOps).2) (CompactChildHeadersArithmetic.compile eraseScratch).2

def cost (c m D K rho ell q d G : ℕ) :=
  CompactGlobalRowHeaderOps.scheduleCost (rowOps c m) (initial D K rho ell q d G)+
  CompactChildHeadersArithmetic.scheduleCost countOps (rowState c m D K rho ell q d G)+
  CompactChildHeadersArithmetic.scheduleCost eraseScratch (counts c m D K rho ell q d G)+2

theorem runs (c m D K rho ell q d G : ℕ) (hc : 2≤c) (hm : 2≤m) (hd : 0<d) (hK : 0<K)
    (hD : reserved c m d G K≤D) :
    HoareTime (program c m) (fun v => v=ActiveRepairRankHeadersCommands.bank (initial D K rho ell q d G))
      (fun v => v=ActiveRepairRankHeadersCommands.bank (prepared c m D K rho ell q d G 0))
      (cost c m D K rho ell q d G) := by
  have h0 := CompactGlobalRowHeaderOps.schedule_runs (a:=2) (rowOps c m) _ (row_valid c m D K rho ell q d G hc hm hd)
  rw [row_executes] at h0
  have h1 := CompactChildHeadersArithmetic.schedule_runs (a:=2) countOps _ (count_valid c m D K rho ell q d G hd hK hD)
  have h2 := CompactChildHeadersArithmetic.schedule_runs (a:=2) eraseScratch _ (cleanup_valid c m D K rho ell q d G)
  rw [cleanup_executes c m D K rho ell q d G hK] at h2
  exact ((h0.seq h1).seq h2).consequence (fun _ h => h) (fun _ h => h) (by unfold cost; omega)

end
end IntegerMultBounds.Machine.CompactReservedHeaders
