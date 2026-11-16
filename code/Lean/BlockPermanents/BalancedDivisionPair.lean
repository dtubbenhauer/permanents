import BlockPermanents.OccupationBasis
import BlockPermanents.BalancedCorners

/-! The fine and coarse pair kernels are unchanged when the two packets
exchange their places at both ends. -/
namespace BlockPermanents.BalancedDivision
open Bend OccupationBasis

private theorem append_swap_occ {d k : ℕ} (a b : Word d k) :
    occ (Fin.append b a) = occ (Fin.append a b) := by
  funext j
  unfold occ OccupationSplit.counts
  have count (w : Word d (k+k)) :
      (Finset.univ.filter fun i => w i = j).card = ∑ i, if w i = j then 1 else 0 := by
    exact (Finset.sum_boole (α := ℕ) (fun i => w i = j) Finset.univ).symm
  simp only [count, Fin.sum_univ_add, Fin.append_left, Fin.append_right]
  exact add_comm _ _

theorem fine_pair_swap {d k : ℕ} (a b c e : Word d k) :
    totalClasp d k k (b,a) (e,c) = totalClasp d k k (a,b) (c,e) := by
  unfold totalClasp
  simp only [← kernel_word, kernel_eq, append_swap_occ a b, append_swap_occ c e]

theorem packet_pair_swap {d k : ℕ} (a b c e : Word d k) :
    BalancedCorners.packetPair d k (b,a) (e,c) = BalancedCorners.packetPair d k (a,b) (c,e) := by
  simp only [BalancedCorners.packetPair]
  ring

end BlockPermanents.BalancedDivision
