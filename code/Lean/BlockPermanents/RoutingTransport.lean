import BlockPermanents.RoutingExits

/-! # Moving a prescribed spectator at either boundary -/
namespace BlockPermanents.RoutingFibres
open Equiv Routings
open scoped BigOperators
noncomputable section

variable {m n k : ℕ} {R : Type*} [Ring R] [Algebra ℚ R]

private theorem packet_within (s : Perm (Fin m)) (g : Fin m → Perm (Fin k)) :
    packetHom m k s * within g = within (g ∘ s.symm) * packetHom m k s := by
  apply Equiv.ext; rintro ⟨i,t⟩
  change (s i,g i t) = (s i,g (s.symm (s i)) t)
  rw [s.symm_apply_apply]

theorem packet_internal (ρ : Wire m k →* R) (s : Perm (Fin m)) :
    ρ (packetHom m k s) * internal ρ = internal ρ * ρ (packetHom m k s) := by
  simp only [internal,Transfer.clasp,mul_smul_comm,smul_mul_assoc,Finset.mul_sum,Finset.sum_mul,MonoidHom.comp_apply]
  apply congrArg (_ • ·)
  have h (g : Fin m → Perm (Fin k)) :
      ρ (packetHom m k s) * ρ (within g) = ρ (within (g ∘ s.symm)) * ρ (packetHom m k s) := by
    rw [← map_mul,packet_within,map_mul]
  simp_rw [h]
  exact Equiv.sum_comp (s.arrowCongr (Equiv.refl (Perm (Fin k))))
    (fun g => ρ (within g) * ρ (packetHom m k s))

theorem move_compressed (ρ : Wire m k →* R) (s t : Perm (Fin m)) (p : Wire m k) :
    ρ (packetHom m k s) * compressed ρ p * ρ (packetHom m k t) =
      compressed ρ (packetHom m k s * p * packetHom m k t) := by
  simp only [compressed,map_mul]
  calc
    _ = (ρ (packetHom m k s)*internal ρ)*ρ p*(internal ρ*ρ (packetHom m k t)) := by simp [mul_assoc]
    _ = _ := by rw [packet_internal ρ s,← packet_internal ρ t];simp [mul_assoc]

theorem move_entry (s t : Perm (Fin m)) (p : Wire m k) (i j : Fin m) :
    (table (packetHom m k s * p * packetHom m k t)).entries i j =
      (table p).entries (t i) (s.symm j) := by
  change Fintype.card {a : Fin k // s (p (t i,a)).1=j} = Fintype.card {a : Fin k // (p (t i,a)).1=s.symm j}
  exact Fintype.card_congr (Equiv.subtypeEquivRight fun _ => s.apply_eq_iff_eq_symm_apply)

theorem split_move (s t : Perm (Fin m)) (p : Wire m k) :
    (table (packetHom m k s * p * packetHom m k t)).splitInputs =
      (table p).splitInputs.map t.symm.toEmbedding := by
  ext i
  rw [Finset.mem_map_equiv,split_mem,split_mem]
  simp only [move_entry,symm_symm]
  constructor
  · intro h j;simpa using h (s j)
  · intro h j;exact h (s.symm j)

theorem move_exit (ρ : Wire (n+1) k →* R) (s t : Perm (Fin (n+1))) (i j : Fin (n+1))
    (hk : 0<k) (c : ℕ → ℚ) :
    ρ (packetHom (n+1) k s) * exitOp ρ i j c * ρ (packetHom (n+1) k t) =
      exitOp ρ (t.symm i) (s j) c := by
  let g (i j : Fin (n+1)) (p : Wire (n+1) k) :=
    (if (i,j) ∈ (table p).whole then c (table p).splitInputs.card else 0) • compressed ρ p
  have asSum (i j : Fin (n+1)) : exitOp ρ i j c =
      ((k.factorial:ℚ)^(n+1))⁻¹ • ∑ p : Wire (n+1) k, g i j p :=
    (exit_expand ρ i j hk c).trans (weighted_expand ρ _).symm
  rw [asSum,asSum,mul_smul_comm,smul_mul_assoc,Finset.mul_sum,Finset.sum_mul]
  apply congrArg (_ • ·)
  let L := packetHom (n+1) k s
  let T := packetHom (n+1) k t
  have h (p : Wire (n+1) k) : ρ L * g i j p * ρ T = g (t.symm i) (s j) (L*p*T) := by
    dsimp only [g,L,T]
    rw [mul_smul_comm,smul_mul_assoc,move_compressed,split_move,Finset.card_map]
    simp only [Routing.whole,Finset.mem_filter,Finset.mem_univ,true_and,move_entry,
      apply_symm_apply,symm_apply_apply]
  change (∑ p, ρ L * g i j p * ρ T) = _
  simp_rw [h]
  exact Equiv.sum_comp ((Equiv.mulLeft L).trans (Equiv.mulRight T)) (g (t.symm i) (s j))

end
end BlockPermanents.RoutingFibres
