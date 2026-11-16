import BlockPermanents.ExitAverage
import BlockPermanents.RoutingAttachment
import BlockPermanents.RoutingTransport

/-! # Packet-clasp and signed transfer formulas for the iterated operator -/
namespace BlockPermanents.RoutingFibres
open Equiv Routings ExitAverage
open scoped BigOperators
noncomputable section
variable {n k : ℕ} {R : Type*} [Ring R] [Algebra ℚ R]

abbrev packets (ρ : Wire (n+1) k →* R) := ρ.comp (packetHom (n+1) k)
abbrev oldPackets (ρ : Wire (n+1) k →* R) := (packets ρ).comp (keep n)

/-- The old operator with a straight last spectator and all internal clasps. -/
def attached (ρ : Wire (n+1) k →* R) :=
  internal ρ * iterate (ρ.comp (attach (Fin.last n))) * internal ρ

private theorem both {G : Type*} [Fintype G] [Group G] (π : G →* R) (x : R) :
    Transfer.clasp π * x * Transfer.clasp π =
      average (fun t : G => average (fun s : G => π s * x * π t)) := by
  rw [right]
  apply congrArg average
  funext t
  rw [mul_assoc, left]
  simp only [mul_assoc]

private theorem moveL (ρ : Wire (n+1) k →* R) (s : Perm (Fin (n+1))) (i j : Fin (n+1))
    (hk : 0<k) (c : ℕ → ℚ) : packets ρ s * exitOp ρ i j c = exitOp ρ i (s j) c := by
  simpa [packets] using move_exit ρ s 1 i j hk c

private theorem moveR (ρ : Wire (n+1) k →* R) (s : Perm (Fin (n+1))) (i j : Fin (n+1))
    (hk : 0<k) (c : ℕ → ℚ) : exitOp ρ i j c * packets ρ s = exitOp ρ (s.symm i) j c := by
  simpa [packets] using move_exit ρ 1 s i j hk c

/-- Averaging both packet ends of the straight spectator freely chooses its input and output. -/
theorem full_clasp_attachment (ρ : Wire (n+1) k →* R) (hk : 0<k) :
    Transfer.clasp (packets ρ) * attached ρ * Transfer.clasp (packets ρ) =
      average (fun i => average (fun j => exitOp ρ i j (fun b => n/b))) := by
  rw [both,attached,← exit_attachment _ _ hk]
  simp only [packets,MonoidHom.comp_apply,move_exit _ _ _ _ _ hk]
  let X (i j : Fin (n+1)) := exitOp ρ i j (fun b => n/b)
  have inr (t : Perm (Fin (n+1))) := orbit (Fin.last n) (fun j => X (t.symm (Fin.last n)) j)
  change average (fun t : Perm (Fin (n+1)) => average (fun s : Perm (Fin (n+1)) => X (t.symm (Fin.last n)) (s (Fin.last n)))) = _
  simp_rw [inr]
  exact orbit_inv (Fin.last n) (fun i => average (X i))

/-- The literal recurrence with the packet clasp at both ends of the attached old iterate. -/
theorem iterate_clasp_step (ρ : Wire (n+1) k →* R) (hk : 0<k) (hn : 0<n) :
    iterate ρ = defect ρ + (((n+1:ℚ)^2)/n) •
      (Transfer.clasp (packets ρ) * attached ρ * Transfer.clasp (packets ρ)) := by
  rw [iterate_step ρ hk hn,full_clasp_attachment ρ hk,Fintype.sum_prod_type]
  simp only [average,Fintype.card_fin,Nat.cast_succ,← Finset.smul_sum,smul_smul]
  congr 2
  have hn' : (n:ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hp : (n:ℚ)+1 ≠ 0 := by positivity
  field_simp; ring

/-- Signed operator before simultaneous relabeling. The two old slots determine the
moved and crossed swaps, respectively. -/
def signedTransfer (ρ : Wire (n+1) k →* R) (p q : Fin n) : R :=
  let f := Transfer.clasp (oldPackets ρ)
  let s := packets ρ (swap (Fin.last n) p.castSucc)
  let t := packets ρ (swap (Fin.last n) q.castSucc)
  let A := attached ρ
  defect ρ - A + (n:ℚ) • (f * (s*A*s) * f) -
    (((n:ℚ)-1)/2) • (A*t*f + f*t*A)

/-- The four terms of the transfer give the signed exit count of each prescribed routing. -/
theorem signedTransfer_eq_marked (ρ : Wire (n+1) k →* R) (p q : Fin n) (hk : 0<k) :
    signedTransfer ρ p q = marked ρ (Fin.last n) := by
  let X (i j : Fin (n+1)) := exitOp ρ i j (fun b => n/b)
  have shift (i j : Fin (n+1)) (s t : Perm (Fin (n+1))) :
      packets ρ s * X i j * packets ρ t = X (t.symm i) (s j) :=
    move_exit _ _ _ _ _ hk _
  have L (i j : Fin (n+1)) (s : Perm (Fin (n+1))) : packets ρ s * X i j = X i (s j) :=
    moveL _ _ _ _ hk _
  have T (i j : Fin (n+1)) (s : Perm (Fin (n+1))) : X i j * packets ρ s = X (s.symm i) j :=
    moveR _ _ _ _ hk _
  have hA : attached ρ = X (Fin.last n) (Fin.last n) := (exit_attachment _ _ hk).symm
  have moved :
      Transfer.clasp (oldPackets ρ) * X p.castSucc p.castSucc * Transfer.clasp (oldPackets ρ) =
      average (fun i : Fin n => average (fun j : Fin n => X i.castSucc j.castSucc)) := by
    rw [both]
    change average (fun t => average (fun s => packets ρ (keep n s) * X p.castSucc p.castSucc * packets ρ (keep n t))) = _
    simp only [shift,keep_symm_cast,keep_cast]
    have inr (t : Perm (Fin n)) := orbit p (fun j => X (t.symm p).castSucc j.castSucc)
    simp_rw [inr]
    exact orbit_inv p (fun i => average (fun j : Fin n => X i.castSucc j.castSucc))
  have crossR : X q.castSucc (Fin.last n) * Transfer.clasp (oldPackets ρ) =
      average (fun i : Fin n => X i.castSucc (Fin.last n)) := by
    rw [right]
    change average (fun t => X q.castSucc (Fin.last n) * packets ρ (keep n t)) = _
    simp only [T,keep_symm_cast]
    exact orbit_inv q (fun i => X i.castSucc (Fin.last n))
  have crossL : Transfer.clasp (oldPackets ρ) * X (Fin.last n) q.castSucc =
      average (fun j : Fin n => X (Fin.last n) j.castSucc) := by
    rw [left]
    change average (fun s => packets ρ (keep n s) * X (Fin.last n) q.castSucc) = _
    simp only [L,keep_cast]
    exact orbit q (fun j => X (Fin.last n) j.castSucc)
  unfold signedTransfer marked
  dsimp only
  rw [weights (Nat.zero_lt_of_lt p.isLt) X,hA]
  change _ = defect ρ + (-X _ _ + _ - _)
  rw [shift,T,mul_assoc (Transfer.clasp (oldPackets ρ)) (packets ρ (swap (Fin.last n) q.castSucc)),L]
  simp only [symm_swap,swap_apply_left,swap_apply_right]
  rw [moved,crossR,crossL]
  abel_nf

/-- The packet permutation action fixes the underlying coarse/fine defect on either end. -/
private theorem defect_biinvariant (ρ : Wire (n+1) k →* R) (s t : Perm (Fin (n+1))) :
    packets ρ s * defect ρ * packets ρ t = defect ρ := by
  have hl (v : Perm (Fin (n+1))) : packets ρ v * internal ρ = internal ρ * packets ρ v :=
    packet_internal _ _
  have aux (z : R) (hz : packets ρ s * z = z) (ht : z * packets ρ t = z) :
      packets ρ s * (internal ρ * z * internal ρ) * packets ρ t = internal ρ * z * internal ρ := by
    calc
      _ = internal ρ * (packets ρ s * z) * (packets ρ t * internal ρ) := by
        rw [← mul_assoc,← mul_assoc,hl s,hl t]
        simp only [mul_assoc]
      _ = _ := by rw [hz,← mul_assoc (internal ρ * z),mul_assoc (internal ρ),ht]
  unfold defect
  simp only [mul_sub,sub_mul,mul_smul_comm,smul_mul_assoc]
  rw [aux _ (Transfer.absorb_left ρ _) (Transfer.absorb_right ρ _),
    aux _ (Transfer.absorb_left (packets ρ) _) (Transfer.absorb_right (packets ρ) _)]

private theorem conjugate_mark (ρ : Wire (n+1) k →* R) (s : Perm (Fin (n+1))) (a : Fin (n+1))
    (hk : 0<k) : packets ρ s * marked ρ a * packets ρ s⁻¹ = marked ρ (s a) := by
  unfold marked
  simp only [mul_add,add_mul,defect_biinvariant,Finset.mul_sum,Finset.sum_mul,
    mul_smul_comm,smul_mul_assoc]
  congr 1
  let v (b : Fin (n+1)) (ij : Fin (n+1) × Fin (n+1)) :=
    (Routing.exitWeight b ij / n) • exitOp ρ ij.1 ij.2 (fun c => n/c)
  have h (ij : Fin (n+1) × Fin (n+1)) :
      (Routing.exitWeight a ij / n) •
        (packets ρ s * exitOp ρ ij.1 ij.2 (fun c => n/c) * packets ρ s⁻¹) =
      v (s a) ((s.prodCongr s) ij) := by
    simp only [packets,MonoidHom.comp_apply,move_exit _ _ _ _ _ hk,v,Equiv.prodCongr_apply,
      Prod.map_fst,Prod.map_snd,Routing.exitWeight,EmbeddingLike.apply_eq_iff_eq]
    rfl
  simp_rw [h]
  exact Equiv.sum_comp (s.prodCongr s) (v (s a))

/-- The average over marked packets recovers the defect before any numerical specialization. -/
theorem mean_marked (ρ : Wire (n+1) k →* R) (hk : 0<k) (hn : 0<n) :
    average (marked ρ) = defect ρ := by
  classical
  have form (a : Fin (n+1)) : marked ρ a =
      ∑ M : Routing (n+1) k,(weight M * M.transferred a) • routingOp ρ M := by
    rw [marked_expand ρ a hk hn]
    apply Finset.sum_congr rfl
    intro M _
    rw [Routing.transferred_eq _ hk, Nat.cast_succ,mul_assoc]
  unfold average
  simp_rw [form]
  rw [Finset.sum_comm,Finset.smul_sum,defect,defect_expand ρ hk]
  apply Finset.sum_congr rfl
  intro M _
  rw [← Finset.sum_smul,← Finset.mul_sum,smul_smul,Fintype.card_fin]
  by_cases h : M.splitInputs.card = 0
  · simp [Routing.transferred,h]
  · rw [M.transferred_sum hk h,if_neg h]
    have hp : ((n+1:ℕ):ℚ)≠0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero _)
    congr 1
    field_simp

/-- The literal bracket of the signed routing operator equals the fine/coarse defect. -/
theorem bracket_signedTransfer (ρ : Wire (n+1) k →* R) (p q : Fin n) (hk : 0<k) :
    Transfer.bracket (packets ρ) (signedTransfer ρ p q) = defect ρ := by
  rw [signedTransfer_eq_marked _ _ _ hk]
  change average (fun s => packets ρ s * marked ρ (Fin.last n) * packets ρ s⁻¹) = _
  simp_rw [conjugate_mark ρ _ _ hk]
  exact (orbit (Fin.last n) (marked ρ)).trans (mean_marked ρ hk (Nat.zero_lt_of_lt p.isLt))

end
end BlockPermanents.RoutingFibres
