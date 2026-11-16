import BlockPermanents.FaceSlacks

/-! # The four-face improvement to the matching upper bound

The correction is a sum of genuine squared differences between the square
roots of adjacent matching moments. The spectator count and both permanent
bounds are attached to the given vectors.
-/
namespace BlockPermanents.RefinedCoarse
open FaceMeans FaceSlacks FacePeel Closures CycleMatching Matchings Threshold
noncomputable section

private theorem U_sum (z : ℕ → ℝ) (q r R : ℕ) (fit : q/2 ≤ R) :
    U z q r = ∑ s ∈ Finset.range (R+1), (pathCoeff q s : ℝ)*z (r+s) := by
  match q with
  | 0 | 1 =>
    rw [Finset.sum_range_succ']
    simp [U,pathCoeff]
  | n+2 =>
    obtain ⟨R,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : R ≠ 0)
    rw [U, U_sum z (n+1) r (R+1) (by omega), U_sum z n (r+1) R (by omega)]
    rw [Finset.sum_range_succ' (f := fun i => (pathCoeff (n+1) i : ℝ)*z (r+i)),
      Finset.sum_range_succ' (f := fun i => (pathCoeff (n+2) i : ℝ)*z (r+i))]
    simp only [pathCoeff,Nat.cast_one,Nat.cast_add,Nat.cast_pow,Nat.cast_mul,add_mul,
      Finset.sum_add_distrib,mul_assoc,← Finset.mul_sum,
      show ∀ s, z (r+(s+1)) = z ((r+1)+s) from fun s => congrArg z (by omega)]
    ring
termination_by q

private theorem full_H {m d : ℕ} (x : Input m d) : H x 0 m = MatchingFine.fine x := by
  let e : Roles 0 m ↪ Fin m :=
    ⟨Sum.elim (fun t => Fin.elim0 t.1) id, by
      rintro (⟨i,j⟩|i) (⟨a,b⟩|a) h
      · exact Fin.elim0 i
      · exact Fin.elim0 i
      · exact Fin.elim0 a
      · exact congrArg Sum.inr h⟩
  rw [H, mean, FaceSampling.sample_eq e]
  have h (σ : CycleMatching.S m) : FaceMeans.weight x (σ ∘ e) *
      MatchingFine.fine (active x (σ ∘ e)) = MatchingFine.fine x := by
    simp only [FaceMeans.weight,Finset.univ_eq_empty,Finset.prod_empty,one_mul]
    exact MatchingFine.fine_reindex σ x
  simp only [h, average_const]

private theorem four_slack {m d r : ℕ} (x : Input m d) (fit : 2*r+4 ≤ m) :
    FaceSlacks.S x 4 r = fourSlack x r := by
  let e := positions fit
  let p := Function.Embedding.inl.trans e
  let j := Function.Embedding.inr.trans e
  let z := Z (crossGram x x)
  have fresh (i : Fin 4) : j i ∉ Set.range p := by
    rintro ⟨k,hk⟩
    exact Sum.inl_ne_inr (e.injective hk)
  let P (y : Input 4 d) := FourTrade.edges (crossGram y y)
  let D (y : Input 4 d) := FourTrade.matchings (crossGram y y)
  have he := FaceTrade.extensions (crossGram x x) p j fresh
  have hp : mean x r 4 P = 6*z (r+1) := by
    rw [mean, FaceSampling.sample_eq e]
    simpa only [Fintype.card_fin] using he.1
  have hd : mean x r 4 D = 3*z (r+2) := by
    rw [mean, FaceSampling.sample_eq e]
    simpa only [Fintype.card_fin] using he.2
  have hs : fourSlack x r = mean x r 4 (fun y =>
      1 + 7/3*P y + 3*D y + (-1)*MatchingFine.fine y) := by
    unfold fourSlack FaceTrade.slack
    simp only [neg_one_mul, sub_eq_add_neg]
    rfl
  rw [hs]
  simp only [mean_linear x fit,mean_smul x fit, hp,hd,mean_one x fit]
  change U z 4 r - H x r 4 = z r + _ + _ + (-1)*H x r 4
  norm_num [U]
  ring

/-- The paper's refined upper bound on an actual unit Gram permanent,
including zero matching moments. -/
theorem upper {m d : ℕ} (x : Input m d) (schur : ∀ p q, SchurNormalization.HomogeneousSchur d p q)
    (unit : ∀ i, Bend.energy (x i)=1) :
    let z := Z (crossGram x x)
    MatchingFine.fine x ≤
      (∑ s ∈ Finset.range (m/2+1), (pathCoeff m s : ℝ)*z s) -
      ∑ s ∈ Finset.range (m+1), (spectator m s : ℝ)*(Real.sqrt (z (s+1))-Real.sqrt (z (s+2)))^2 := by
  let z := Z (crossGram x x)
  have hn (s : ℕ) : 0 ≤ z s := moment_nonneg (fun _ => zero_le_one) (fun _ _ => Complex.normSq_nonneg _)
  have h (s : ℕ) (fit : 2*s+4 ≤ m) :
      4*(Real.sqrt (z (s+1))-Real.sqrt (z (s+2)))^2 ≤ FaceSlacks.S x 4 s := by
    rw [four_slack x fit]
    exact TradeMatrix.optimize (hn _) (hn _) (fun u hu => weighted_gain x unit fit hu)
  have hp := FaceSlacks.propagate x schur unit (q := m) (r := 0) (R := m) (by omega) le_rfl
  have ht (s : ℕ) : 4*((spectator m s : ℝ)*(Real.sqrt (z (s+1))-Real.sqrt (z (s+2)))^2) ≤
      (spectator m s : ℝ)*FaceSlacks.S x 4 s := by
    by_cases fit : 2*s+4 ≤ m
    · linarith only [mul_le_mul_of_nonneg_left (h s fit) (show 0 ≤ (spectator m s : ℝ) by positivity)]
    · simp [FaceWeights.spectator_outside (by omega : m < 4+2*s)]
  have hs := Finset.sum_le_sum (s := Finset.range (m+1)) (fun s _ => ht s)
  rw [← Finset.mul_sum] at hs
  simp only [FaceWeights.weighted,Nat.zero_add] at hp
  unfold FaceSlacks.S at hp
  rw [full_H,U_sum _ m 0 (m/2) le_rfl] at hp
  simp only [Nat.zero_add] at hp
  change MatchingFine.fine x ≤ (∑ s ∈ Finset.range (m/2+1), (pathCoeff m s : ℝ)*z s) - _
  change _ ≤ 4*((∑ s ∈ Finset.range (m/2+1), (pathCoeff m s : ℝ)*z s) - MatchingFine.fine x) at hp
  have result := hs.trans hp
  change MatchingFine.fine x ≤ (∑ s ∈ Finset.range (m/2+1), (pathCoeff m s : ℝ)*z s) -
    ∑ s ∈ Finset.range (m+1), (spectator m s : ℝ)*(Real.sqrt (z (s+1))-Real.sqrt (z (s+2)))^2
  linarith only [result]

end
end BlockPermanents.RefinedCoarse
