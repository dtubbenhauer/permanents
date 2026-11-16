import BlockPermanents.PathJacobi
import BlockPermanents.Matchings

/-! Signed coefficients of the Jacobi characteristic polynomial in Theorem 7C.1. -/
namespace BlockPermanents.PathJacobi
open Polynomial Threshold
noncomputable section

/-- Removing r disjoint edges leaves degree m−2r, with sign (−1)^r and
coefficient the weighted path matching count. -/
theorem charpoly_coeff (m r : ℕ) (h : 2*r ≤ m) :
    ((J m).charpoly).coeff (m - 2*r) = (-1 : ℝ)^r * pathCoeff m r := by
  match m,r with
  | m, 0 =>
    simpa [pathCoeff] using (J m).charpoly_monic.coeff_natDegree
  | 0, r+1 | 1, r+1 => omega
  | n+2, r+1 =>
    have hr : 2*r ≤ n := by omega
    have first : (X * (J (n+1)).charpoly).coeff (n - 2*r) =
        (-1 : ℝ)^(r+1) * pathCoeff (n+1) (r+1) := by
      cases hk : n - 2*r with
      | zero =>
        rw [coeff_X_mul_zero, Matchings.pathCoeff_outside (by omega : n+1 < 2*(r+1))]
        simp
      | succ k =>
        rw [coeff_X_mul, show k = n+1 - 2*(r+1) by omega]
        exact charpoly_coeff (n+1) (r+1) (by omega)
    rw [show n+2 - 2*(r+1) = n-2*r by omega, charpoly_step, coeff_sub, first,
      coeff_C_mul, charpoly_coeff n r hr, pathCoeff]
    push_cast
    rw [pow_succ (-1 : ℝ) r]
    ring

/-- The coefficient vanishes whenever the number of vertices missing from
the degree is odd. -/
theorem charpoly_odd_coeff (m k : ℕ) (h : k ≤ m) (odd : Odd (m-k)) :
    ((J m).charpoly).coeff k = 0 := by
  obtain ⟨u,hu⟩ := odd
  match m with
  | 0 => omega
  | 1 =>
    have hk : k = 0 := by omega
    simp [hk,charpoly_one]
  | n+2 =>
    rw [charpoly_step, coeff_sub, coeff_C_mul]
    have first : (X * (J (n+1)).charpoly).coeff k = 0 := by
      cases k with
      | zero => exact coeff_X_mul_zero _
      | succ k =>
        rw [coeff_X_mul]
        exact charpoly_odd_coeff (n+1) k (by omega) ⟨u,by omega⟩
    have second : (J n).charpoly.coeff k = 0 := by
      by_cases hk : k ≤ n
      · exact charpoly_odd_coeff n k hk ⟨u-1,by omega⟩
      · apply coeff_eq_zero_of_natDegree_lt
        simpa using (lt_of_not_ge hk)
    simp [first,second]
termination_by m

end
end BlockPermanents.PathJacobi
