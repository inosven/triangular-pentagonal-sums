import Mathlib

/-!
# Sums of two triangular numbers and a pentagonal number

Formalization of the elementary part of the paper
"Every natural number is a sum of two triangular numbers and a pentagonal number".

The classical input (primitive representation by `x² + 3y² + 3z²` and `x² + y² + 3z²`,
Proposition 4.1 of the paper) is not proved here; it enters as the explicit hypotheses
`PrimRep133` and `PrimRep113`.
-/

namespace TriPent

/-! ## The partner of an odd pair (Section 2) -/

theorem normI {u v u' v' : ℤ} (h1 : 2 * u' = u + v) (h2 : 2 * v' = 3 * u - v) :
    3 * u' ^ 2 + v' ^ 2 = 3 * u ^ 2 + v ^ 2 := by
  have : 4 * (3 * u' ^ 2 + v' ^ 2) = 4 * (3 * u ^ 2 + v ^ 2) := by
    linear_combination 3 * (2 * u' + u + v) * h1 + (2 * v' + 3 * u - v) * h2
  linarith

theorem normII {u v u' v' : ℤ} (h1 : 2 * u' = u + v) (h2 : 2 * v' = v - 3 * u) :
    3 * u' ^ 2 + v' ^ 2 = 3 * u ^ 2 + v ^ 2 := by
  have : 4 * (3 * u' ^ 2 + v' ^ 2) = 4 * (3 * u ^ 2 + v ^ 2) := by
    linear_combination 3 * (2 * u' + u + v) * h1 + (2 * v' + v - 3 * u) * h2
  linarith

theorem normIII {u v u' v' : ℤ} (h1 : 2 * u' = u - v) (h2 : 2 * v' = 3 * u + v) :
    3 * u' ^ 2 + v' ^ 2 = 3 * u ^ 2 + v ^ 2 := by
  have : 4 * (3 * u' ^ 2 + v' ^ 2) = 4 * (3 * u ^ 2 + v ^ 2) := by
    linear_combination 3 * (2 * u' + u - v) * h1 + (2 * v' + 3 * u + v) * h2
  linarith

theorem normIII' {u v u' v' : ℤ} (h1 : 2 * u' = v - u) (h2 : 2 * v' = 3 * u + v) :
    3 * u' ^ 2 + v' ^ 2 = 3 * u ^ 2 + v ^ 2 := by
  have : 4 * (3 * u' ^ 2 + v' ^ 2) = 4 * (3 * u ^ 2 + v ^ 2) := by
    linear_combination 3 * (2 * u' + v - u) * h1 + (2 * v' + 3 * u + v) * h2
  linarith

/-- Lemma 2.2: an odd positive pair `(u, v)` with `3 ∤ v` has a partner `(u', v')` with the same
value of `3u² + v²`. Either `v'` and `v` have different residues mod 3 (cases II, III), or the
partner is given by the linear formulas of case I. -/
theorem partner (u v : ℤ) (hu0 : 0 < u) (hv0 : 0 < v) (hu : u % 2 = 1) (hv : v % 2 = 1)
    (hv3 : v % 3 ≠ 0) :
    ∃ u' v' : ℤ, 0 < u' ∧ 0 < v' ∧ u' % 2 = 1 ∧ v' % 2 = 1 ∧ v' % 3 ≠ 0 ∧
      3 * u' ^ 2 + v' ^ 2 = 3 * u ^ 2 + v ^ 2 ∧
      (v' % 3 ≠ v % 3 ∨ (v < 3 * u ∧ 2 * u' = u + v ∧ 2 * v' = 3 * u - v)) := by
  by_cases h4 : (u - v) % 4 = 0
  · rcases lt_or_gt_of_ne (show v ≠ 3 * u by omega) with hlt | hgt
    · -- case I
      obtain ⟨u', h1⟩ : ∃ u' : ℤ, 2 * u' = u + v := ⟨(u + v) / 2, by omega⟩
      obtain ⟨v', h2⟩ : ∃ v' : ℤ, 2 * v' = 3 * u - v := ⟨(3 * u - v) / 2, by omega⟩
      exact ⟨u', v', by omega, by omega, by omega, by omega, by omega, normI h1 h2,
        Or.inr ⟨hlt, h1, h2⟩⟩
    · -- case II
      obtain ⟨u', h1⟩ : ∃ u' : ℤ, 2 * u' = u + v := ⟨(u + v) / 2, by omega⟩
      obtain ⟨v', h2⟩ : ∃ v' : ℤ, 2 * v' = v - 3 * u := ⟨(v - 3 * u) / 2, by omega⟩
      exact ⟨u', v', by omega, by omega, by omega, by omega, by omega, normII h1 h2,
        Or.inl (by omega)⟩
  · -- case III
    obtain ⟨v', h2⟩ : ∃ v' : ℤ, 2 * v' = 3 * u + v := ⟨(3 * u + v) / 2, by omega⟩
    rcases lt_or_gt_of_ne (show u ≠ v by omega) with hlt | hgt
    · obtain ⟨u', h1⟩ : ∃ u' : ℤ, 2 * u' = v - u := ⟨(v - u) / 2, by omega⟩
      exact ⟨u', v', by omega, by omega, by omega, by omega, by omega, normIII' h1 h2,
        Or.inl (by omega)⟩
    · obtain ⟨u', h1⟩ : ∃ u' : ℤ, 2 * u' = u - v := ⟨(u - v) / 2, by omega⟩
      exact ⟨u', v', by omega, by omega, by omega, by omega, by omega, normIII h1 h2,
        Or.inl (by omega)⟩

/-! ## The 2-adic lemma (Lemma 3.1) -/

/-- A sequence of integer pairs that is periodic, bounded, and satisfies a linear recurrence
`Rel` with the two properties below, is identically zero. -/
theorem descent {Rel : ℤ → ℤ → ℤ → ℤ → Prop}
    (hlin : ∀ p q p' q', Rel (2 * p) (2 * q) (2 * p') (2 * q') → Rel p q p' q')
    (heven : ∀ p q p' q' pm qm, Rel p q p' q' → Rel pm qm p q → p % 2 = 0 ∧ q % 2 = 0) :
    ∀ (B : ℕ) (z : ℕ → ℤ × ℤ),
      (∀ k, Rel (z k).1 (z k).2 (z (k + 1)).1 (z (k + 1)).2) →
      ∀ r : ℕ, 1 ≤ r → (∀ k, z (k + r) = z k) →
      (∀ k, -(B : ℤ) ≤ (z k).1 ∧ (z k).1 ≤ B ∧ -(B : ℤ) ≤ (z k).2 ∧ (z k).2 ≤ B) →
      ∀ k, z k = (0, 0) := by
  intro B
  induction B using Nat.strong_induction_on with
  | _ B ih =>
    intro z hrec r hr hper hB k
    have hev : ∀ k, (z k).1 % 2 = 0 ∧ (z k).2 % 2 = 0 := by
      intro k
      have h1 := hrec k
      have h2 := hrec (k + r - 1)
      have e : k + r - 1 + 1 = k + r := by omega
      rw [e, hper k] at h2
      exact heven _ _ _ _ _ _ h1 h2
    by_cases hB0 : B = 0
    · subst hB0
      have hk := hB k
      have h1 : (z k).1 = 0 := by omega
      have h2 : (z k).2 = 0 := by omega
      exact Prod.ext h1 h2
    · have hz := ih (B / 2) (by omega) (fun k => ((z k).1 / 2, (z k).2 / 2)) ?_ r hr ?_ ?_ k
      · have hk := hev k
        have hz1 : (z k).1 / 2 = 0 := congrArg Prod.fst hz
        have hz2 : (z k).2 / 2 = 0 := congrArg Prod.snd hz
        have h1 : (z k).1 = 0 := by omega
        have h2 : (z k).2 = 0 := by omega
        exact Prod.ext h1 h2
      · intro k
        apply hlin
        have a1 := hev k
        have a2 := hev (k + 1)
        have e1 : 2 * ((z k).1 / 2) = (z k).1 := by omega
        have e2 : 2 * ((z k).2 / 2) = (z k).2 := by omega
        have e3 : 2 * ((z (k + 1)).1 / 2) = (z (k + 1)).1 := by omega
        have e4 : 2 * ((z (k + 1)).2 / 2) = (z (k + 1)).2 := by omega
        show Rel (2 * ((z k).1 / 2)) (2 * ((z k).2 / 2)) (2 * ((z (k + 1)).1 / 2))
          (2 * ((z (k + 1)).2 / 2))
        rw [e1, e2, e3, e4]
        exact hrec k
      · intro k
        show ((z (k + r)).1 / 2, (z (k + r)).2 / 2) = ((z k).1 / 2, (z k).2 / 2)
        rw [hper k]
      · intro k
        have hk := hB k
        have hk2 := hev k
        show -((B / 2 : ℕ) : ℤ) ≤ (z k).1 / 2 ∧ (z k).1 / 2 ≤ ((B / 2 : ℕ) : ℤ) ∧
          -((B / 2 : ℕ) : ℤ) ≤ (z k).2 / 2 ∧ (z k).2 / 2 ≤ ((B / 2 : ℕ) : ℤ)
        omega

/-- The recurrence given by the matrix `M₁`. -/
def Rel1 (p q p' q' : ℤ) : Prop := 4 * p' = 5 * p - 6 * q ∧ 4 * q' = 6 * p - 4 * q

/-- The recurrence given by the matrix `M₂`. -/
def Rel2 (p q p' q' : ℤ) : Prop := 4 * p' = -3 * p - 2 * q ∧ 4 * q' = 2 * p - 4 * q

theorem descent1 : ∀ (B : ℕ) (z : ℕ → ℤ × ℤ),
    (∀ k, Rel1 (z k).1 (z k).2 (z (k + 1)).1 (z (k + 1)).2) →
    ∀ r : ℕ, 1 ≤ r → (∀ k, z (k + r) = z k) →
    (∀ k, -(B : ℤ) ≤ (z k).1 ∧ (z k).1 ≤ B ∧ -(B : ℤ) ≤ (z k).2 ∧ (z k).2 ≤ B) →
    ∀ k, z k = (0, 0) :=
  descent (Rel := Rel1)
    (by rintro p q p' q' ⟨h1, h2⟩; exact ⟨by omega, by omega⟩)
    (by rintro p q p' q' pm qm ⟨h1, h2⟩ ⟨h3, h4⟩; exact ⟨by omega, by omega⟩)

theorem descent2 : ∀ (B : ℕ) (z : ℕ → ℤ × ℤ),
    (∀ k, Rel2 (z k).1 (z k).2 (z (k + 1)).1 (z (k + 1)).2) →
    ∀ r : ℕ, 1 ≤ r → (∀ k, z (k + r) = z k) →
    (∀ k, -(B : ℤ) ≤ (z k).1 ∧ (z k).1 ≤ B ∧ -(B : ℤ) ≤ (z k).2 ∧ (z k).2 ≤ B) →
    ∀ k, z k = (0, 0) :=
  descent (Rel := Rel2)
    (by rintro p q p' q' ⟨h1, h2⟩; exact ⟨by omega, by omega⟩)
    (by rintro p q p' q' pm qm ⟨h1, h2⟩ ⟨h3, h4⟩; exact ⟨by omega, by omega⟩)

/-- A periodic point of a self-map: if `f^[i] x = f^[j] x` with `i < j`, the orbit from `i` on
has period `j - i`. -/
theorem iterate_periodic {α : Type*} (f : α → α) (x : α) {i j : ℕ} (hij : i < j)
    (h : f^[i] x = f^[j] x) (k : ℕ) : f^[i + k + (j - i)] x = f^[i + k] x := by
  have e : i + k + (j - i) = k + j := by omega
  rw [e, Function.iterate_add_apply, ← h, ← Function.iterate_add_apply, Nat.add_comm]

/-! ## Theorem 3.2 -/

/-- `(v, a, b)` is a solution of `v² + 3a² + 3b² = N` in odd positive integers with `3 ∤ v`. -/
def IsS (N v a b : ℤ) : Prop :=
  0 < v ∧ 0 < a ∧ 0 < b ∧ v % 2 = 1 ∧ a % 2 = 1 ∧ b % 2 = 1 ∧ v % 3 ≠ 0 ∧
    v ^ 2 + 3 * a ^ 2 + 3 * b ^ 2 = N

theorem IsS.le {N v a b : ℤ} (h : IsS N v a b) : v ≤ N ∧ a ≤ N ∧ b ≤ N := by
  obtain ⟨hv0, ha0, hb0, -, -, -, -, heq⟩ := h
  refine ⟨by nlinarith, by nlinarith, by nlinarith⟩

/-- The move `α`: either some solution has a different residue of `v` mod 3, or `α` is the
linear map `A`. -/
theorem IsS.moveA {N v a b : ℤ} (h : IsS N v a b) :
    (∃ v' a' b', IsS N v' a' b' ∧ v' % 3 ≠ v % 3) ∨
      IsS N ((3 * a - v) / 2) ((a + v) / 2) b := by
  obtain ⟨hv0, ha0, hb0, hv, ha, hb, hv3, heq⟩ := h
  obtain ⟨a', v', ha'0, hv'0, ha', hv', hv'3, hn, hcase⟩ := partner a v ha0 hv0 ha hv hv3
  have hS : IsS N v' a' b := ⟨hv'0, ha'0, hb0, hv', ha', hb, hv'3, by linarith⟩
  rcases hcase with hne | ⟨_, h1, h2⟩
  · exact Or.inl ⟨v', a', b, hS, hne⟩
  · right
    have e1 : (3 * a - v) / 2 = v' := by omega
    have e2 : (a + v) / 2 = a' := by omega
    rw [e1, e2]
    exact hS

/-- The move `β`. -/
theorem IsS.moveB {N v a b : ℤ} (h : IsS N v a b) :
    (∃ v' a' b', IsS N v' a' b' ∧ v' % 3 ≠ v % 3) ∨
      IsS N ((3 * b - v) / 2) a ((b + v) / 2) := by
  obtain ⟨hv0, ha0, hb0, hv, ha, hb, hv3, heq⟩ := h
  obtain ⟨b', v', hb'0, hv'0, hb', hv', hv'3, hn, hcase⟩ := partner b v hb0 hv0 hb hv hv3
  have hS : IsS N v' a b' := ⟨hv'0, ha0, hb'0, hv', ha, hb', hv'3, by linarith⟩
  rcases hcase with hne | ⟨_, h1, h2⟩
  · exact Or.inl ⟨v', a, b', hS, hne⟩
  · right
    have e1 : (3 * b - v) / 2 = v' := by omega
    have e2 : (b + v) / 2 = b' := by omega
    rw [e1, e2]
    exact hS

/-- The map `R = BA` on triples `(v, a, b)`. -/
def stepS (s : ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ :=
  ((3 * s.2.2 - (3 * s.2.1 - s.1) / 2) / 2, (s.2.1 + s.1) / 2,
    (s.2.2 + (3 * s.2.1 - s.1) / 2) / 2)

theorem stepS_rec {N : ℤ} {s : ℤ × ℤ × ℤ} (h : IsS N s.1 s.2.1 s.2.2)
    (hA : IsS N ((3 * s.2.1 - s.1) / 2) ((s.2.1 + s.1) / 2) s.2.2) :
    Rel1 (s.2.1 - s.1) (s.2.2 - s.1) ((stepS s).2.1 - (stepS s).1)
      ((stepS s).2.2 - (stepS s).1) := by
  obtain ⟨-, -, -, hv, ha, hb, -, -⟩ := h
  obtain ⟨-, -, -, hv1, -, -, -, -⟩ := hA
  simp only [stepS, Rel1]
  constructor <;> omega

/-- **Theorem 3.2.** If `v² + 3a² + 3b² = N` has a solution in odd positive integers with
`3 ∤ v` that is not diagonal, then it has such a solution with the other residue of `v` mod 3. -/
theorem exists_other_residue {N v a b : ℤ} (h : IsS N v a b) (hnd : ¬(v = a ∧ a = b)) :
    ∃ v' a' b', IsS N v' a' b' ∧ v' % 3 ≠ v % 3 := by
  by_contra hcon
  push Not at hcon
  -- under `hcon`, the set of solutions is closed under the linear maps `A` and `R = BA`
  have hcl : ∀ s : ℤ × ℤ × ℤ, IsS N s.1 s.2.1 s.2.2 →
      IsS N ((3 * s.2.1 - s.1) / 2) ((s.2.1 + s.1) / 2) s.2.2 ∧
      IsS N (stepS s).1 (stepS s).2.1 (stepS s).2.2 := by
    intro s hs
    have hA : IsS N ((3 * s.2.1 - s.1) / 2) ((s.2.1 + s.1) / 2) s.2.2 := by
      rcases hs.moveA with ⟨v', a', b', h', hne⟩ | h'
      · exact absurd ((hcon v' a' b' h').trans (hcon _ _ _ hs).symm) hne
      · exact h'
    refine ⟨hA, ?_⟩
    rcases hA.moveB with ⟨v', a', b', h', hne⟩ | h'
    · exact absurd ((hcon v' a' b' h').trans (hcon _ _ _ hA).symm) hne
    · exact h'
  have ht : ∀ j, IsS N (stepS^[j] (v, a, b)).1 (stepS^[j] (v, a, b)).2.1
      (stepS^[j] (v, a, b)).2.2 := by
    intro j
    induction j with
    | zero => exact h
    | succ j ih =>
      rw [Function.iterate_succ_apply']
      exact (hcl _ ih).2
  have hN : 0 < N := by
    have := h.le
    have := h.1
    omega
  -- the orbit is contained in a finite box, hence eventually periodic
  have hbd : ∀ j, stepS^[j] (v, a, b) ∈ Set.Icc ((0, 0, 0) : ℤ × ℤ × ℤ) (N, N, N) := by
    intro j
    have h1 := ht j
    have h2 := h1.le
    exact ⟨⟨h1.1.le, h1.2.1.le, h1.2.2.1.le⟩, ⟨h2.1, h2.2.1, h2.2.2⟩⟩
  obtain ⟨i, j, hij, hEq⟩ := (Set.finite_Icc _ _).exists_lt_map_eq_of_forall_mem hbd
  have hper := iterate_periodic stepS (v, a, b) hij hEq
  -- the differences `(a - v, b - v)` along the orbit
  have hrec : ∀ m, Rel1 ((stepS^[m] (v, a, b)).2.1 - (stepS^[m] (v, a, b)).1)
      ((stepS^[m] (v, a, b)).2.2 - (stepS^[m] (v, a, b)).1)
      ((stepS^[m + 1] (v, a, b)).2.1 - (stepS^[m + 1] (v, a, b)).1)
      ((stepS^[m + 1] (v, a, b)).2.2 - (stepS^[m + 1] (v, a, b)).1) := by
    intro m
    rw [Function.iterate_succ_apply']
    exact stepS_rec (ht m) (hcl _ (ht m)).1
  have hzero := descent1 N.toNat
    (fun k => ((stepS^[i + k] (v, a, b)).2.1 - (stepS^[i + k] (v, a, b)).1,
      (stepS^[i + k] (v, a, b)).2.2 - (stepS^[i + k] (v, a, b)).1))
    (fun k => hrec (i + k)) (j - i) (by omega)
    (fun k => by
      show ((stepS^[i + (k + (j - i))] (v, a, b)).2.1 - (stepS^[i + (k + (j - i))] (v, a, b)).1,
        (stepS^[i + (k + (j - i))] (v, a, b)).2.2 - (stepS^[i + (k + (j - i))] (v, a, b)).1) = _
      rw [← Nat.add_assoc, hper k])
    (fun k => by
      have h1 := ht (i + k)
      have h2 := h1.le
      have h3 := h1.1
      have h4 := h1.2.1
      have h5 := h1.2.2.1
      show -((N.toNat : ℕ) : ℤ) ≤ _ ∧ _ ≤ ((N.toNat : ℕ) : ℤ) ∧ -((N.toNat : ℕ) : ℤ) ≤ _ ∧
        _ ≤ ((N.toNat : ℕ) : ℤ)
      omega) 0
  -- go back from index `i` to index `0`
  have hback : ∀ m, (stepS^[m] (v, a, b)).2.1 - (stepS^[m] (v, a, b)).1 = 0 ∧
      (stepS^[m] (v, a, b)).2.2 - (stepS^[m] (v, a, b)).1 = 0 →
      a - v = 0 ∧ b - v = 0 := by
    intro m
    induction m with
    | zero => exact fun hm => hm
    | succ m ih =>
      intro hm
      apply ih
      obtain ⟨r1, r2⟩ := hrec m
      omega
  have h0 := hback i ⟨congrArg Prod.fst hzero, congrArg Prod.snd hzero⟩
  exact hnd ⟨by omega, by omega⟩

/-! ## Theorem 3.3 -/

/-- `(u, v, w)` is a solution of `3u² + v² + w² = N` in odd positive integers with `3 ∤ vw`. -/
def IsT (N u v w : ℤ) : Prop :=
  0 < u ∧ 0 < v ∧ 0 < w ∧ u % 2 = 1 ∧ v % 2 = 1 ∧ w % 2 = 1 ∧ v % 3 ≠ 0 ∧ w % 3 ≠ 0 ∧
    3 * u ^ 2 + v ^ 2 + w ^ 2 = N

theorem IsT.le {N u v w : ℤ} (h : IsT N u v w) : u ≤ N ∧ v ≤ N ∧ w ≤ N := by
  obtain ⟨hu0, hv0, hw0, -, -, -, -, -, heq⟩ := h
  refine ⟨by nlinarith, by nlinarith, by nlinarith⟩

theorem IsT.swap {N u v w : ℤ} (h : IsT N u v w) : IsT N u w v := by
  obtain ⟨hu0, hv0, hw0, hu, hv, hw, hv3, hw3, heq⟩ := h
  exact ⟨hu0, hw0, hv0, hu, hw, hv, hw3, hv3, by linarith⟩

theorem IsT.moveA {N u v w : ℤ} (h : IsT N u v w) (hvw : v % 3 = w % 3) :
    (∃ u' v' w', IsT N u' v' w' ∧ v' % 3 ≠ w' % 3) ∨
      IsT N ((u + v) / 2) ((3 * u - v) / 2) w := by
  obtain ⟨hu0, hv0, hw0, hu, hv, hw, hv3, hw3, heq⟩ := h
  obtain ⟨u', v', hu'0, hv'0, hu', hv', hv'3, hn, hcase⟩ := partner u v hu0 hv0 hu hv hv3
  have hT : IsT N u' v' w := ⟨hu'0, hv'0, hw0, hu', hv', hw, hv'3, hw3, by linarith⟩
  rcases hcase with hne | ⟨_, h1, h2⟩
  · exact Or.inl ⟨u', v', w, hT, by omega⟩
  · right
    have e1 : (u + v) / 2 = u' := by omega
    have e2 : (3 * u - v) / 2 = v' := by omega
    rw [e1, e2]
    exact hT

theorem IsT.moveB {N u v w : ℤ} (h : IsT N u v w) (hvw : v % 3 = w % 3) :
    (∃ u' v' w', IsT N u' v' w' ∧ v' % 3 ≠ w' % 3) ∨
      IsT N ((u + w) / 2) v ((3 * u - w) / 2) := by
  rcases h.swap.moveA hvw.symm with ⟨u', v', w', h', hne⟩ | h'
  · exact Or.inl ⟨u', w', v', h'.swap, fun e => hne e.symm⟩
  · exact Or.inr h'.swap

/-- The map `R = BA` on triples `(u, v, w)`. -/
def stepT (s : ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ :=
  (((s.1 + s.2.1) / 2 + s.2.2) / 2, (3 * s.1 - s.2.1) / 2,
    (3 * ((s.1 + s.2.1) / 2) - s.2.2) / 2)

theorem stepT_rec {N : ℤ} {s : ℤ × ℤ × ℤ} (h : IsT N s.1 s.2.1 s.2.2)
    (hA : IsT N ((s.1 + s.2.1) / 2) ((3 * s.1 - s.2.1) / 2) s.2.2) :
    Rel2 (s.1 - s.2.1) (s.1 - s.2.2) ((stepT s).1 - (stepT s).2.1)
      ((stepT s).1 - (stepT s).2.2) := by
  obtain ⟨-, -, -, hu, hv, hw, -, -, -⟩ := h
  obtain ⟨-, -, -, hu1, -, -, -, -, -⟩ := hA
  simp only [stepT, Rel2]
  constructor <;> omega

/-- **Theorem 3.3.** If `3u² + v² + w² = N` has a solution in odd positive integers with
`3 ∤ vw` that is not diagonal, then it has such a solution with `v ≢ w (mod 3)`. -/
theorem exists_mixed {N u v w : ℤ} (h : IsT N u v w) (hnd : ¬(u = v ∧ v = w)) :
    ∃ u' v' w', IsT N u' v' w' ∧ v' % 3 ≠ w' % 3 := by
  by_contra hcon
  push Not at hcon
  have hcl : ∀ s : ℤ × ℤ × ℤ, IsT N s.1 s.2.1 s.2.2 →
      IsT N ((s.1 + s.2.1) / 2) ((3 * s.1 - s.2.1) / 2) s.2.2 ∧
      IsT N (stepT s).1 (stepT s).2.1 (stepT s).2.2 := by
    intro s hs
    have hA : IsT N ((s.1 + s.2.1) / 2) ((3 * s.1 - s.2.1) / 2) s.2.2 := by
      rcases hs.moveA (hcon _ _ _ hs) with ⟨u', v', w', h', hne⟩ | h'
      · exact absurd (hcon u' v' w' h') hne
      · exact h'
    refine ⟨hA, ?_⟩
    rcases hA.moveB (hcon _ _ _ hA) with ⟨u', v', w', h', hne⟩ | h'
    · exact absurd (hcon u' v' w' h') hne
    · exact h'
  have ht : ∀ j, IsT N (stepT^[j] (u, v, w)).1 (stepT^[j] (u, v, w)).2.1
      (stepT^[j] (u, v, w)).2.2 := by
    intro j
    induction j with
    | zero => exact h
    | succ j ih =>
      rw [Function.iterate_succ_apply']
      exact (hcl _ ih).2
  have hbd : ∀ j, stepT^[j] (u, v, w) ∈ Set.Icc ((0, 0, 0) : ℤ × ℤ × ℤ) (N, N, N) := by
    intro j
    have h1 := ht j
    have h2 := h1.le
    exact ⟨⟨h1.1.le, h1.2.1.le, h1.2.2.1.le⟩, ⟨h2.1, h2.2.1, h2.2.2⟩⟩
  obtain ⟨i, j, hij, hEq⟩ := (Set.finite_Icc _ _).exists_lt_map_eq_of_forall_mem hbd
  have hper := iterate_periodic stepT (u, v, w) hij hEq
  have hrec : ∀ m, Rel2 ((stepT^[m] (u, v, w)).1 - (stepT^[m] (u, v, w)).2.1)
      ((stepT^[m] (u, v, w)).1 - (stepT^[m] (u, v, w)).2.2)
      ((stepT^[m + 1] (u, v, w)).1 - (stepT^[m + 1] (u, v, w)).2.1)
      ((stepT^[m + 1] (u, v, w)).1 - (stepT^[m + 1] (u, v, w)).2.2) := by
    intro m
    rw [Function.iterate_succ_apply']
    exact stepT_rec (ht m) (hcl _ (ht m)).1
  have hzero := descent2 N.toNat
    (fun k => ((stepT^[i + k] (u, v, w)).1 - (stepT^[i + k] (u, v, w)).2.1,
      (stepT^[i + k] (u, v, w)).1 - (stepT^[i + k] (u, v, w)).2.2))
    (fun k => hrec (i + k)) (j - i) (by omega)
    (fun k => by
      show ((stepT^[i + (k + (j - i))] (u, v, w)).1 - (stepT^[i + (k + (j - i))] (u, v, w)).2.1,
        (stepT^[i + (k + (j - i))] (u, v, w)).1 - (stepT^[i + (k + (j - i))] (u, v, w)).2.2) = _
      rw [← Nat.add_assoc, hper k])
    (fun k => by
      have h1 := ht (i + k)
      have h2 := h1.le
      have h3 := h1.1
      have h4 := h1.2.1
      have h5 := h1.2.2.1
      show -((N.toNat : ℕ) : ℤ) ≤ _ ∧ _ ≤ ((N.toNat : ℕ) : ℤ) ∧ -((N.toNat : ℕ) : ℤ) ≤ _ ∧
        _ ≤ ((N.toNat : ℕ) : ℤ)
      omega) 0
  have hback : ∀ m, (stepT^[m] (u, v, w)).1 - (stepT^[m] (u, v, w)).2.1 = 0 ∧
      (stepT^[m] (u, v, w)).1 - (stepT^[m] (u, v, w)).2.2 = 0 →
      u - v = 0 ∧ u - w = 0 := by
    intro m
    induction m with
    | zero => exact fun hm => hm
    | succ m ih =>
      intro hm
      apply ih
      obtain ⟨r1, r2⟩ := hrec m
      omega
  have h0 := hback i ⟨congrArg Prod.fst hzero, congrArg Prod.snd hzero⟩
  exact hnd ⟨by omega, by omega⟩

/-! ## Squares modulo 8 and 3 -/

theorem sq_mod8 (x : ℤ) : (x % 2 = 1 ∧ x ^ 2 % 8 = 1) ∨ (x % 4 = 0 ∧ x ^ 2 % 8 = 0) ∨
    (x % 4 = 2 ∧ x ^ 2 % 8 = 4) := by
  have key : x ^ 2 % 8 = x % 8 * (x % 8) % 8 := by rw [pow_two]; exact Int.mul_emod x x 8
  have h8 : x % 8 = 0 ∨ x % 8 = 1 ∨ x % 8 = 2 ∨ x % 8 = 3 ∨ x % 8 = 4 ∨ x % 8 = 5 ∨ x % 8 = 6 ∨
      x % 8 = 7 := by omega
  rcases h8 with h | h | h | h | h | h | h | h <;> rw [h] at key <;> norm_num at key <;> omega

theorem sq_mod3 (x : ℤ) : (x % 3 = 0 ∧ x ^ 2 % 3 = 0) ∨ (x % 3 ≠ 0 ∧ x ^ 2 % 3 = 1) := by
  have key : x ^ 2 % 3 = x % 3 * (x % 3) % 3 := by rw [pow_two]; exact Int.mul_emod x x 3
  have h3 : x % 3 = 0 ∨ x % 3 = 1 ∨ x % 3 = 2 := by omega
  rcases h3 with h | h | h <;> rw [h] at key <;> norm_num at key <;> omega

/-! ## Starting points (Lemma 4.2) -/

theorem IsS.swap {N v a b : ℤ} (h : IsS N v a b) : IsS N v b a := by
  obtain ⟨hv0, ha0, hb0, hv, ha, hb, hv3, heq⟩ := h
  exact ⟨hv0, hb0, ha0, hv, hb, ha, hv3, by linarith⟩

theorem mod3_S {N v a b : ℤ} (heq : v ^ 2 + 3 * a ^ 2 + 3 * b ^ 2 = N) (hN : N % 3 = 1) :
    v % 3 ≠ 0 := by
  rcases sq_mod3 v with ⟨h, h2⟩ | ⟨h, h2⟩
  · omega
  · exact h

theorem mod3_T {N u v w : ℤ} (heq : 3 * u ^ 2 + v ^ 2 + w ^ 2 = N) (hN : N % 3 = 2) :
    v % 3 ≠ 0 ∧ w % 3 ≠ 0 := by
  rcases sq_mod3 v with ⟨h, h2⟩ | ⟨h, h2⟩ <;> rcases sq_mod3 w with ⟨h', h2'⟩ | ⟨h', h2'⟩ <;>
    omega

/-- Case 2 of Lemma 4.2(a): from a solution with `V`, `B` even to a solution in odd numbers. -/
theorem seedS_even {N V A B : ℤ} (hN3 : N % 3 = 1) (hV : 0 ≤ V) (hB : 0 ≤ B) (hA0 : 0 < A)
    (heq : V ^ 2 + 3 * A ^ 2 + 3 * B ^ 2 = N) (hA1 : A % 2 = 1) (hV0 : V % 2 = 0)
    (hB0 : B % 2 = 0) (h4 : (V + B) % 4 = 2) :
    ∃ v₁ b₁ : ℤ, IsS N v₁ A b₁ ∧ (v₁ = A ∧ A = b₁ → B = 0 ∧ V = 2 * A) := by
  obtain ⟨v₁, h2⟩ : ∃ v₁ : ℤ, 2 * v₁ = 3 * B + V := ⟨(3 * B + V) / 2, by omega⟩
  rcases lt_or_gt_of_ne (show B ≠ V by omega) with hlt | hgt
  · obtain ⟨b₁, h1⟩ : ∃ b₁ : ℤ, 2 * b₁ = V - B := ⟨(V - B) / 2, by omega⟩
    have hn := normIII' h1 h2
    have heq' : v₁ ^ 2 + 3 * A ^ 2 + 3 * b₁ ^ 2 = N := by linarith
    refine ⟨v₁, b₁, ⟨by omega, hA0, by omega, by omega, hA1, by omega, mod3_S heq' hN3, heq'⟩, ?_⟩
    rintro ⟨e1, e2⟩
    constructor <;> omega
  · obtain ⟨b₁, h1⟩ : ∃ b₁ : ℤ, 2 * b₁ = B - V := ⟨(B - V) / 2, by omega⟩
    have hn := normIII h1 h2
    have heq' : v₁ ^ 2 + 3 * A ^ 2 + 3 * b₁ ^ 2 = N := by linarith
    refine ⟨v₁, b₁, ⟨by omega, hA0, by omega, by omega, hA1, by omega, mod3_S heq' hN3, heq'⟩, ?_⟩
    rintro ⟨e1, e2⟩
    constructor <;> omega

/-- **Lemma 4.2(a).** A primitive solution of `v² + 3a² + 3b² = N`, `N ≡ 7 (mod 24)`, `N > 7`,
gives a solution in odd positive integers that is not diagonal. -/
theorem seedS {N : ℤ} (hN : N % 24 = 7) (hN7 : 7 < N) {v a b : ℤ}
    (heq : v ^ 2 + 3 * a ^ 2 + 3 * b ^ 2 = N) (hprim : Int.gcd (Int.gcd v a) b = 1) :
    ∃ v' a' b', IsS N v' a' b' ∧ ¬(v' = a' ∧ a' = b') := by
  have hdiv : ∀ k : ℤ, 0 < k → k ∣ v → k ∣ a → k ∣ b → k = 1 := by
    intro k hk h1 h2 h3
    have h12 : k ∣ ((Int.gcd v a : ℕ) : ℤ) := Int.dvd_coe_gcd h1 h2
    have h123 : k ∣ ((Int.gcd (Int.gcd v a) b : ℕ) : ℤ) := Int.dvd_coe_gcd h12 h3
    rw [hprim] at h123
    exact Int.eq_one_of_dvd_one hk.le (by simpa using h123)
  obtain ⟨V, hVd⟩ : ∃ V : ℤ, V = |v| := ⟨_, rfl⟩
  obtain ⟨A, hAd⟩ : ∃ A : ℤ, A = |a| := ⟨_, rfl⟩
  obtain ⟨B, hBd⟩ : ∃ B : ℤ, B = |b| := ⟨_, rfl⟩
  have hV : 0 ≤ V := hVd ▸ abs_nonneg v
  have hA : 0 ≤ A := hAd ▸ abs_nonneg a
  have hB : 0 ≤ B := hBd ▸ abs_nonneg b
  have hdvV : ∀ k : ℤ, k ∣ V → k ∣ v := fun k h => (dvd_abs k v).mp (hVd ▸ h)
  have hdvA : ∀ k : ℤ, k ∣ A → k ∣ a := fun k h => (dvd_abs k a).mp (hAd ▸ h)
  have hdvB : ∀ k : ℤ, k ∣ B → k ∣ b := fun k h => (dvd_abs k b).mp (hBd ▸ h)
  have heq' : V ^ 2 + 3 * A ^ 2 + 3 * B ^ 2 = N := by
    rw [hVd, hAd, hBd, sq_abs, sq_abs, sq_abs]; exact heq
  have hN3 : N % 3 = 1 := by omega
  have pattern : (V % 2 = 1 ∧ A % 2 = 1 ∧ B % 2 = 1) ∨
      (A % 2 = 1 ∧ V % 2 = 0 ∧ B % 2 = 0 ∧ (V + B) % 4 = 2) ∨
      (B % 2 = 1 ∧ V % 2 = 0 ∧ A % 2 = 0 ∧ (V + A) % 4 = 2) := by
    rcases sq_mod8 V with ⟨h1, h1'⟩ | ⟨h1, h1'⟩ | ⟨h1, h1'⟩ <;>
    rcases sq_mod8 A with ⟨h2, h2'⟩ | ⟨h2, h2'⟩ | ⟨h2, h2'⟩ <;>
    rcases sq_mod8 B with ⟨h3, h3'⟩ | ⟨h3, h3'⟩ | ⟨h3, h3'⟩ <;> omega
  rcases pattern with ⟨h1, h2, h3⟩ | ⟨h2, h1, h3, h4⟩ | ⟨h3, h1, h2, h4⟩
  · refine ⟨V, A, B, ⟨by omega, by omega, by omega, h1, h2, h3, mod3_S heq' hN3, heq'⟩, ?_⟩
    rintro ⟨e1, e2⟩
    have hk : V = 1 := hdiv V (by omega) (hdvV V dvd_rfl) (hdvA V ⟨1, by omega⟩)
      (hdvB V ⟨1, by omega⟩)
    have hA1 : A = 1 := by omega
    have hB1 : B = 1 := by omega
    rw [hk, hA1, hB1] at heq'
    norm_num at heq'
    omega
  · obtain ⟨v₁, b₁, hS, hd⟩ := seedS_even hN3 hV hB (by omega : 0 < A) heq' h2 h1 h3 h4
    refine ⟨v₁, A, b₁, hS, ?_⟩
    intro hdiag
    obtain ⟨hB0, hV2⟩ := hd hdiag
    have hk : A = 1 := hdiv A (by omega) (hdvV A ⟨2, by omega⟩) (hdvA A dvd_rfl)
      (hdvB A ⟨0, by omega⟩)
    have hV2' : V = 2 := by omega
    rw [hV2', hk, hB0] at heq'
    norm_num at heq'
    omega
  · have heq'' : V ^ 2 + 3 * B ^ 2 + 3 * A ^ 2 = N := by linarith
    obtain ⟨v₁, a₁, hS, hd⟩ := seedS_even hN3 hV hA (by omega : 0 < B) heq'' h3 h1 h2 h4
    refine ⟨v₁, a₁, B, hS.swap, ?_⟩
    rintro ⟨e1, e2⟩
    obtain ⟨hA0, hV2⟩ := hd ⟨by omega, by omega⟩
    have hk : B = 1 := hdiv B (by omega) (hdvV B ⟨2, by omega⟩) (hdvA B ⟨0, by omega⟩)
      (hdvB B dvd_rfl)
    have hV2' : V = 2 := by omega
    rw [hV2', hk, hA0] at heq'
    norm_num at heq'
    omega

/-- Case 2 of Lemma 4.2(b). -/
theorem seedT_even {N U V W : ℤ} (hN3 : N % 3 = 2) (hU : 0 ≤ U) (hV : 0 ≤ V) (hW0 : 0 < W)
    (heq : 3 * U ^ 2 + V ^ 2 + W ^ 2 = N) (hW1 : W % 2 = 1) (hU0 : U % 2 = 0)
    (hV0 : V % 2 = 0) (h4 : (U + V) % 4 = 2) :
    ∃ u₁ v₁ : ℤ, IsT N u₁ v₁ W ∧ (u₁ = v₁ ∧ v₁ = W → U = 0 ∧ V = 2 * W) := by
  obtain ⟨v₁, h2⟩ : ∃ v₁ : ℤ, 2 * v₁ = 3 * U + V := ⟨(3 * U + V) / 2, by omega⟩
  rcases lt_or_gt_of_ne (show U ≠ V by omega) with hlt | hgt
  · obtain ⟨u₁, h1⟩ : ∃ u₁ : ℤ, 2 * u₁ = V - U := ⟨(V - U) / 2, by omega⟩
    have hn := normIII' h1 h2
    have heq' : 3 * u₁ ^ 2 + v₁ ^ 2 + W ^ 2 = N := by linarith
    have h3 := mod3_T heq' hN3
    refine ⟨u₁, v₁, ⟨by omega, by omega, hW0, by omega, by omega, hW1, h3.1, h3.2, heq'⟩, ?_⟩
    rintro ⟨e1, e2⟩
    constructor <;> omega
  · obtain ⟨u₁, h1⟩ : ∃ u₁ : ℤ, 2 * u₁ = U - V := ⟨(U - V) / 2, by omega⟩
    have hn := normIII h1 h2
    have heq' : 3 * u₁ ^ 2 + v₁ ^ 2 + W ^ 2 = N := by linarith
    have h3 := mod3_T heq' hN3
    refine ⟨u₁, v₁, ⟨by omega, by omega, hW0, by omega, by omega, hW1, h3.1, h3.2, heq'⟩, ?_⟩
    rintro ⟨e1, e2⟩
    constructor <;> omega

/-- **Lemma 4.2(b).** A primitive solution of `3u² + v² + w² = N`, `N ≡ 5 (mod 24)`, `N > 5`,
gives a solution in odd positive integers that is not diagonal. -/
theorem seedT {N : ℤ} (hN : N % 24 = 5) (hN5 : 5 < N) {u v w : ℤ}
    (heq : 3 * u ^ 2 + v ^ 2 + w ^ 2 = N) (hprim : Int.gcd (Int.gcd u v) w = 1) :
    ∃ u' v' w', IsT N u' v' w' ∧ ¬(u' = v' ∧ v' = w') := by
  have hdiv : ∀ k : ℤ, 0 < k → k ∣ u → k ∣ v → k ∣ w → k = 1 := by
    intro k hk h1 h2 h3
    have h12 : k ∣ ((Int.gcd u v : ℕ) : ℤ) := Int.dvd_coe_gcd h1 h2
    have h123 : k ∣ ((Int.gcd (Int.gcd u v) w : ℕ) : ℤ) := Int.dvd_coe_gcd h12 h3
    rw [hprim] at h123
    exact Int.eq_one_of_dvd_one hk.le (by simpa using h123)
  obtain ⟨U, hUd⟩ : ∃ U : ℤ, U = |u| := ⟨_, rfl⟩
  obtain ⟨V, hVd⟩ : ∃ V : ℤ, V = |v| := ⟨_, rfl⟩
  obtain ⟨W, hWd⟩ : ∃ W : ℤ, W = |w| := ⟨_, rfl⟩
  have hU : 0 ≤ U := hUd ▸ abs_nonneg u
  have hV : 0 ≤ V := hVd ▸ abs_nonneg v
  have hW : 0 ≤ W := hWd ▸ abs_nonneg w
  have hdvU : ∀ k : ℤ, k ∣ U → k ∣ u := fun k h => (dvd_abs k u).mp (hUd ▸ h)
  have hdvV : ∀ k : ℤ, k ∣ V → k ∣ v := fun k h => (dvd_abs k v).mp (hVd ▸ h)
  have hdvW : ∀ k : ℤ, k ∣ W → k ∣ w := fun k h => (dvd_abs k w).mp (hWd ▸ h)
  have heq' : 3 * U ^ 2 + V ^ 2 + W ^ 2 = N := by
    rw [hUd, hVd, hWd, sq_abs, sq_abs, sq_abs]; exact heq
  have hN3 : N % 3 = 2 := by omega
  have pattern : (U % 2 = 1 ∧ V % 2 = 1 ∧ W % 2 = 1) ∨
      (W % 2 = 1 ∧ U % 2 = 0 ∧ V % 2 = 0 ∧ (U + V) % 4 = 2) ∨
      (V % 2 = 1 ∧ U % 2 = 0 ∧ W % 2 = 0 ∧ (U + W) % 4 = 2) := by
    rcases sq_mod8 U with ⟨h1, h1'⟩ | ⟨h1, h1'⟩ | ⟨h1, h1'⟩ <;>
    rcases sq_mod8 V with ⟨h2, h2'⟩ | ⟨h2, h2'⟩ | ⟨h2, h2'⟩ <;>
    rcases sq_mod8 W with ⟨h3, h3'⟩ | ⟨h3, h3'⟩ | ⟨h3, h3'⟩ <;> omega
  rcases pattern with ⟨h1, h2, h3⟩ | ⟨h3, h1, h2, h4⟩ | ⟨h2, h1, h3, h4⟩
  · have hm := mod3_T heq' hN3
    refine ⟨U, V, W, ⟨by omega, by omega, by omega, h1, h2, h3, hm.1, hm.2, heq'⟩, ?_⟩
    rintro ⟨e1, e2⟩
    have hk : U = 1 := hdiv U (by omega) (hdvU U dvd_rfl) (hdvV U ⟨1, by omega⟩)
      (hdvW U ⟨1, by omega⟩)
    have hV1 : V = 1 := by omega
    have hW1 : W = 1 := by omega
    rw [hk, hV1, hW1] at heq'
    norm_num at heq'
    omega
  · obtain ⟨u₁, v₁, hT, hd⟩ := seedT_even hN3 hU hV (by omega : 0 < W) heq' h3 h1 h2 h4
    refine ⟨u₁, v₁, W, hT, ?_⟩
    intro hdiag
    obtain ⟨hU0, hV2⟩ := hd hdiag
    have hk : W = 1 := hdiv W (by omega) (hdvU W ⟨0, by omega⟩) (hdvV W ⟨2, by omega⟩)
      (hdvW W dvd_rfl)
    have hV2' : V = 2 := by omega
    rw [hU0, hV2', hk] at heq'
    norm_num at heq'
    omega
  · have heq'' : 3 * U ^ 2 + W ^ 2 + V ^ 2 = N := by linarith
    obtain ⟨u₁, w₁, hT, hd⟩ := seedT_even hN3 hU hW (by omega : 0 < V) heq'' h2 h1 h3 h4
    refine ⟨u₁, V, w₁, hT.swap, ?_⟩
    rintro ⟨e1, e2⟩
    obtain ⟨hU0, hW2⟩ := hd ⟨by omega, by omega⟩
    have hk : V = 1 := hdiv V (by omega) (hdvU V ⟨0, by omega⟩) (hdvV V dvd_rfl)
      (hdvW V ⟨2, by omega⟩)
    have hW2' : W = 2 := by omega
    rw [hU0, hk, hW2'] at heq'
    norm_num at heq'
    omega

/-! ## The classical input (Proposition 4.1), as hypotheses -/

/-- Proposition 4.1(a): every `N ≡ 7 (mod 24)` is primitively represented by
`v² + 3a² + 3b²`. This follows from the classical theory of genera; it is not proved here. -/
def PrimRep133 : Prop :=
  ∀ N : ℤ, 0 < N → N % 24 = 7 →
    ∃ v a b : ℤ, v ^ 2 + 3 * a ^ 2 + 3 * b ^ 2 = N ∧ Int.gcd (Int.gcd v a) b = 1

/-- Proposition 4.1(b): every `N ≡ 5 (mod 24)` is primitively represented by
`3u² + v² + w²`. This follows from the classical theory of genera; it is not proved here. -/
def PrimRep113 : Prop :=
  ∀ N : ℤ, 0 < N → N % 24 = 5 →
    ∃ u v w : ℤ, 3 * u ^ 2 + v ^ 2 + w ^ 2 = N ∧ Int.gcd (Int.gcd u v) w = 1

/-- For `N ≡ 7 (mod 24)`, `N > 7`, both residues of `v` mod 3 occur. -/
theorem exists_S_residue (hP : PrimRep133) {N : ℤ} (hN : N % 24 = 7) (hN7 : 7 < N) (c : ℤ)
    (hc : c = 1 ∨ c = 2) : ∃ v a b, IsS N v a b ∧ v % 3 = c := by
  obtain ⟨v, a, b, heq, hprim⟩ := hP N (by omega) hN
  obtain ⟨v', a', b', hS, hnd⟩ := seedS hN hN7 heq hprim
  by_cases hv : v' % 3 = c
  · exact ⟨v', a', b', hS, hv⟩
  · obtain ⟨v'', a'', b'', hS', hne⟩ := exists_other_residue hS hnd
    refine ⟨v'', a'', b'', hS', ?_⟩
    have h1 := hS.2.2.2.2.2.2.1
    have h2 := hS'.2.2.2.2.2.2.1
    omega

/-- For `N ≡ 5 (mod 24)`, `N > 5`, there is a solution with `v ≡ 2`, `w ≡ 1 (mod 3)`. -/
theorem exists_T_mixed (hP : PrimRep113) {N : ℤ} (hN : N % 24 = 5) (hN5 : 5 < N) :
    ∃ u v w, IsT N u v w ∧ v % 3 = 2 ∧ w % 3 = 1 := by
  obtain ⟨u, v, w, heq, hprim⟩ := hP N (by omega) hN
  obtain ⟨u', v', w', hT, hnd⟩ := seedT hN hN5 heq hprim
  obtain ⟨u'', v'', w'', hT', hne⟩ := exists_mixed hT hnd
  have h1 := hT'.2.2.2.2.2.2.1
  have h2 := hT'.2.2.2.2.2.2.2.1
  by_cases hv : v'' % 3 = 2
  · exact ⟨u'', v'', w'', hT', hv, by omega⟩
  · exact ⟨u'', w'', v'', hT'.swap, by omega, by omega⟩

/-! ## From solutions to representations (Lemma 5.1) -/

theorem even_pent (z : ℕ) : Even (z * (3 * z - 1)) := by
  rcases Nat.even_or_odd z with h | h
  · exact Nat.even_mul.mpr (Or.inl h)
  · refine Nat.even_mul.mpr (Or.inr ?_)
    obtain ⟨k, rfl⟩ := h
    exact ⟨3 * k + 1, by omega⟩

theorem even_pent' (z : ℕ) : Even (z * (3 * z + 1)) := by
  rcases Nat.even_or_odd z with h | h
  · exact Nat.even_mul.mpr (Or.inl h)
  · refine Nat.even_mul.mpr (Or.inr ?_)
    obtain ⟨k, rfl⟩ := h
    exact ⟨3 * k + 2, by omega⟩

theorem repr_class2 (n : ℕ) {v a b : ℤ} (h : IsS (24 * n + 7) v a b) (hv : v % 3 = 2) :
    ∃ x y z : ℕ, 1 ≤ z ∧ n = x * (x + 1) / 2 + y * (y + 1) / 2 + z * (3 * z - 1) / 2 := by
  obtain ⟨hv0, ha0, hb0, hv2, ha2, hb2, -, heq⟩ := h
  obtain ⟨x, hx⟩ : ∃ x : ℕ, a = 2 * x + 1 := ⟨((a - 1) / 2).toNat, by omega⟩
  obtain ⟨y, hy⟩ : ∃ y : ℕ, b = 2 * y + 1 := ⟨((b - 1) / 2).toNat, by omega⟩
  obtain ⟨z, hz⟩ : ∃ z : ℕ, v = 6 * z - 1 := ⟨((v + 1) / 6).toNat, by omega⟩
  have hz1 : 1 ≤ z := by omega
  subst hx hy hz
  have h24 : (24 : ℤ) * n = 12 * (x * (x + 1)) + 12 * (y * (y + 1)) + 12 * (z * (3 * z - 1)) := by
    linear_combination (-1 : ℤ) * heq
  have hN : 2 * n = x * (x + 1) + y * (y + 1) + z * (3 * z - 1) := by
    zify [show 1 ≤ 3 * z by omega]
    linarith
  obtain ⟨X, hX⟩ := Nat.even_mul_succ_self x
  obtain ⟨Y, hY⟩ := Nat.even_mul_succ_self y
  obtain ⟨Z, hZ⟩ := even_pent z
  refine ⟨x, y, z, hz1, ?_⟩
  rw [hX, hY, hZ] at hN ⊢
  omega

theorem repr_class1 (n : ℕ) {v a b : ℤ} (h : IsS (24 * n + 7) v a b) (hv : v % 3 = 1) :
    ∃ x y z : ℕ, n = x * (x + 1) / 2 + y * (y + 1) / 2 + z * (3 * z + 1) / 2 := by
  obtain ⟨hv0, ha0, hb0, hv2, ha2, hb2, -, heq⟩ := h
  obtain ⟨x, hx⟩ : ∃ x : ℕ, a = 2 * x + 1 := ⟨((a - 1) / 2).toNat, by omega⟩
  obtain ⟨y, hy⟩ : ∃ y : ℕ, b = 2 * y + 1 := ⟨((b - 1) / 2).toNat, by omega⟩
  obtain ⟨z, hz⟩ : ∃ z : ℕ, v = 6 * z + 1 := ⟨((v - 1) / 6).toNat, by omega⟩
  subst hx hy hz
  have h24 : (24 : ℤ) * n = 12 * (x * (x + 1)) + 12 * (y * (y + 1)) + 12 * (z * (3 * z + 1)) := by
    linear_combination (-1 : ℤ) * heq
  have hN : 2 * n = x * (x + 1) + y * (y + 1) + z * (3 * z + 1) := by
    zify
    linarith
  obtain ⟨X, hX⟩ := Nat.even_mul_succ_self x
  obtain ⟨Y, hY⟩ := Nat.even_mul_succ_self y
  obtain ⟨Z, hZ⟩ := even_pent' z
  refine ⟨x, y, z, ?_⟩
  rw [hX, hY, hZ] at hN ⊢
  omega

theorem repr_mixed (n : ℕ) {u v w : ℤ} (h : IsT (24 * n + 5) u v w) (hv : v % 3 = 2)
    (hw : w % 3 = 1) :
    ∃ x y z : ℕ, 1 ≤ y ∧ n = x * (x + 1) / 2 + y * (3 * y - 1) / 2 + z * (3 * z + 1) / 2 := by
  obtain ⟨hu0, hv0, hw0, hu2, hv2, hw2, -, -, heq⟩ := h
  obtain ⟨x, hx⟩ : ∃ x : ℕ, u = 2 * x + 1 := ⟨((u - 1) / 2).toNat, by omega⟩
  obtain ⟨y, hy⟩ : ∃ y : ℕ, v = 6 * y - 1 := ⟨((v + 1) / 6).toNat, by omega⟩
  obtain ⟨z, hz⟩ : ∃ z : ℕ, w = 6 * z + 1 := ⟨((w - 1) / 6).toNat, by omega⟩
  have hy1 : 1 ≤ y := by omega
  subst hx hy hz
  have h24 : (24 : ℤ) * n = 12 * (x * (x + 1)) + 12 * (y * (3 * y - 1)) + 12 * (z * (3 * z + 1)) := by
    linear_combination (-1 : ℤ) * heq
  have hN : 2 * n = x * (x + 1) + y * (3 * y - 1) + z * (3 * z + 1) := by
    zify [show 1 ≤ 3 * y by omega]
    linarith
  obtain ⟨X, hX⟩ := Nat.even_mul_succ_self x
  obtain ⟨Y, hY⟩ := even_pent y
  obtain ⟨Z, hZ⟩ := even_pent' z
  refine ⟨x, y, z, hy1, ?_⟩
  rw [hX, hY, hZ] at hN ⊢
  omega

/-! ## Main theorems -/

/-- **Theorem 1.1.** Every natural number is a sum of two triangular numbers and a pentagonal
number, `n = x(x+1)/2 + y(y+1)/2 + z(3z-1)/2` with `x y z : ℕ`; if `n ≥ 1` one can take `z ≥ 1`. -/
theorem two_triangular_pentagonal (hP : PrimRep133) (n : ℕ) :
    ∃ x y z : ℕ, n = x * (x + 1) / 2 + y * (y + 1) / 2 + z * (3 * z - 1) / 2 ∧
      (1 ≤ n → 1 ≤ z) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨0, 0, 0, by norm_num, by omega⟩
  · obtain ⟨v, a, b, hS, hv⟩ :=
      exists_S_residue hP (N := 24 * n + 7) (by omega) (by omega) 2 (Or.inr rfl)
    obtain ⟨x, y, z, hz, h⟩ := repr_class2 n hS hv
    exact ⟨x, y, z, h, fun _ => hz⟩

/-- Every natural number is `x(x+1)/2 + y(y+1)/2 + z(3z+1)/2` with `x y z : ℕ`
(the tuple `(3,1,1,1,1,1)`). -/
theorem two_triangular_second_pentagonal (hP : PrimRep133) (n : ℕ) :
    ∃ x y z : ℕ, n = x * (x + 1) / 2 + y * (y + 1) / 2 + z * (3 * z + 1) / 2 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨0, 0, 0, by norm_num⟩
  · obtain ⟨v, a, b, hS, hv⟩ :=
      exists_S_residue hP (N := 24 * n + 7) (by omega) (by omega) 1 (Or.inl rfl)
    exact repr_class1 n hS hv

/-- **Theorem 1.4.** Every natural number is `x(x+1)/2 + y(3y-1)/2 + z(3z+1)/2` with
`x y z : ℕ`; if `n ≥ 1` one can take `y ≥ 1`. -/
theorem triangular_two_pentagonal_mixed (hP : PrimRep113) (n : ℕ) :
    ∃ x y z : ℕ, n = x * (x + 1) / 2 + y * (3 * y - 1) / 2 + z * (3 * z + 1) / 2 ∧
      (1 ≤ n → 1 ≤ y) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨0, 0, 0, by norm_num, by omega⟩
  · obtain ⟨u, v, w, hT, hv, hw⟩ := exists_T_mixed hP (N := 24 * n + 5) (by omega) (by omega)
    obtain ⟨x, y, z, hy, h⟩ := repr_mixed n hT hv hw
    exact ⟨x, y, z, h, fun _ => hy⟩

end TriPent

#print axioms TriPent.exists_other_residue
#print axioms TriPent.exists_mixed
#print axioms TriPent.two_triangular_pentagonal
#print axioms TriPent.two_triangular_second_pentagonal
#print axioms TriPent.triangular_two_pentagonal_mixed
