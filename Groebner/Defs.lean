import Mathlib
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.MvPolynomial.MonomialOrder
import Mathlib.RingTheory.Ideal.Span
import Groebner.SimpIntro

namespace MonomialOrder

open MvPolynomial
variable {σ : Type*} (m : MonomialOrder σ)

section CommSemiring
variable {R : Type*} [CommSemiring R]

/--
a \in Partially Ordered Set, a \geq 0
-/
@[simp]
lemma zero_le (a : m.syn) : 0 ≤ a := bot_le

/--
Given a nonzero polynomial \( f \in k[x] \), let
  \[
  f = c_0 x^m + c_1 x^{m-1} + \cdots + c_m,
  \]
  where \( c_i \in k \) and \( c_0 \neq 0 \) [thus, \( m = \deg(f) \)]. Then we say that \( c_0 x^m \) is the \textbf{leading term} of \( f \), written
  \[
  \operatorname{LT}(f) = c_0 x^m.
  \]
--/
noncomputable def leadingTerm (f : MvPolynomial σ R) : MvPolynomial σ R :=
  monomial (m.degree f) (m.leadingCoeff f)

/--
Fix a monomial order \(>\) on \(\mathbb{Z}_{\geq 0}^n\), and let
  \(F = (f_1, \ldots, f_s)\) be an ordered \(s\)-tuple of polynomials in \(k[x_1, \ldots, x_n]\).
  Then every \(f \in k[x_1, \ldots, x_n]\) can be written as
  \[
  f = a_1 f_1 + \cdots + a_s f_s + r,
  \]
  where \(a_i, r \in k[x_1, \ldots, x_n]\), and either \(r = 0\) or \(r\) is a linear combination, with coefficients in \(k\), of monomials, none of which is divisible by any of \(\mathrm{LT}(f_1), \ldots, \mathrm{LT}(f_s)\).
  We will call \(r\) a \textbf{remainder} of \(f\) on division by \(F\).
--/
def IsRemainder (p : MvPolynomial σ R) (G'' : Set (MvPolynomial σ R)) (r : MvPolynomial σ R)
  := ∃ (g : G'' →₀ (MvPolynomial σ R)),
      p = Finsupp.linearCombination _ (fun (g' : G'') ↦ (g' : MvPolynomial σ R)) g + r ∧
      (∀ (g' : G''), m.degree ((g' : MvPolynomial σ R) * (g g')) ≼[m] m.degree p) ∧
      (∀ c ∈ r.support, ∀ g' ∈ G'', g' ≠ 0 → ¬ (m.degree g' ≤ c))

open Classical

-- it may free you from coercion between different kinds of "sets",
-- "finite subsets", "finite subsets" of "sets", ...,
-- when you are dealing with different G''

/--
Let $p \in R[\mathbf{X}]$, $G'' \subseteq R[\mathbf{X}]$ be a set of polynomials,
  and $r \in R[\mathbf{X}]$. Then $r$ is a remainder of $p$ modulo $G''$ with respect to
  monomial order $m$ if and only if there exists a finite linear combination from $G''$
  such that:
  \begin{enumerate}
    \item The support of the combination is contained in $G''$
    \item $p$ decomposes as the sum of this combination and $r$
    \item For each $g' \in G''$, the degree of $g' \cdot (coefficient\ of\ g')$
          is bounded by $\deg_m(p)$
    \item No term of $r$ is divisible by any leading term of non-zero elements in $G''$
  \end{enumerate}
--/
lemma IsRemainder_def' (p : MvPolynomial σ R) (G'' : Set (MvPolynomial σ R)) (r : MvPolynomial σ R)
  : m.IsRemainder p G'' r ↔ ∃ (g : (MvPolynomial σ R) →₀ (MvPolynomial σ R)),
      ↑g.support ⊆ G'' ∧
      p = Finsupp.linearCombination _ id g + r ∧
      (∀ g' ∈ G'', m.degree ((g' : MvPolynomial σ R) * (g g')) ≼[m] m.degree p) ∧
      (∀ c ∈ r.support, ∀ g' ∈ G'', g' ≠ 0 → ¬ (m.degree g' ≤ c)) := by
  -- probably many tech details
  -- (technologically but not mathematically) normal or hard
  unfold IsRemainder
  constructor
  ·
    intro ⟨g, h₁, h₂, h₃⟩
    use {
      support := g.support,
      toFun := fun x => if hx : x ∈ G'' then g.toFun (⟨x, hx⟩) else 0,
      mem_support_toFun := by intro; simp; rfl
    }
    split_ands
    · simp
    · simp [h₁]
      congr 1
      simp [Finsupp.linearCombination_apply, Finsupp.sum]
      rfl
    · simp_intro' g' hg'
      convert h₂ ⟨g', hg'⟩
    · exact h₃
  ·
    intro ⟨g, hg, h₁, h₂, h₃⟩
    use {
      support := g.support.filterMap
        (fun x => if hx : x ∈ G'' then some (⟨x, hx⟩ : ↑G'') else none)
        (by simp_intro' ..),
      toFun := (g.toFun ·),
      mem_support_toFun := by intro; simp; rfl
    }
    split_ands
    · rw [h₁, eq_comm]
      congr 1
      simp [Finsupp.linearCombination_apply, Finsupp.sum]
      apply Finset.sum_nbij (↑·)
      · simp_intro' ..
      ·  -- if I use `simp_intro' x _ a _ h`, then how to deal with coe?
        intro q
        simp
        intro _ _ _ _ hqs
        simp [←hqs]
      · simp_intro' q hq
        exact Set.mem_of_subset_of_mem hg <| Finsupp.mem_support_iff.mpr hq
      · simp [DFunLike.coe]
    · simp
      exact h₂
    · exact h₃

/--
Let \( p, r \in k[x_i : i \in \sigma] \), and let \( G' \subseteq k[x_i : i \in \sigma] \) be a finite set.
We say that \( r \) is a \emph{generalized remainder} of \( p \) upon division by \( G' \) if the following two conditions hold:

\begin{enumerate}
  \item For every nonzero \( g \in G' \) and every monomial \( x^s \in \operatorname{supp}(r) \),
        there exists some component \( j \in \sigma \) such that
        \[
        \operatorname{multideg}(g)_j > s_j.
        \]
  \item There exists a function \( q : G' \to k[x_i : i \in \sigma] \) such that:
  \begin{itemize}
    \item For every \( g \in G' \),
          \[
          \operatorname{multideg}''(q(g)g) \leq \operatorname{multideg}''(p);
          \]
    \item The decomposition holds:
          \[
          p = \sum_{g \in G'} q(g)g + r.
          \]
  \end{itemize}
\end{enumerate}
-/
lemma IsRemainder_def'' (p : MvPolynomial σ R) (G'' : Set (MvPolynomial σ R)) (r : MvPolynomial σ R)
  : m.IsRemainder p G'' r ↔
  ∃ (g : (MvPolynomial σ R) → (MvPolynomial σ R))(G' : Finset (MvPolynomial σ R)),
      ↑G' ⊆ G'' ∧
      p = G'.sum (fun x => g x * x) + r ∧
      (∀ g' ∈ G', m.degree ((g' : MvPolynomial σ R) * (g g')) ≼[m] m.degree p) ∧
      (∀ c ∈ r.support, ∀ g' ∈ G'', g' ≠ 0 → ¬ (m.degree g' ≤ c)) := by
  rw [IsRemainder_def']
  constructor
  · intro ⟨g, h₁, h₂, h₃, h₄⟩
    use g.toFun, g.support
    refine ⟨h₁, by rwa [Finsupp.linearCombination_apply, Finsupp.sum] at h₂, ?_, h₄⟩
    intro g' hg'
    exact h₃ g' (Set.mem_of_mem_of_subset hg' h₁)
  · intro ⟨g, G', h₁, h₂, h₃, h₄⟩
    use Finsupp.onFinset G' (fun x => if x ∈ G' then g x else 0) (by simp; intro _ ha _; exact ha)
    split_ands
    · simp_intro' x hx
      exact Set.mem_of_mem_of_subset hx.1 h₁
    · rw [Finsupp.linearCombination_apply, Finsupp.sum, h₂, Finsupp.support_onFinset]
      congr 1
      simp
      have h : G' = ({a ∈ G' | a ∈ G' ∧ ¬g a = 0} ∩ G') ∪ ({a ∈ G' | g a = 0}) := by
        apply subset_antisymm
        · simp_intro' x hx [em']
        · simp_intro' x
          rintro (⟨_, hx⟩ | ⟨hx,_⟩) <;> exact hx
      have h' : Disjoint ({a ∈ G' | a ∈ G' ∧ ¬g a = 0} ∩ G')  ({a ∈ G' | g a = 0}) := by
        unfold Disjoint
        simp_intro' s hs hs'
        by_contra h
        obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr h
        have hs := Finset.mem_of_subset hs hx
        have hs' := Finset.mem_of_subset hs' hx
        simp at hs hs'
        exact hs.1.2 hs'.2
      nth_rewrite 1 [h]
      rw [Finset.sum_union h']
      convert add_zero _
      convert Finset.sum_const_zero
      expose_names
      simp at h_1
      simp [h_1.2]
    ·
      intro g'' hg''
      by_cases hg''G' : g'' ∈ G'
      · simp [hg''G', h₃]
      · simp [hg''G']
    · exact h₄

/--
Let $p \in R[\mathbf{X}]$ be a multivariate polynomial. Then the leading term of $p$
  vanishes with respect to monomial order $m$ if and only if $p$ is the zero polynomial:
  \[
    \LT_m(p) = 0 \iff p = 0
  \]
--/
lemma lm_eq_zero_iff (p : MvPolynomial σ R): m.leadingTerm p = 0 ↔ p = 0 := by
  simp only [leadingTerm, monomial_eq_zero, leadingCoeff_eq_zero_iff]

/--
For any set of polynomials $G'' \subseteq R[\mathbf{X}]$ and monomial order $m$,
  the image of leading terms on the nonzero elements of $G''$ equals the image on all
  elements minus zero:
  \[
    \LT_m(G'' \setminus \{0\}) = \LT_m(G'') \setminus \{0\}
  \]
-/
lemma leadingTerm_image_sdiff_singleton_zero (G'' : Set (MvPolynomial σ R)) :
  m.leadingTerm '' (G''\ {0}) = (m.leadingTerm '' G'') \ {0} := by
  apply subset_antisymm
  · intro p
    simp
    intro q hq hq' hpq
    exact ⟨⟨q, hq, hpq⟩, hpq ▸ (m.lm_eq_zero_iff _).not.mpr hq'⟩
  · intro p
    simp
    intro q hq hpq hp
    rw [←hpq, MonomialOrder.lm_eq_zero_iff] at hp
    exact ⟨q, ⟨hq, hp⟩, hpq⟩

/--
Let $p \in R[\mathbf{X}]$ be a polynomial, $G'' \subseteq R[\mathbf{X}]$ a set of polynomials,
  and $r \in R[\mathbf{X}]$ a remainder. Then the remainder property is invariant under
  inserting the zero polynomial:
  \[
    \mathsf{IsRemainder}_m\,p\,(G'' \cup \{0\})\,r \iff \mathsf{IsRemainder}_m\,p\,G''\,r
  \]
-/
lemma isRemainder_of_insert_zero_iff_isRemainder (p : MvPolynomial σ R)
  (G'' : Set (MvPolynomial σ R)) (r : MvPolynomial σ R) :
  m.IsRemainder p (insert 0 G'') r ↔ m.IsRemainder p G'' r := by
  constructor
  ·
    by_cases hG'' : 0 ∈ G''; simp only [Set.insert_eq_of_mem hG'', imp_self]
    rw [IsRemainder_def'', IsRemainder_def'']
    intro ⟨g, G', hG', h₁, h₂, h₃⟩
    use g, (G'.erase 0)
    split_ands
    · simp [hG']
    ·
      rw [h₁]
      congr 1
      by_cases hG'0 : 0 ∈ G'
      ·
        nth_rw 1 [← Finset.insert_erase hG'0]
        rw [Finset.sum_insert_zero (a:=0)]
        simp
      ·
        rw [Finset.erase_eq_self.mpr hG'0]

    ·
      intro g' hg'
      simp at hg'
      exact h₂ g' hg'.2
    ·
      intro n hn g' hg'G' hg'
      exact h₃ n hn g' (by simp [hg'G']) hg'
  ·
    rw [IsRemainder_def', IsRemainder_def']
    intro ⟨g, hg, h₁, h₂, h₃⟩
    use g
    split_ands
    · exact subset_trans hg (Set.subset_insert _ _)
    · exact h₁
    · intro g' hg'
      by_cases hg'₁ : g' = 0
      · simp only [hg'₁, zero_mul, degree_zero, map_zero, zero_le]
      · exact h₂ g' ((Set.mem_insert_iff.mp hg').resolve_left hg'₁)
    ·
      intro c hc g' hg' hg'₁
      exact h₃ c hc g' ((Set.mem_insert_iff.mp hg').resolve_left hg'₁) hg'₁

/--
  Let $p \in R[\mathbf{X}]$ be a polynomial, $G'' \subseteq R[\mathbf{X}]$ a set of polynomials,
  and $r \in R[\mathbf{X}]$ a remainder. Then the remainder property is invariant under
  removal of the zero polynomial:
  \[
    \mathsf{IsRemainder}_m\,p\,(G'' \setminus \{0\})\,r \iff \mathsf{IsRemainder}_m\,p\,G''\,r
  \]
-/
lemma isRemainder_of_singleton_zero_iff_isRemainder (p : MvPolynomial σ R)
  (G'' : Set (MvPolynomial σ R)) (r : MvPolynomial σ R) :
  m.IsRemainder p (G'' \ {0}) r ↔ m.IsRemainder p G'' r := by
  -- tips: refer to the proof of `Submodule.span_sdiff_singleton_zero` in `Submodule.lean`,
  -- and use `isRemainder_of_insert_zero_iff_isRemainder`.
  by_cases h : 0 ∈ G''
  · rw[←isRemainder_of_insert_zero_iff_isRemainder,
        (by simp [h] : insert 0 (G'' \ {0}) = G'')]
  · have h' : G'' \ {0} = G'' := by
      ext x
      simp [h]
    rw [h']

end CommSemiring

section CommRing
open Classical
variable {R : Type*} [CommRing R] {s : σ →₀ ℕ}


/--
The $S$-polynomial of $f$ and $g$ is the combination
  \[
  S(f, g) = \frac{x^\gamma}{\mathrm{LT}(f)} \cdot f - \frac{x^\gamma}{\mathrm{LT}(g)} \cdot g.
  \]
--/
noncomputable def sPolynomial (f g : MvPolynomial σ R) : MvPolynomial σ R :=
  monomial (m.degree g - m.degree f) (m.leadingCoeff g) * f -
  monomial (m.degree f - m.degree g) (m.leadingCoeff f) * g


/--
Fix a monomial order on the polynomial ring $k[x_1, \ldots, x_n]$.A finite subset $G = \{g_1, \ldots, g_t\}$ of an ideal $I \subseteq k[x_1, \ldots, x_n]$, with $I \ne \{0\}$, is said to be a \textbf{Gröbner basis} (or standard basis) if
  \[
  \langle \operatorname{LT}(g_1), \ldots, \operatorname{LT}(g_t) \rangle = \langle \operatorname{LT}(I) \rangle.
  \]
  Using the convention that $\langle \emptyset \rangle = \{0\}$, we define the empty set $\emptyset$ to be the Gröbner basis of the zero ideal $\{0\}$.
--/
def IsGroebnerBasis (G': Finset (MvPolynomial σ R)) (I : Ideal (MvPolynomial σ R)) :=
  G'.toSet ⊆ I ∧
  Ideal.span (m.leadingTerm '' ↑I)
    = Ideal.span (m.leadingTerm '' G'.toSet)

/--
the S-polynomial of $f$ and $g$ is antisymmetric:
  \[
    \Sph{f}{g} = -\Sph{g}{f}
  \]
--/
lemma sPolynomial_antisymm (f g : MvPolynomial σ R) :
   m.sPolynomial f g = - m.sPolynomial g f := by
   unfold sPolynomial
   exact
     Eq.symm
       (neg_sub ((monomial (m.degree f - m.degree g)) (m.leadingCoeff f) * g)
         ((monomial (m.degree g - m.degree f)) (m.leadingCoeff g) * f))

/--
  For any polynomial $g \in \MvPolynomial{\sigma}{R}$ and monomial order $m$,
  the S-polynomial with zero as first argument vanishes:
  \[
    \Sph{0}{g} = 0
  \]
--/
lemma sPolynomial_eq_zero_of_left_eq_zero (g : MvPolynomial σ R) :
  m.sPolynomial 0 g = 0 := by
  unfold sPolynomial
  simp only [zero_mul, sub_zero, leadingCoeff_zero, monomial_zero]
  exact CommMonoidWithZero.mul_zero ((monomial (m.degree g - m.degree 0)) (m.leadingCoeff g))

/--
  For any polynomial $g \in \MvPolynomial{\sigma}{R}$ and monomial order $m$,
  the S-polynomial with zero as second argument vanishes:
  \[
    \Sph{f}{0} = 0
  \]
--/
lemma sPolynomial_eq_zero_of_right_eq_zero' (f : MvPolynomial σ R) :
  m.sPolynomial f 0 = 0 := by
  rw [sPolynomial_antisymm, sPolynomial_eq_zero_of_left_eq_zero, neg_zero]

/--
  Let $G'' \subseteq R[\mathbf{X}]$ be a set of polynomials where every nonzero element has a unit leading coefficient:
  \[
    \forall g \in G'',\ \big(\mathrm{IsUnit}(\LC_m(g)) \lor g = 0\big)
  \]
  Then for any polynomial $p \in R[\mathbf{X}]$, there exists a remainder $r$ satisfying:
  \[
    \mathsf{IsRemainder}_m\,p\,G''\,r
  \]
  where $\LC_m(g)$ denotes the leading coefficient of $g$ under monomial order $m$.
--/
theorem div_set' {G'' : Set (MvPolynomial σ R)}
    (hG : ∀ g ∈ G'', (IsUnit (m.leadingCoeff g) ∨ g = 0)) (p : MvPolynomial σ R) :
    ∃ (r : MvPolynomial σ R), m.IsRemainder p G'' r := by
  -- tips: use `isRemainder_of_singleton_zero_iff_isRemainder` and `MonomialOrder.div_set`
  let G := G'' \ {0}

  have hG' : ∀ g ∈ G, IsUnit (m.leadingCoeff g) := by
    intro g hg
    obtain ⟨hg₁, hg₂⟩ := hg  -- hg₁: g ∈ G'', hg₂: g ≠ 0
    obtain (h1 | h2) := hG g hg₁
    · exact h1
    · contradiction
  obtain ⟨g, r, h⟩ := MonomialOrder.div_set hG' p
  exists r
  refine (isRemainder_of_singleton_zero_iff_isRemainder m p G'' r).mp ?_
  rcases h with ⟨h₁, h₂, h₃⟩
  simp at *
  unfold IsRemainder
  use g
  split_ands
  · exact h₁
  · exact fun g' ↦ h₂ (↑g') g'.property
  · intro c hc g hg g_neq0
    have hg' : g ∈ G := by
      obtain ⟨hg₁, hg₂⟩ := hg
      exact ⟨hg₁, hg₂⟩
    have hc': ¬coeff c r = 0 := by
      exact mem_support_iff.mp hc
    have h₃_applied := h₃ c hc'
    have h₃_g := h₃_applied g hg'
    exact h₃_g
end CommRing

section Field

/--
Let \( k \) be a field, and let \( G'' \subseteq k[x_i : i \in \sigma] \) be a set of polynomials.
Then for any \( p \in k[x_i : i \in \sigma] \), there exists a generalized remainder \( r \) of \( p \) upon division by \( G'' \).
-/
theorem div_set'' {k : Type*} [Field k] {G'' : Set (MvPolynomial σ k)}
    (p : MvPolynomial σ k) :
    ∃ (r : MvPolynomial σ k), m.IsRemainder p G'' r := by
  apply div_set'
  simp [em']


end Field
