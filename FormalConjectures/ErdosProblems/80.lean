/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import FormalConjectures.Util.ProblemImports

/-!
# Erdős Problem 80
*Reference:*
- [erdosproblems.com/80](https://www.erdosproblems.com/80)
- [erdosproblems.com/600](https://www.erdosproblems.com/600)
- [erdosproblems.com/905](https://www.erdosproblems.com/905)
- [Er87] Erdős, P., _Some problems on finite and infinite graphs_. Logic and combinatorics (Arcata, Calif., 1985) (1987), 223-228.
- [KhNi79] Khadzhiivanov, N. G. and Nikiforov, S. V., _Solution of a problem of {P}. Erdős about the maximum number of triangles with a common edge in a graph_. C. R. Acad. Bulgare Sci. (1979), 1315--1318.
- [FoLo12] Fox, Jacob and Loh, Po-Shen, _On a problem of Erdős and {R}othschild on edges in triangles_. Combinatorica (2012), 619--628.
-/

open Classical Filter

namespace Erdos80

/--
The set of triangles of a graph $G$ containing a given edge $uv$.
-/
private noncomputable def trianglesContaining
  {α : Type*}
  (G : SimpleGraph α)
  (uv : Sym2 α)
  [Fintype α] :
  Finset (Finset α) :=
  (G.cliqueFinset 3).filter (fun t ↦ uv.toFinset ⊆ t)

/--
Let $c>0$ and let $f_c(n)$ be the maximal $m$ such that every graph $G$ with $n$ vertices and
at least $cn^2$ edges, where each edge is contained in at least one triangle, must contain a
book of size $m$, that is, an edge shared by at least $m$ different triangles.
-/
def Erdos80Prop (c : ℝ) (m : ℕ) (n : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin n), G.edgeFinset.card ≥ c * (n : ℝ)^2 →
  (∀ uv ∈ G.edgeFinset, (trianglesContaining G uv).Nonempty) →
  ∃ uv ∈ G.edgeFinset, m ≤ (trianglesContaining G uv).card

noncomputable def fFunction (c : ℝ) (n : ℕ) : ℕ := sSup {m : ℕ | Erdos80Prop c m n}

/--
Estimate $f_c(n)$ - lower bound.
-/
@[category research open, AMS 5]
theorem erdos_80.parts.i.lower_bound :
    ∀ c : ℝ, 0 < c → (answer(sorry) : ℕ → ℝ) =O[atTop] (fun (n : ℕ) ↦ (fFunction c n : ℝ)) := by
  sorry

/--
Estimate $f_c(n)$ - upper bound.
-/
@[category research open, AMS 5]
theorem erdos_80.parts.i.upper_bound :
    ∀ c : ℝ, 0 < c → (fun (n : ℕ) ↦ (fFunction c n : ℝ)) =O[atTop] (answer(sorry) : ℕ → ℝ) := by
  sorry

/--
In particular, is it true that $f_c(n) > n^\epsilon$ for some $\epsilon > 0$?
(Here "for all sufficiently large $n$" is intended, though not stated explicitly.)

Fox and Loh [FoLo12] proved that this is false for all $c < 1/4$; see the variant below.
-/
@[category research solved, AMS 5]
theorem erdos_80.parts.ii :
    answer(False) ↔ ∀ c : ℝ, 0 < c → ∃ ε : ℝ, 0 < ε ∧
      ∀ᶠ (n : ℕ) in atTop, (n : ℝ)^ε < (fFunction c n : ℝ) := by
  sorry

/--
Is it true that $f_c(n) \gg \log n$?
-/
@[category research open, AMS 5]
theorem erdos_80.parts.iii :
    answer(sorry) ↔ ∀ c : ℝ, 0 < c →
      (fun (n : ℕ) ↦ (n : ℝ).log) =O[atTop] (fun (n : ℕ) ↦ (fFunction c n : ℝ)) := by
  sorry

/--
Alon and Trotter showed that, provided $c < 1/4$, $f_c(n) \ll_c n^{1/2}$.
-/
@[category research solved, AMS 5]
theorem erdos_80.variants.alon_trotter_sqrt_upper_bound_of_c_lt_quarter :
    ∀ c : ℝ, 0 < c → c < 1/4 → (fun (n : ℕ) ↦ (fFunction c n : ℝ))
      =O[atTop] (fun (n : ℕ) ↦ (n : ℝ).sqrt) := by
  sorry

/--
Szemerédi observed that his regularity lemma implies that $f_c(n) \to \infty$.
-/
@[category research solved, AMS 5]
theorem erdos_80.variants.szemeredi_tends_to_infinity :
    ∀ c : ℝ, 0 < c → Tendsto (fun (n : ℕ) ↦ (fFunction c n : ℝ)) atTop atTop := by
  sorry

/--
Edwards (unpublished) and Khadzhiivanov and Nikiforov [KhNi79] proved independently that
$f_c(n) ≥ n/6$ when $c > 1/4$ (see [erdosproblems.com/905]).
-/
@[category research solved, AMS 5]
theorem erdos_80.variants.edwards_khadzhiivanov_nikiforov_linear_lower_bound_of_quarter_lt_c :
    ∀ c : ℝ, ∀ n : ℕ, 1/4 < c → (fFunction c n : ℝ) ≥ (n : ℝ) / 6 := by
  sorry

/--
Fox and Loh [FoLo12] proved that $f_c(n) \leq n^{O(1/\log\log n)}$ for all $c < 1/4$,
disproving the first conjecture of Erdős.
-/
@[category research solved, AMS 5]
theorem erdos_80.variants.fox_loh_subpolynomial_upper_bound_of_c_lt_quarter :
    ∀ c : ℝ, 0 < c → c < 1/4 → ∃ k : ℝ, k > 0 ∧
      ∀ᶠ (n : ℕ) in atTop, (fFunction c n : ℝ) ≤ (n : ℝ)^(k / (n : ℝ).log.log) := by
  sorry

end Erdos80
