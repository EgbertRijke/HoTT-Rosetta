import unittest

from rosetta.math_text import (
    _word_like_book_macros,
    normalize_heading_title,
    normalize_markdown_math,
    normalize_math,
)


class MathTextTests(unittest.TestCase):
    def test_logical_connectives_remain_distinct_from_their_interpretations(self):
        self.assertEqual(normalize_math(r"\bot, \emptyt, P\Leftrightarrow Q, P\leftrightarrow Q"),
                         "⊥, empty, P⇔ Q, P↔ Q")
        self.assertEqual(normalize_math(r"\bottomrule"), r"\bottomrule")

    def test_cases_keep_grouping_values_conditions_and_surrounding_equations(self):
        self.assertEqual(
            normalize_math(r"h(x)=\begin{cases}H(m,q) & \text{if }x=\inl(q)\\"
                           r"p_S(n,H) & \text{if }x=\inr(\refl{}).\end{cases}"),
            "h(x)=cases {\nH(m,q) if x=inl(q)\np_S(n,H) if x=inr(refl).\n}",
        )
        self.assertEqual(
            normalize_math(r"a &=\begin{cases}b & \text{if }P\\c & \text{if }Q\end{cases}\\"
                           r"&=d"),
            "a =cases {\nb if P\nc if Q\n}\n=d",
        )
        self.assertEqual(normalize_math(r"\begin{cases}a & P"), r"\begin{cases}a P")

    def test_labelled_arrows_preserve_the_retraction_pair_labels(self):
        self.assertEqual(
            normalize_math(r"X \stackrel{i}{\longrightarrow} Y \stackrel{r}{\longrightarrow} X"),
            "X ⟶[i] Y ⟶[r] X",
        )
        self.assertEqual(
            normalize_math(r"\stackrel {\ap{f}{p}} {\longrightarrow}"),
            "⟶[ap_{f}(p)]",
        )
        self.assertEqual(normalize_math(r"\stackrel{i}"), r"\stackrel{i}")
        self.assertEqual(normalize_math(r"\stackrelation"), r"\stackrelation")

    def test_type_judgments_use_the_explicit_book_macro(self):
        self.assertEqual(normalize_math(r"\Gamma,x:A\vdash B(x)~\type"),
                         "Γ,x:A⊢ B(x) type")
        self.assertEqual(normalize_math(r"\typewriter"), r"\typewriter")

    def test_total_map_keeps_its_optional_base_map(self):
        self.assertEqual(
            normalize_math(r"\tot{g}, \tot[f]{g}, \tot[f]{\tot{g}}"),
            "tot(g), tot_f(g), tot_f(tot(g))",
        )

    def test_singleton_induction_aliases_from_book(self):
        self.assertEqual(
            normalize_math(r"\singind_a, \singcomp_a, \indsing_a, \compsing_a, \omega"),
            "ind-sing_a, comp-sing_a, ind-sing_a, comp-sing_a, ω",
        )

    def test_foundational_commands(self):
        self.assertEqual(
            normalize_math(r"\addN(m,\succN(n)) \jdeq \succN(\addN(m,n))"),
            "add-ℕ(m,succ-ℕ(n)) ≐ succ-ℕ(add-ℕ(m,n))",
        )

    def test_inline_pandoc_math_becomes_code(self):
        self.assertEqual(
            normalize_markdown_math(r"For $`n:\N`$ we have $`\zeroN+n`$."),
            "For `n:ℕ` we have `0+n`.",
        )

    def test_display_pandoc_math_becomes_text_fence(self):
        source = "``` math\n\\begin{equation*}\n\\N\\to\\N\n\\end{equation*}\n```"
        self.assertEqual(
            normalize_markdown_math(source), "```text\nℕ→ℕ\n```"
        )

    def test_dependent_products_and_identifications(self):
        self.assertEqual(
            normalize_math(r"\prd{x:A}\id[A]{f(x)}{g(x)}"),
            "Π(x:A) f(x) =_A g(x)",
        )

    def test_multline_display_preserves_every_line(self):
        for environment in ("multline", "multline*"):
            source = (
                "``` math\n\\begin{" + environment + "}\n"
                "A \\\\\n\\simeq B\n\\end{" + environment + "}\n```"
            )
            self.assertEqual(
                normalize_markdown_math(source), "```text\nA\n≃ B\n```"
            )

    def test_html_table_math_is_normalized(self):
        self.assertEqual(
            normalize_markdown_math('<span class="math inline">$A\\to B$</span>'),
            "`A→ B`",
        )

    def test_nested_concatenation(self):
        self.assertEqual(
            normalize_math(r"\ct{\alpha}{(\ct{\beta}{\gamma})}"),
            "α ∙ (β ∙ γ)",
        )

    def test_universe_and_proposition_notation(self):
        self.assertEqual(
            normalize_math(r"A:\UU \to \prop_\UU"),
            "A:𝒰 → Prop_𝒰",
        )

    def test_common_homotopy_and_fiber_notation(self):
        self.assertEqual(
            normalize_math(
                r"\fib{f}{b} \eqv{A}{B}, f\circ g\htpy\idfunc"
            ),
            "fib(f, b) A ≃ B, f∘ g~id",
        )

    def test_common_logical_notation(self):
        self.assertEqual(
            normalize_math(r"\brck{P}\to\isdecidable(P), \neg P, x\neq y"),
            "‖P‖→is-decidable(P), ¬ P, x≠ y",
        )

    def test_equiv_is_congruence_not_type_equivalence(self):
        self.assertEqual(
            normalize_math(r"x\equiv y\mod k, A\simeq B"),
            "x≡ ymod k, A≃ B",
        )

    def test_common_named_constructions(self):
        self.assertEqual(
            normalize_math(
                r"\succZ, \succFin_k, \natFin, \distN, \iscontr(A), \isemb(f)"
            ),
            "succ-ℤ, succ-Fin_k, nat-Fin, dist-ℕ, is-contr(A), is-emb(f)",
        )

    def test_word_like_book_macros_use_kebab_case(self):
        self.assertEqual(
            normalize_math(
                r"\issplitsurjective(f), \hasdecidableequality(A), \isupperbound(P)"
            ),
            "is-split-surjective(f), has-decidable-eq(A), is-upper-bound(P)",
        )
        for command in _word_like_book_macros():
            with self.subTest(command=command):
                self.assertNotIn(command, normalize_math(command))

    def test_multiple_of_gcd_uses_the_books_displayed_notation(self):
        self.assertEqual(
            normalize_math(r"\ismultipleofgcd(a,b,n)"),
            "M(a,b,n)",
        )

    def test_accents_and_property_names(self):
        self.assertEqual(
            normalize_math(
                r"\tilde{f}, \check{A}, \hasinverse(f), \isequiv(f)"
            ),
            "f̃, Ǎ, has-inverse(f), is-equiv(f)",
        )

    def test_command_prefix_does_not_corrupt_unknown_command(self):
        self.assertEqual(normalize_math(r"\independent"), r"\independent")

    def test_nested_truncation_and_binomial_notation(self):
        self.assertEqual(
            normalize_math(
                r"\Brck{\sm{x:A}P(x)}, \dbinomtype[\UU]{A}{B}, \binom{n}{k}"
            ),
            "‖Σ(x:A) P(x)‖, binom_𝒰(A, B), binom(n, k)",
        )

    def test_fixture_backed_symbols_and_formatting(self):
        self.assertEqual(
            normalize_math(
                r"\Big(A\twoheadrightarrow B\Big), "
                r"G\cong H, \mu, \pi, \leftunit, \ev"
            ),
            "(A↠ B), G≅ H, μ, π, left-unit, ev",
        )

    def test_labels_placeholders_and_common_blackboard_letters(self):
        self.assertEqual(
            normalize_math(
                r"\label{eq:test}\phantom{A} \mathbb{Z} "
                r"\bar{\alpha} \ind{\times}"
            ),
            "A ℤ ᾱ ind-×",
        )

    def test_nested_action_and_fixture_formatting_macros(self):
        self.assertEqual(
            normalize_math(
                r"\ap{tr_{E}(\lloop)}{\alpha}, "
                r"\mathsf{Pointed\usc{}Type}, "
                r"x\ct_y, \tag{\textasteriskcentered}, x\pm y"
            ),
            "ap_{tr_{E}(loop)}(α), Pointed-Type, x∙_y, (*), x± y",
        )

    def test_later_chapter_macros_follow_book_definitions(self):
        self.assertEqual(
            normalize_math(
                r"\group, \isgroup, \loopspace[n]{A}, \trunc{0}{A}, "
                r"\W(A,B), \collect(x,\alpha), \mulcircle, "
                r"\universalcovercircle, \inneg"
            ),
            "Group, is-group, Ω^n(A), ‖A‖_0, W(A,B), tree(x,α), "
            "mul_(S^1), E_(S^1), in-neg",
        )

    def test_later_chapter_parameterized_macros(self):
        self.assertEqual(
            normalize_math(
                r"\comphtpy{S^1}, \multiset{\UU}, "
                r"\issmallmultiset{\VV}(X), \yggdrasil"
            ),
            "comp_S^1, M_𝒰, is-small_M_𝒱(X), Y_𝒰",
        )

    def test_stirling_number_macro(self):
        self.assertEqual(
            normalize_math(r"\stirling{A}{B}"), "Stirling(A, B)"
        )

    def test_texorpdf_title_with_suffix_uses_readable_branch(self):
        self.assertEqual(
            normalize_heading_title(
                r"Identity types of \texorpdfstring{$\Sigma$-}{dependent pair }types"
            ),
            "Identity types of dependent pair types",
        )

    def test_texorpdf_title_uses_readable_branch(self):
        self.assertEqual(
            normalize_heading_title(r"Laws on \texorpdfstring{$\N$}{ℕ}"),
            "Laws on ℕ",
        )


if __name__ == "__main__":
    unittest.main()
