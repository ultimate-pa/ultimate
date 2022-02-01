/*
 * Copyright (C) 2017 University of Freiburg
 *
 * This file is part of SMTInterpol.
 *
 * SMTInterpol is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * SMTInterpol is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with SMTInterpol.  If not, see <http://www.gnu.org/licenses/>.
 */
package de.uni_freiburg.informatik.ultimate.smtinterpol.proof;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/**
 * The proof tracker interface. There are two implementations, one that builds the proof and one that only builds the
 * proved term.
 *
 * Many function take terms annotated with proofs. The annotation is only present when proof generation is enabled; the
 * NoopTracker will not produce this annotation, nor expect the annotation. Other classes should use
 * {@link #getProvedTerm} to extract the term without the proof.
 *
 * Some proof rules expect a term {@code g} to be annotated with a proof for {@code (= f g)}, where {@code f} is the
 * original term, while others just expect the term {@code g} to be annotated with a proof for {@code g} itself. This is
 * documented for each function.
 *
 * @author Jochen Hoenicke
 */
public interface IProofTracker {

	/**
	 * Returns the converted term without the proof.
	 *
	 * @param term
	 *            A term optionally annotated with a proof.
	 * @return the term without the proof.
	 */
	public Term getProvedTerm(Term t);

	/* == combine rewrite rules == */
	/**
	 * Create a proof that input term x equals x using reflexivity.
	 *
	 * @param x
	 *            a simple term (no proof annotation).
	 * @return the term x annotated with a proof <code>(= x x)</code>.
	 */
	public Term reflexivity(Term x);

	/**
	 * Create a proof that input term x equals (or implies) z from a proof for {@code (= x y)} (or {@code (=> x y)}) and
	 * a proof for {@code (= y z)} (or {@code (=> y z)}).
	 *
	 * @param y
	 *            the intermediate term annotated with a proof {@code (= x y)} (or {@code (=> x y)}).
	 * @param z
	 *            the final term annotated with a proof {@code (= y z)} (or {@code (=> y z)}).
	 * @return the term z annotated with a proof {@code (= x z)} (or {@code (=> x z)} if at least one of the input
	 *         proofs proves an implication).
	 */
	public Term transitivity(Term y, Term z);

	/**
	 * Create a proof that input term x equals {@code f(b[0],...,b[n])} from a proof for {@code (= x a)} where
	 * {@code a = f(a[0],...,a[n])} and an array of b, each annotated with a proof that {@code (= a[i] b[i])}.
	 *
	 * @param a
	 *            the term a=f(a[0],...,a[n]) with a proof {@code (= x a)}.
	 * @param b
	 *            an array of terms b[i] annotated with proofs {@code (= a[i] b[i])}.
	 * @return the term z annotated with a proof {@code (= x f(b[0],...b[n]))}.
	 */
	public Term congruence(Term a, Term[] b);

	/**
	 * Create a proof that input term x implies {@code (or b[0] ... b[n]} from a proof for {@code (= x a)} where
	 * {@code a = (or a[0],...,a[n])}, and an array of b each annotated with a proof that {@code (=> a[i] b[i])} (or
	 * {@code (= a[i] b[i])}).
	 *
	 * @param a
	 *            the term a=(or a[0] ... a[n]) with a proof {@code (= x a)}
	 * @param b
	 *            an array of terms b[i] annotated with proofs {@code (=> a[i] b[i])} (or {@code (= a[i] b[i])})
	 * @return the term {@code (or b[0] ... b[n]} annotated with a proof
	 *         {@code (=> (or a[0] ... a[n]) (or b[0] ... b[n])} or {@code (=> (or a[0] ... a[n]) (or b[0] ... b[n])} if
	 *         the proofs for the b[i] contain no implication proof.
	 */
	public Term orMonotony(Term a, Term[] b);

	/**
	 * Lift a rewrite over an exists, i.e. convert a proof for {@code (= f g)} into a proof for
	 * {@code (= (exists varlist f) (exists varlist g))}
	 *
	 * @param old
	 *            the existential quantifier to left
	 * @param newBody
	 *            the formula g with its rewrite proof for {@code (= f g)}.
	 * @return the new existential quantifier annotated with a proof for {@code (= old (exists varlist g))}.
	 */
	public Term exists(QuantifiedFormula old, Term newBody);

	/* == rewrite rules == */

	/**
	 * Create a rewrite proof for {@code (= orig res)} or {@code (=> orig res)}, respectively. This function doesn't
	 * check if the rewrite proof is sound but trusts the caller.
	 *
	 * @param orig
	 *            the original term
	 * @param res
	 *            the rewritten term
	 * @param rule
	 *            the rewrite rule, one of {@link ProofConstants}.RW_*
	 * @return res annotated with proof of {@code (= orig res)} or {@code (=> orig res)}, respectively.
	 */
	public Term buildRewrite(Term orig, Term res, Annotation rule);

	/**
	 * Create a intern rewrite proof for {@code (= orig res)}. This function doesn't check if the rewrite proof is sound
	 * but trusts the caller.
	 *
	 * @param orig
	 *            the original term
	 * @param res
	 *            the rewritten term
	 * @return res annotated with proof of {@code (= orig res)}.
	 */
	public Term intern(Term orig, Term res);

	/**
	 * Rewrites a forall quantifier into is normal form, a negated exists quantifier. The normal form is given as
	 * parameter and this function doesn't check it.
	 *
	 * @param old
	 *            the forall quantifier.
	 * @param negNewBody
	 *            the rewritten quantifer.
	 * @return negNewBody annotated with its proof.
	 */
	public Term forall(QuantifiedFormula old, Term negNewBody);

	//// ==== Tracking of clausification ====

	/**
	 * Apply disjunction flattening.
	 *
	 * @param orig
	 *            The term to flatten.
	 * @param flattenedOrs
	 *            The sub terms of orig (ApplicationTerms with function "or") that were flattened.
	 * @return the rewrite proof to flatten the orig term.
	 */
	public Term flatten(Term orig, Set<Term> flattenedOrs);

	/**
	 * Prepend a disjunction simplification step. This removes double entries and {@code false} from the disjunction.
	 *
	 * @param args
	 *            The disjunction to simplify.
	 * @return
	 */
	public Term orSimpClause(Term rewrite);

	/**
	 * Create aux axiom input (tautologies). The term axiom is introduced as Tautology. This doesn't check if the axiom
	 * is correct.
	 *
	 * @param axiom
	 *            The axiom.
	 * @param auxRule
	 *            The rule for the axiom, one of {@link ProofConstants}.AUX_*.
	 * @return Proof node of the auxiliary tautology.
	 */
	public Term auxAxiom(Term axiom, Annotation auxRule);

	/**
	 * Track a structural splitting step. Rewrites formula into subterm.
	 *
	 * @param formula
	 *            The formula being split annotated with its proof.
	 * @param subterm
	 *            The subformula, which is the result of the split.
	 * @param splitKind
	 *            The kind of split, see {@see ProofConstants}.SPLIT_*.
	 * @return The subterm annotated with its proof.
	 */
	public Term split(Term formula, Term subterm, Annotation splitKind);

	/**
	 * Introduce a universal quantifier.
	 *
	 * @param formula
	 *            The formula containing free variables annotated with its proof.
	 * @param vars
	 *            the variables to quantify
	 * @return The universally quantified formula annotated with its proof.
	 */
	public Term allIntro(Term formula, TermVariable[] vars);

	/**
	 * Annotate an asserted formula with its proof {@code (@asserted formula)}.
	 *
	 * @param formula
	 *            The formula to annotate.
	 * @return the formula annotated with its proof.
	 */
	public Term asserted(Term formula);

	/**
	 * Create a proof of g from the proof of f and the rewrite proof of {@code (= f g)} (or {@code (=> f g)}) for g.
	 *
	 * @param asserted
	 *            the asserted formula f annotated with its proof.
	 * @param rewrite
	 *            the simplified formula g annotated with a proof of {@code (= f g)} (or {@code (=> f g)}).
	 * @return the resulting simpFormula annotated with the complete proof
	 */
	public Term modusPonens(Term asserted, Term rewrite);

	/**
	 * Creates the clause proof of t. This is usually the annotation of t.
	 *
	 * @param t the proved term annotated with its proof.
	 * @return the proof.
	 */
	public Term getClauseProof(Term t);
}
