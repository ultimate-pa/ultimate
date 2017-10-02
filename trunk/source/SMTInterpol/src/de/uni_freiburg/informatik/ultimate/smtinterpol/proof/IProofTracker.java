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
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;

/**
 * The proof tracker interface. There are two implementations, one that builds the proof and one that only builds the
 * proved term.
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
	 * Create a proof that input term x equals z from a proof for {@code (= x y)} and a proof for {@code (= y z)}.
	 *
	 * @param y
	 *            the intermediate term annotated with a proof {@code (= x y)}.
	 * @param z
	 *            the final term annotated with a proof {@code (= y z)}.
	 * @return the term z annotated with a proof {@code (= x z)}.
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
	 * Create a rewrite proof for {@code (= orig res)}. This function doesn't check if the rewrite proof is sound but
	 * trusts the caller.
	 *
	 * @return res annotated with proof of {@code (= orig res)}.
	 */
	public Term buildRewrite(Term orig, Term res, Annotation rule);

	/**
	 * Create a intern rewrite proof for {@code (= orig res)}. This function doesn't check if the rewrite proof is sound
	 * but trusts the caller.
	 *
	 * @return res annotated with proof of {@code (= orig res)}.
	 */
	public Term intern(Term orig, Term res);

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
	public Term orSimpClause(Term rewrite, Literal[] finalClause);

	// TODO *******************************************************************

	/**
	 * Create aux axiom input (tautologies).
	 * @param axiom The axiom.
	 * @param auxRule The rule for the axiom.
	 * @return Proof node of the auxiliary tautology.
	 */
	public Term auxAxiom(Term axiom, Annotation auxRule);

	/**
	 * Track a structural splitting step.
	 *
	 * @param formula
	 *            The formula being split annotated with its proof.
	 * @param subterm
	 *            Data used to produce the result of the split.
	 * @param splitKind
	 *            The kind of split (@see ProofConstants).
	 *
	 * @return The subterm annotated with its proof.
	 */
	public Term split(Term formula, Term subterm, Annotation splitKind);

	/**
	 * Annotated an asserted formula with its proof (@asserted formula).
	 *
	 * @param formula
	 *            The formula to annotate.
	 * @return the formula annotated with its proof.
	 */
	public Term asserted(Term formula);

	/**
	 * Create a proof of g from the proof of f and the rewrite proof of (= f g) for g.
	 *
	 * @param asserted
	 *            the asserted formula with its proof.
	 * @param rewrite
	 *            the simplified formula with a proof of {@code (= asserted simpFormula)}.
	 * @return the resulting simpFormula annotated with the complete proof
	 */
	public Term getRewriteProof(Term asserted, Term rewrite);

	/**
	 * Creates the clause proof of t. This is usually the annotation of t.
	 *
	 * @param t the proved term annotated with its proof.
	 * @return the proof.
	 */
	public Term getClauseProof(Term t);
}
