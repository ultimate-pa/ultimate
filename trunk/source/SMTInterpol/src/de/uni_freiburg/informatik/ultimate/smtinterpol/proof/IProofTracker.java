/*
 * Copyright (C) 2012 University of Freiburg
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

import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.SMTAffineTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;

/**
 * A tracker for rewrite steps done while rewriting the original formula into
 * canonical form and producing clauses.  The interface is designed to prevent
 * creation of unneeded terms if proof tracking is disabled.
 * @author Juergen Christ
 */
public interface IProofTracker {
	//// ==== Tracking ====
	/**
	 * Track an expansion rewrite.
	 * @param orig     The original term.
	 */
	public void expand(ApplicationTerm orig);
	/**
	 * Track the expand definition rule.
	 * @param orig The original term.
	 * @param res  The result of the expansion.
	 */
	public void expandDef(Term orig, Term res);
	/**
	 * Track an equality rewrite.
	 * @param args The arguments to the equality.
	 * @param res  The result of the rewrite.
	 * @param rule The number of the rule used.
	 */
	public void equality(Term[] args, Object res, int rule);
	/**
	 * Track a distinct rewrite.
	 * @param args The arguments to the distinct.
	 * @param res  The result of the rewrite.
	 * @param rule The number of the rule used.
	 */
	public void distinct(Term[] args, Term res, int rule);
	/**
	 * Track the transformation of a Boolean distinct into a negated equality.
	 * @param lhs          The left-hand-side of the distinct.
	 * @param rhs          The right-hand-side of the distinct.
	 * @param firstNegated Should the lhs be negated?
	 */
	public void distinctBoolEq(Term lhs, Term rhs, boolean firstNegated);
	/**
	 * Track the result of a negation rewrite.
	 * @param pos  What to negate.
	 * @param res  The result of the rewrite.
	 * @param rule The number of the rule.
	 */
	public void negation(Term pos, Term res, int rule);
	/**
	 * Track an or rewrite
	 * @param args The arguments to the disjunction.
	 * @param res  The simplification result.
	 * @param rule The rule number.
	 */
	public void or(Term[] args, Term res, int rule);
	/**
	 * Track an ite rewrite.
	 * @param cond     The condition.
	 * @param thenTerm The then-term.
	 * @param elseTerm The else-term.
	 * @param res      The result.
	 * @param rule     The rule number.
	 */
	public void ite(Term cond, Term thenTerm, Term elseTerm, Term res, int rule);
	/**
	 * Track removal of a Boolean connective.
	 * @param origArgs The original term.
	 * @param result   (Part of) the resulting term (used for SMTAffineTerms).
	 * @param rule The rule number.
	 */
	public void removeConnective(Term[] origArgs, Term result, int rule);
	/**
	 * Track an annotation stripping.
	 * @param orig The annotated term.
	 */
	public void strip(AnnotatedTerm orig);
	/**
	 * Track a canonical summarization.
	 * @param fsym The function symbol of the original term.
	 * @param args The arguments of the original term.
	 * @param res  The result of the rewrite.
	 */
	public void sum(FunctionSymbol fsym, Term[] args, Term res);
	/**
	 * Track a normalization of a constant term.  This rule is needed, e.g., to
	 * justify the transformation of 1.5 into (/ 3 2).
	 * @param term The constant.
	 * @param res  The result of the transformation.
	 */
	public void normalized(ConstantTerm term, SMTAffineTerm res);
	/**
	 * Track an leq simplification.
	 * @param leq  The leq0-term.
	 * @param res  The rewrite result.
	 * @param rule The simplification rule.
	 */
	public void leqSimp(SMTAffineTerm leq, Term res, int rule);
	/**
	 * Track an application of the IRA-Hack.
	 * @param orig     The original term.
	 * @param origArgs Arguments that should be used for the original term.
	 * @param newArgs  The arguments to that term after applying the IRA-Hack.
	 */
	public void desugar(ApplicationTerm orig, Term[] origArgs, Term[] newArgs);
	/**
	 * Track a modulo-rewrite. (mod x y) ==> (- x  (* y (div x y))) under the
	 * assumption y is integral and not 0.
	 * @param appTerm The modulo application term.
	 * @param res     The resulting term.
	 */
	public void modulo(ApplicationTerm appTerm, Term res);
	/**
	 * Track a modulo simplification, i.e., a rewrite that does not transform
	 * a modulo into an application term like 
	 * {@link #modulo(ApplicationTerm, Term)}, but evaluates applications
	 * (mod x y) where either y is 1 or -1, or x is constant.
	 * @param x    The first argument of the mod.
	 * @param y    The second argument of the mod.
	 * @param res  The result of the rule.
	 * @param rule The simplification rule applied.
	 */
	public void mod(Term x, Term y, Term res, int rule);
	/**
	 * Track a divison simplification, i.e., a rewrite that evaluates
	 * applications (div x y) where either y is 1 or -1, or x is constant.
	 * @param x    The first argument of the div.
	 * @param y    The second argument of the div.
	 * @param res  The result of the rule.
	 * @param rule The simplification rule applied.
	 */
	public void div(Term x, Term y, Term res, int rule);
	/**
	 * Track a divisible-rewrite.  ((_ divisible n) x) ==> (= x (* n (div x n))).
	 * @param divn The divisible-by-n symbol.
	 * @param div  The divisible term.
	 * @param res  The rewritten result.
	 */
	public void divisible(FunctionSymbol divn, Term div, Term res);
	/**
	 * Track a to_int simplification where the argument is constant.
	 * @param arg The argument.
	 * @param res The result.
	 */
	public void toInt(Term arg, Term res);
	/**
	 * Track a to_real simplification where the argument is constant.
	 * @param arg The argument.
	 * @param res The result.
	 */
	public void toReal(Term arg, Term res);
	/**
	 * Track an array rewrite.
	 * @param args   The arguments of the original array.
	 * @param result The result of the rewrite.
	 * @param rule   The rule used.
	 */
	public void arrayRewrite(Term[] args, Term result, int rule);
	/**
	 * Rewrite for "useless store": (= a (store a i v)).
	 * @param store      The store term.
	 * @param result     The result of the rewrite.
	 * @param arrayFirst Is the array the lhs?
	 */
	public void storeRewrite(ApplicationTerm store, Term result, boolean arrayFirst);
	
	//// ==== Tracking of clausification ====
	
	/**
	 * Track the introduction of a quote.
	 * @param orig  The original term.
	 * @param quote The quoted term.
	 */
	public void quoted(Term orig, Literal quote);
	/**
	 * Track an equality interning.
	 * @param lhs The left-hand-side.
	 * @param rhs The right-hand-side.
	 * @param res The result.
	 */
	public void eq(Term lhs, Term rhs, Term res);
	/**
	 * Convenience function to prevent term creation of equality terms if
	 * proof generation is disabled.
	 * @param lhs    The left-hand-side.
	 * @param rhs    The right-hand-side.
	 * @param eqAtom The equality atom.
	 */
	public void eq(Term lhs, Term rhs, DPLLAtom eqAtom);
	/**
	 * Convenience function to prevent creation of leq0 terms if proof
	 * generation is disabled.
	 * @param sum The sum to be less than or equal to 0.
	 * @param lit The resulting literal.
	 */
	public void leq0(SMTAffineTerm sum, Literal lit);
	/**
	 * Track literal creation.
	 * @param term The term transformed into a literal.
	 * @param lit  The resulting literal.
	 */
	public void intern(Term term, Literal lit);
	/**
	 * Apply double negation elimination on a literal.  Note that the literal
	 * has to be negated already.
	 * @param lit    The literal to negate
	 * @param theory The theory to use in conversion.
	 */
	public void negateLit(Literal lit, Theory theory);
	/**
	 * Apply disjunction flattening.
	 * @param args   The term to flatten.
	 * @param simpOr Apply disjunction simplification on the flattened and
	 *               interned clause. 
	 */
	public void flatten(Term[] args, boolean simpOr);
	/**
	 * Prepend a disjunction simplification step.
	 * @param args The disjunction to simplify.
	 */
	public void orSimpClause(Term[] args);
	/**
	 * Create a clause-creation proof.
	 * @param proof The proof whose result is transformed into a clause.
	 * @return The clause conversion proof.
	 */
	public Term clause(Term proof);
	/**
	 * Create aux axiom input (tautologies).
	 * @param auxKind The kind of the aux axiom.
	 * @param auxLit  The term auxiliary literal.
	 * @param data    Data needed to construct the result term.
	 * @param base    Base used for Term-ITEs.
	 * @param auxData Auxiliary data (needed for Term-ITEs).
	 * @return Proof node of the auxiliary tautology.
	 */
	public Term auxAxiom(int auxKind, Literal auxLit, Term data, Term base,
			Object auxData);
	/**
	 * Track a structural splitting step.
	 * @param data      Data used to produce the result of the split.
	 * @param proof     The proof for the formula being split.
	 * @param splitKind The kind of split (@see ProofConstants).
	 * @return The proof for the split.
	 */
	public Term split(Term data, Term proof, int splitKind);
	
	//// ===== Accessors ====
	/**
	 * Get a rewrite proof justifying the rewrites from <code>asserted</code>
	 * into <code>result</code>.
	 * 
	 * Note that <code>asserted</code> is a Boolean term from the input.  If a
	 * proof should be produced, it has to be wrapped by the
	 * <code>@asserted</code> function.  The <code>result</code> might contain
	 * SMTAffineTerms. 
	 * @param asserted The input term.
	 * @return The rewrite proof or <code>null</code> if proof-production is
	 *         disabled.
	 */
	public Term getRewriteProof(Term asserted);
	
	//// ==== Incrementality ====
	/**
	 * Reset the cached proof data.
	 */
	public void reset();

	//// ==== Creating descendent trackers
	/**
	 * Create a sub-tracker.
	 * @return A sub-tracker with the same tracking capabilities than this
	 *         tracker.
	 */
	public IProofTracker getDescendent();
	/**
	 * Prepare to apply the IRA-Hack.  This should return a copy of the original
	 * arguments to ensure correct applications of the desugar rule.
	 * @param args The original arguments.
	 * @return <code>null</code> if no desugar should be applied and a copy of
	 *         the argument otherwise. 
	 */
	public Term[] prepareIRAHack(Term[] args);
	/**
	 * Mark the position where a clause simplification rule can be applied.
	 * This function is necessary since clause simplification is delayed and,
	 * hence, recognized at the wrong time. 
	 */
	public void markPosition();
	/**
	 * Produce the disjunctive arguments of an auxiliary axiom.
	 * @param auxlit The auxiliary literal (in polarity of the aux axiom)
	 * @param args   The remaining arguments.
	 * @return Arguments of the clause (stub) or <code>null</code> if no proof
	 *         tracking.
	 */
	public Term[] produceAuxAxiom(Literal auxlit, Term... args);
	/**
	 * Save the current position in the rewrite list.
	 */
	public void save();
	/**
	 * Restore to the last position in the list.
	 */
	public void restore();
	/**
	 * Remove all saved information.
	 */
	public void cleanSave();
	/**
	 * Notification about the creation of a literal.  This function is only
	 * used to compute the correct delayed clause simplification axiom.
	 * @param lit The created literal (in correct polarity.
	 * @param t   The term for which the literal has been created.
	 * @return Was <code>lit</code> the first literal for <code>t</code>? 
	 */
	public boolean notifyLiteral(Literal lit, Term t);
	/**
	 * Notification about the simplification of a literal to false.  This
	 * function is only used to compute the correct delayed clause
	 * simplification axiom.
	 * @param t The term that simplified to false.
	 */
	public void notifyFalseLiteral(Term t);
}
