/*
 * Copyright (C) 2021 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2021 University of Freiburg
 *
 * This file is part of the ULTIMATE SmtLibUtils Library.
 *
 * The ULTIMATE SmtLibUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE SmtLibUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE SmtLibUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE SmtLibUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE SmtLibUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.smtlibutils.abduction;

import java.util.Collections;
import java.util.Set;
import java.util.function.ToIntFunction;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier.PartialQuantifierElimination;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/**
 * Performs logical abduction. That is, given a premise phi and a conclusion psi, such that the implication "phi -> psi"
 * is NOT valid, attempts to find a formula phi' such that the implication "phi /\ phi' -> psi" is valid, and
 * furthermore "phi /\ phi'" is satisfiable (ruling out trivial solutions such as false). The returned phi' should be as
 * simple and as logically weak as possible.
 *
 * Based on the algorithm presented in the 2013 Interpolation Workshop presentation by Isil Dillig
 * <https://www.cs.utexas.edu/~isil/interpolation-workshop.pdf>.
 *
 * As a slight extension, this class can also generate predicates phi' such that phi' implies the logical equivalence
 * "phi <-> psi", rather than only the implication "phi -> psi". A solution phi' is consistent with both phi and psi.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 */
public class Abducer {
	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private final ManagedScript mScript;
	private final ToIntFunction<TermVariable> mCost;
	private final Set<TermVariable> mForbiddenVars;

	/**
	 * Creates a new abducer.
	 *
	 * @param services
	 *            Ultimate services, used in quantifier elimination
	 * @param script
	 *            Script instance, used for satisfiability checks and quantifier elimination
	 */
	public Abducer(final IUltimateServiceProvider services, final ManagedScript script) {
		this(services, script, Collections.emptySet());
	}

	/**
	 * Creates a new abducer that restricts the variables that can be used in the resulting formula.
	 *
	 * @param services
	 *            Ultimate services, used in quantifier elimination
	 * @param script
	 *            Script instance, used for satisfiability checks and quantifier elimination
	 * @param forbiddenVars
	 *            A set of variables that may not be used in the resulting formula (phi' in the description above). Note
	 *            that this restricts the problem and may lead to no solution being found.
	 */
	public Abducer(final IUltimateServiceProvider services, final ManagedScript script,
			final Set<TermVariable> forbiddenVars) {
		this(services, script, x -> 1, forbiddenVars);
	}

	/**
	 * Creates a new abducer that restricts the variables that can be used in the resulting formula, and assigns a cost
	 * (to be minimized) to used variables.
	 *
	 * @param services
	 *            Ultimate services, used in quantifier elimination
	 * @param script
	 *            Script instance, used for satisfiability checks and quantifier elimination
	 * @param cost
	 *            A cost function that assigns a cost to each variable. The computation minimizes the sum cost of all
	 *            free variables in the solution.
	 * @param forbiddenVars
	 *            A set of variables that may not be used in the resulting formula (phi' in the description above). Note
	 *            that this restricts the problem and may lead to no solution being found.
	 */
	public Abducer(final IUltimateServiceProvider services, final ManagedScript script,
			final ToIntFunction<TermVariable> cost, final Set<TermVariable> forbiddenVars) {
		mServices = services;
		mLogger = services.getLoggingService().getLogger(Abducer.class);
		mScript = script;
		mCost = cost;
		mForbiddenVars = forbiddenVars;
	}

	/**
	 * Computes the solution to a given abduction problem.
	 *
	 * @param premise
	 *            The premise of an invalid implication (phi in the description above)
	 * @param conclusion
	 *            The conclusion of an invalid implication (psi in the description above)
	 * @return the problem solution, if one exists (psi in the description above). Null otherwise.
	 */
	public Term abduce(final Term premise, final Term conclusion) {
		final Term solution =
				solveAbductionProblem(SmtUtils.implies(mScript.getScript(), premise, conclusion), premise);
		assert checkResult(premise, conclusion, solution, false) : "Abduction failed";
		return solution;
	}

	/**
	 * Computes the solution to a given equivalence-abduction problem.
	 *
	 * @param lhs
	 *            The left-hand side of an invalid equivalence
	 * @param rhs
	 *            The right-hand side of an invalid equivalence
	 * @return a formula psi that entails equivalence of the input formulae, and is consistent with both of them. Null
	 *         if no such formula exists.
	 */
	public Term abduceEquivalence(final Term lhs, final Term rhs) {
		final Term formula = SmtUtils.binaryBooleanEquality(mScript.getScript(), lhs, rhs);
		final Term invariant = SmtUtils.or(mScript.getScript(), lhs, rhs);
		final Term solution = solveAbductionProblem(formula, invariant);
		assert checkResult(lhs, rhs, solution, true) : "Abduction failed";
		return solution;
	}

	private Term solveAbductionProblem(final Term formula, final Term invariant) {
		final Term quantifiedFormula = tryEliminateForall(mForbiddenVars, formula);

		final LBool sat = SmtUtils.checkSatTerm(mScript.getScript(),
				SmtUtils.and(mScript.getScript(), invariant, quantifiedFormula));
		if (sat != LBool.SAT) {
			return null;
		}

		final Term unsimplified =
				new MaximumUniversalSetComputation(mServices, mScript, quantifiedFormula, invariant, mCost)
						.getQuantifiedFormula();
		return SmtUtils.simplify(mScript, unsimplified, invariant, mServices, SimplificationTechnique.SIMPLIFY_DDA);
	}

	private Term tryEliminateForall(final Set<TermVariable> vars, final Term formula) {
		final Term quantified = SmtUtils.quantifier(mScript.getScript(), QuantifiedFormula.FORALL, vars, formula);
		final boolean eliminateLight = true;
		if (eliminateLight) {
			return PartialQuantifierElimination.eliminateLight(mServices, mScript, quantified);
		} else {
			return PartialQuantifierElimination.eliminate(mServices, mScript, quantified,
					SimplificationTechnique.SIMPLIFY_DDA);
		}
	}

	private boolean checkResult(final Term lhs, final Term rhs, final Term solution, final boolean equiv) {
		if (solution == null) {
			// nothing to check
			return true;
		}

		final LBool suff;
		if (equiv) {
			suff = SmtUtils.checkSatTerm(mScript.getScript(), SmtUtils.and(mScript.getScript(), solution,
					SmtUtils.binaryBooleanNotEquals(mScript.getScript(), lhs, rhs)));
			assert suff != LBool.SAT : "Abduction failed: solution " + solution + " does not imply equivalence of "
					+ lhs + " and " + rhs;
		} else {
			suff = SmtUtils.checkSatTerm(mScript.getScript(),
					SmtUtils.and(mScript.getScript(), lhs, solution, SmtUtils.not(mScript.getScript(), rhs)));
			assert suff != LBool.SAT : "Abduction failed: premise " + lhs + " and solution " + solution
					+ " do not imply conclusion " + rhs;
		}

		final LBool cons = SmtUtils.checkSatTerm(mScript.getScript(), SmtUtils.and(mScript.getScript(), lhs, solution));
		assert cons != LBool.UNSAT : "Abduction failed: LHS " + lhs + " and solution " + solution + " are inconsistent";

		return suff != LBool.SAT && cons != LBool.UNSAT;
	}
}
