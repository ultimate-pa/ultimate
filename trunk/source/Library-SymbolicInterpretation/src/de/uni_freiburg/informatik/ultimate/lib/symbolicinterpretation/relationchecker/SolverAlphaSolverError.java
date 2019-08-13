/*
 * Copyright (C) 2019 Claus Schätzle (schaetzc@tf.uni-freiburg.de)
 * Copyright (C) 2019 University of Freiburg
 *
 * This file is part of the ULTIMATE Library-SymbolicInterpretation plug-in.
 *
 * The ULTIMATE Library-SymbolicInterpretation plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Library-SymbolicInterpretation plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Library-SymbolicInterpretation plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Library-SymbolicInterpretation plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Library-SymbolicInterpretation plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.symbolicinterpretation.relationchecker;

import java.util.Optional;

import de.uni_freiburg.informatik.ultimate.lib.symbolicinterpretation.SymbolicTools;
import de.uni_freiburg.informatik.ultimate.lib.symbolicinterpretation.domain.IDomain;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;

/**
 * Tries to check relations using the solver.
 * In case of UNKNOWN results abstracts the operands applies the solver a second time.
 * Throws an exception in case the second solver call returns UNKNOWN too.
 *
 * @author schaetzc@tf.uni-freiburg.de
 */
public class SolverAlphaSolverError implements IRelationChecker {

	private final SymbolicTools mTools;
	private final IDomain mDomain;

	public SolverAlphaSolverError(final SymbolicTools tools, final IDomain domain) {
		mTools = tools;
		mDomain = domain;
	}

	@Override
	public LhsRelRhs isEqBottom(final IPredicate pred) {
		final LhsRelRhs result = new LhsRelRhs(pred, mTools.bottom());
		for (int attempt = 0; attempt < 2; ++attempt) {
			if (SmtUtils.isFalseLiteral(result.mLhs.getFormula())) {
				result.mResult = true;
				return result;
			}
			final Optional<Boolean> solverResult = mTools.isFalse(result.mLhs);
			if (solverResult.isPresent()) {
				result.mResult = solverResult.get();
				return result;
			}
			result.abstractLhs(mDomain::alpha);
		}
		throw new UnsupportedOperationException(String.format(
				"Solver couldn't answer isBottom for\noriginal:\n%s\nabstracted:\n%s",
				pred, result.mLhs));
	}

	@Override
	public LhsRelRhs isSubsetEq(final IPredicate left, final IPredicate right) {
		final LhsRelRhs result = new LhsRelRhs(left, right);
		for (int attempt = 0; attempt < 2; ++attempt) {
			if (SmtUtils.isFalseLiteral(result.mLhs.getFormula()) || result.mLhs.equals(result.mRhs)) {
				result.mResult = true;
				return result;
			}
			final Optional<Boolean> solverResult = mTools.implies(result.mLhs, result.mRhs);
			if (solverResult.isPresent()) {
				result.mResult = solverResult.get();
				return result;
			}
			// TODO maybe abstracting one side per attempt is also possible. Think about it carefully.
			result.abstractLhsAndRhs(mDomain::alpha);
		}
		throw new UnsupportedOperationException(String.format(
				"Solver couldn't answer isSubsetEq for\noriginal:\n%s\n%s\nabstracted:\n%s\n%s",
				left, right, result.mLhs, result.mRhs));
	}

	@Override
	public boolean underapproxIsBottom(IPredicate pred) {
		for (int attempt = 0; attempt < 2; ++attempt) {
			if (SmtUtils.isFalseLiteral(pred.getFormula())) {
				return true;
			}
			pred = mDomain.alpha(pred);
		}
		return false;
	}

	@Override
	public boolean underapproxIsSubsetEq(final IPredicate left, final IPredicate right) {
		// TODO consider using abstraction when this method is needed
		return left.getClosedFormula().equals(right.getClosedFormula()) || underapproxIsBottom(left);
	}

}
