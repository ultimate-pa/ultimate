/*
 * Copyright (C) 2019 Claus Schätzle (schaetzc@tf.uni-freiburg.de)
 * Copyright (C) 2019 University of Freiburg
 *
 * This file is part of the ULTIMATE Library-Sifa plug-in.
 *
 * The ULTIMATE Library-Sifa plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Library-Sifa plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Library-Sifa plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Library-Sifa plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Library-Sifa plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.sifa.domain;

import java.util.Optional;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.SymbolicTools;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IDomain.ResultForAlteredInputs;

/**
 * Common approaches to implement {@link IDomain#isEqBottom(IPredicate)}
 * and {@link IDomain#isSubsetEq(IPredicate, IPredicate)}.
 *
 * @author schaetzc@tf.uni-freiburg.de
 */
public final class RelationCheckUtil {

	private RelationCheckUtil() {
		// objects of this class have no purpose
	}

	public static ResultForAlteredInputs isEqBottom_SolverAlphaSolver(
			final SymbolicTools tools, final IDomain domain, final IPredicate pred) {
		final ResultForAlteredInputs result = new ResultForAlteredInputs(pred, tools.bottom());
		for (int attempt = 0; attempt < 2; ++attempt) {
			if (SmtUtils.isFalseLiteral(result.mLhs.getFormula())) {
				result.mResult = true;
				return result;
			}
			final Optional<Boolean> solverResult = tools.isFalse(result.mLhs);
			if (solverResult.isPresent()) {
				result.mResult = solverResult.get();
				return result;
			}
			result.abstractLhs(domain::alpha);
		}
		throw new UnsupportedOperationException(String.format(
				"Solver couldn't answer isBottom for%noriginal:%n%s%nabstracted:%n%s",
				pred, result.mLhs));
	}

	public static ResultForAlteredInputs isSubsetEq_SolverAlphaSolver(
			final SymbolicTools tools, final IDomain domain, final IPredicate left, final IPredicate right) {
		final ResultForAlteredInputs result = new ResultForAlteredInputs(left, right);
		for (int attempt = 0; attempt < 2; ++attempt) {
			if (SmtUtils.isFalseLiteral(result.mLhs.getFormula()) || result.mLhs.equals(result.mRhs)) {
				result.mResult = true;
				return result;
			}
			final Optional<Boolean> solverResult = tools.implies(result.mLhs, result.mRhs);
			if (solverResult.isPresent()) {
				result.mResult = solverResult.get();
				return result;
			}
			// TODO maybe abstracting one side per attempt is also possible. Think about it carefully.
			result.abstractLhsAndRhs(domain::alpha);
		}
		throw new UnsupportedOperationException(String.format(
				"Solver couldn't answer isSubsetEq for%noriginal:%n%s%n%s%nabstracted:%n%s%n%s",
				left, right, result.mLhs, result.mRhs));
	}

}
