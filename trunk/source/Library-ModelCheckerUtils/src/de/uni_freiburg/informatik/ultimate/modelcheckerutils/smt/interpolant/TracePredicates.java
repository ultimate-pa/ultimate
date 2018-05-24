/*
 * Copyright (C) 2014-2018 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2017-2018 Christian Schilling (schillic@informatik.uni-freiburg.de)
 * Copyright (C) 2015-2018 University of Freiburg
 *
 * This file is part of the ULTIMATE ModelCheckerUtils Library.
 *
 * The ULTIMATE ModelCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ModelCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ModelCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ModelCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ModelCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.interpolant;

import java.util.Arrays;
import java.util.Collections;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.tracecheck.ITraceCheck;

/**
 * Wrapper for a sequence of {@link IPredicate}s along a trace, including the precondition and postcondition.
 * <p>
 * The sequence of interpolants returned by a {@link ITraceCheck} contains neither the precondition nor the
 * postcondition of the trace check. This auxiliary class allows one to access the precondition via the index {@code 0}
 * and to access the postcondition via the index {@code length+1}. All other indices are shifted by one. In the future
 * we might also use negative indices to access pending contexts (therefore you should not catch the error thrown by the
 * getInterpolant method).
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 */
public class TracePredicates {
	private final IPredicate mPrecondition;
	private final IPredicate mPostcondition;
	private final List<IPredicate> mPredicates;

	/**
	 * @param interpolantGenerator
	 *            Interpolant generator.
	 */
	public TracePredicates(final IInterpolantGenerator<? extends IAction> interpolantGenerator) {
		if (interpolantGenerator.getInterpolants() == null) {
			throw new AssertionError(
					"We can only build an interpolant automaton for which interpolants were computed.");
		}
		mPrecondition = interpolantGenerator.getPrecondition();
		mPostcondition = interpolantGenerator.getPostcondition();
		mPredicates = Arrays.asList(interpolantGenerator.getInterpolants());
	}

	/**
	 * @param precondition
	 *            Precondition.
	 * @param postcondition
	 *            postcondition
	 * @param predicates
	 *            sequence of predicates
	 */
	public TracePredicates(final IPredicate precondition, final IPredicate postcondition,
			final List<IPredicate> predicates) {
		mPrecondition = precondition;
		mPostcondition = postcondition;
		mPredicates = predicates;
	}

	/**
	 * @param pos
	 *            Position.
	 * @return predicate at the given position
	 */
	public IPredicate getPredicate(final int pos) {
		if (pos < 0) {
			throw new AssertionError("index beyond precondition");
		} else if (pos == 0) {
			return mPrecondition;
		} else if (pos <= mPredicates.size()) {
			return mPredicates.get(pos - 1);
		} else if (pos == mPredicates.size() + 1) {
			return mPostcondition;
		} else {
			throw new AssertionError("index beyond postcondition");
		}
	}

	public List<IPredicate> getPredicates() {
		return Collections.unmodifiableList(mPredicates);
	}

	public IPredicate getPrecondition() {
		return mPrecondition;
	}

	public IPredicate getPostcondition() {
		return mPostcondition;
	}
}
