/*
 * Copyright (C) 2017 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2017 Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceAbstraction plug-in.
 *
 * The ULTIMATE TraceAbstraction plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceAbstraction plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceAbstraction plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceAbstraction plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceAbstraction plug-in grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction;

import java.util.List;
import java.util.Objects;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;

/**
 * {@link InterpolantSequenceWeakener} tries to weaken each predicate in a sequence of predicates s.t. it is still
 * inductive relative to a given sequence of letters.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 */
public abstract class InterpolantSequenceWeakener<HTC extends IHoareTripleChecker, P extends IPredicate, LETTER extends IAction> {

	private final List<P> mResult;
	private final ILogger mLogger;
	private final HTC mHtc;

	/**
	 * Default constructor. Generates result directly.
	 *
	 * @param logger
	 *            A logger instance.
	 * @param htc
	 *            The {@link IHoareTripleChecker} that should be used to perform the reduction.
	 * @param predicates
	 *            The sequence of {@link IPredicate}s that should be reduced.
	 * @param trace
	 *            The sequence of LETTERs that connects each predicate.
	 */
	public InterpolantSequenceWeakener(final ILogger logger, final HTC htc, final List<P> predicates,
			final List<LETTER> trace) {
		mLogger = logger;
		mHtc = Objects.requireNonNull(htc);
		final List<LETTER> checkedTrace = Objects.requireNonNull(trace, "trace is null");
		final List<P> checkedPredicates = Objects.requireNonNull(predicates, "predicates are null");
		assert checkedTrace.size() == checkedPredicates.size()
				+ 1 : "trace and predicates do not match, their size is incorrect";
		mResult = generateResult(checkedPredicates, checkedTrace);
		assert mResult.size() == predicates.size();
	}

	private List<P> generateResult(final List<P> predicates, final List<LETTER> list) {
		// TODO Auto-generated method stub
		return null;
	}

	/**
	 * @return the (hopefully) weakened sequence of predicates that is still inductive.
	 */
	public List<P> getResult() {
		return mResult;
	}
}
