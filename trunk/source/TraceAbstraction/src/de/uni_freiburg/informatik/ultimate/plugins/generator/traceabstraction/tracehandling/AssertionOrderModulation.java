/*
 * Copyright (C) 2016 Christian Schilling (schillic@informatik.uni-freiburg.de)
 * Copyright (C) 2017 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2016-2017 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling;

import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.tracecheck.ITraceCheckPreferences.AssertCodeBlockOrder;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PathProgramCache;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.InterpolationTechnique;

/**
 * Changes the assertion order based on the path program cache to detect and reduce loop unwindings.
 *
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 */
public class AssertionOrderModulation<LETTER> {

	private static final AssertCodeBlockOrder[] DEFAULT_ORDER = {

			AssertCodeBlockOrder.NOT_INCREMENTALLY,

			AssertCodeBlockOrder.OUTSIDE_LOOP_FIRST1,

			AssertCodeBlockOrder.OUTSIDE_LOOP_FIRST2,

			AssertCodeBlockOrder.TERMS_WITH_SMALL_CONSTANTS_FIRST,

			AssertCodeBlockOrder.INSIDE_LOOP_FIRST1,

			AssertCodeBlockOrder.MIX_INSIDE_OUTSIDE, };

	private final AssertCodeBlockOrder[] mOrder;
	private final ILogger mLogger;
	private final PathProgramCache<LETTER> mPathProgramCache;
	private int mCurrentIndex;

	public AssertionOrderModulation(final PathProgramCache<LETTER> pathProgramCache, final ILogger logger) {
		this(pathProgramCache, logger, DEFAULT_ORDER);
	}

	public AssertionOrderModulation(final PathProgramCache<LETTER> pathProgramCache, final ILogger logger,
			final AssertCodeBlockOrder... order) {
		assert order != null && order.length > 0 : "Order is needed";
		mPathProgramCache = pathProgramCache;
		mLogger = logger;
		mCurrentIndex = 0;
		mOrder = order;
	}

	/**
	 * Get the assertion order to use based on the current state of the {@link PathProgramCache}.
	 *
	 * @param counterexample
	 *            counterexample
	 * @param interpolationTechnique
	 *            interpolation technique
	 * @return which assertion order to use
	 */
	public AssertCodeBlockOrder get(final IRun<LETTER, IPredicate, ?> counterexample,
			final InterpolationTechnique interpolationTechnique) {

		final int count = mPathProgramCache.getPathProgramCount(counterexample);

		final AssertCodeBlockOrder oldOrder = mOrder[mCurrentIndex];
		if (count == 0) {
			mCurrentIndex = 0;
		} else {
			mCurrentIndex = (count - 1) % mOrder.length;
		}

		final AssertCodeBlockOrder newOrder = getOrder(interpolationTechnique);

		if (oldOrder != newOrder) {
			mLogger.info("Changing assertion order to " + newOrder);
		} else {
			mLogger.info("Keeping assertion order " + newOrder);
		}

		return getOrder(interpolationTechnique);
	}

	private AssertCodeBlockOrder getOrder(final InterpolationTechnique interpolationTechnique) {
		if (interpolationTechnique == null) {
			// if we do not compute interpolants, there is no need to assert incrementally
			return AssertCodeBlockOrder.NOT_INCREMENTALLY;
		}

		switch (interpolationTechnique) {
		case Craig_NestedInterpolation:
		case Craig_TreeInterpolation:
		case PDR:
			mLogger.info(interpolationTechnique + " forces the order to " + AssertCodeBlockOrder.NOT_INCREMENTALLY);
			return AssertCodeBlockOrder.NOT_INCREMENTALLY;
		case ForwardPredicates:
		case BackwardPredicates:
		case FPandBP:
		case FPandBPonlyIfFpWasNotPerfect:
		case PathInvariants:
			return mOrder[mCurrentIndex];
		default:
			throw new IllegalArgumentException("Unknown interpolation technique: " + interpolationTechnique);
		}
	}
}
