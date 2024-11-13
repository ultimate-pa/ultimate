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

import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.tracecheck.ITraceCheckPreferences.AssertCodeBlockOrder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.tracecheck.ITraceCheckPreferences.AssertCodeBlockOrderType;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.singletracecheck.InterpolationTechnique;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PathProgramCache;

/**
 * Changes the assertion order based on the path program cache to detect and reduce loop unwindings.
 *
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 */
public class AssertionOrderModulation<LETTER> {

	private static final AssertCodeBlockOrder[] DEFAULT_ORDER = {

			AssertCodeBlockOrder.NOT_INCREMENTALLY,

			new AssertCodeBlockOrder(AssertCodeBlockOrderType.OUTSIDE_LOOP_FIRST1),

			new AssertCodeBlockOrder(AssertCodeBlockOrderType.OUTSIDE_LOOP_FIRST2),

			new AssertCodeBlockOrder(AssertCodeBlockOrderType.TERMS_WITH_SMALL_CONSTANTS_FIRST),

			new AssertCodeBlockOrder(AssertCodeBlockOrderType.INSIDE_LOOP_FIRST1),

			new AssertCodeBlockOrder(AssertCodeBlockOrderType.MIX_INSIDE_OUTSIDE), };

	private final AssertCodeBlockOrder[] mOrder;
	private final ILogger mLogger;
	private final PathProgramCache<LETTER> mPathProgramCache;

	public AssertionOrderModulation(final PathProgramCache<LETTER> pathProgramCache, final ILogger logger) {
		this(pathProgramCache, logger, DEFAULT_ORDER);
	}

	public AssertionOrderModulation(final PathProgramCache<LETTER> pathProgramCache, final ILogger logger,
			final AssertCodeBlockOrder... order) {
		mPathProgramCache = pathProgramCache;
		mLogger = logger;
		mOrder = order == null || order.length == 0 ? DEFAULT_ORDER : order;
	}

	/**
	 * Get the assertion order to use based on the current state of the {@link PathProgramCache}.
	 *
	 * TODO Should this take into account the control configuration sequence as well as the word?
	 *
	 * @param counterexample
	 *            counterexample
	 * @param interpolationTechnique
	 *            interpolation technique
	 * @return which assertion order to use
	 */
	public AssertCodeBlockOrder get(final Word<LETTER> counterexample,
			final InterpolationTechnique interpolationTechnique) {

		final int count = mPathProgramCache.getPathProgramCount(counterexample);
		final int index = toIndex(count - 1);
		final int oldIndex = toIndex(count - 2);

		final AssertCodeBlockOrder oldOrder = getOrder(interpolationTechnique, oldIndex);
		final AssertCodeBlockOrder newOrder = getOrder(interpolationTechnique, index);
		if (oldOrder != newOrder) {
			mLogger.info("Changing assertion order to " + newOrder);
		} else {
			mLogger.info("Keeping assertion order " + newOrder);
		}
		return newOrder;
	}

	private int toIndex(final int count) {
		if (count <= 0) {
			return 0;
		}
		return count % mOrder.length;
	}

	private AssertCodeBlockOrder getOrder(final InterpolationTechnique interpolationTechnique, final int index) {
		if (interpolationTechnique == null) {
			// if we do not compute interpolants, there is no need to assert incrementally
			return AssertCodeBlockOrder.NOT_INCREMENTALLY;
		}

		switch (interpolationTechnique) {
		case Craig_NestedInterpolation:
		case Craig_TreeInterpolation:
		case PDR:
			return AssertCodeBlockOrder.NOT_INCREMENTALLY;
		case ForwardPredicates:
		case BackwardPredicates:
		case FPandBP:
		case FPandBPonlyIfFpWasNotPerfect:
		case PathInvariants:
			return mOrder[index];
		default:
			throw new IllegalArgumentException("Unknown interpolation technique: " + interpolationTechnique);
		}
	}
}
