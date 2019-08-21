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
package de.uni_freiburg.informatik.ultimate.lib.symbolicinterpretation.summarizers;

import java.util.HashMap;
import java.util.Map;
import java.util.function.Supplier;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IProgressAwareTimer;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.pathexpressions.regex.IRegex;
import de.uni_freiburg.informatik.ultimate.lib.pathexpressions.regex.Star;
import de.uni_freiburg.informatik.ultimate.lib.symbolicinterpretation.DagInterpreter;
import de.uni_freiburg.informatik.ultimate.lib.symbolicinterpretation.StarDagCache;
import de.uni_freiburg.informatik.ultimate.lib.symbolicinterpretation.SymbolicTools;
import de.uni_freiburg.informatik.ultimate.lib.symbolicinterpretation.domain.IDomain;
import de.uni_freiburg.informatik.ultimate.lib.symbolicinterpretation.domain.IDomain.ResultForAlteredInputs;
import de.uni_freiburg.informatik.ultimate.lib.symbolicinterpretation.fluid.IFluid;
import de.uni_freiburg.informatik.ultimate.lib.symbolicinterpretation.regexdag.FullOverlay;
import de.uni_freiburg.informatik.ultimate.lib.symbolicinterpretation.regexdag.IDagOverlay;
import de.uni_freiburg.informatik.ultimate.lib.symbolicinterpretation.regexdag.RegexDag;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Summarizes loops by iterating them until a fixpoint is reached. Fixpoint iteration works as in classical abstract
 * interpretation. Widening is used to ensure that the iteration eventually reaches a fixpoint.
 *
 * @author schaetzc@tf.uni-freiburg.de
 */
public class FixpointLoopSummarizer implements ILoopSummarizer {

	private final ILogger mLogger;
	private final Supplier<IProgressAwareTimer> mFixpointIterationTimeout;
	private final SymbolicTools mTools;
	private final IDomain mDomain;
	private final IFluid mFluid;
	private final DagInterpreter mDagIpr;
	private final StarDagCache mStarDagCache = new StarDagCache();
	private final Map<Pair<Star<IIcfgTransition<IcfgLocation>>, IPredicate>, IPredicate> mCache;

	public FixpointLoopSummarizer(final ILogger logger, final Supplier<IProgressAwareTimer> fixpointIterationTimeout,
			final SymbolicTools tools, final IDomain domain, final IFluid fluid, final DagInterpreter dagIpr) {
		mLogger = logger;
		mFixpointIterationTimeout = fixpointIterationTimeout;
		mTools = tools;
		mDomain = domain;
		mFluid = fluid;
		mDagIpr = dagIpr;
		mCache = new HashMap<>();
	}

	@Override
	public IPredicate summarize(final Star<IIcfgTransition<IcfgLocation>> regex, final IPredicate input) {
		final Pair<Star<IIcfgTransition<IcfgLocation>>, IPredicate> key = new Pair<>(regex, input);
		// TODO consider using cache more, for instance if loop is the same but
		// - input is a subset of a known input
		// - input is a superset of a known input, but a subset of any input from the iteration sequence.
		// Such re-use strategies work well as a WrapperLoopSummarzier
		return mCache.computeIfAbsent(key, this::summarizeInternal);
	}

	private IPredicate summarizeInternal(final Pair<Star<IIcfgTransition<IcfgLocation>>, IPredicate> starAndInput) {
		mLogger.debug("Computing new loop summary for input %.60s…", starAndInput.getValue());
		final IProgressAwareTimer timer = mFixpointIterationTimeout.get();

		final IRegex<IIcfgTransition<IcfgLocation>> starredRegex = starAndInput.getFirst().getInner();
		final RegexDag<IIcfgTransition<IcfgLocation>> dag = mStarDagCache.dagOf(starredRegex);
		// Enter calls are dead ends, therefore the inner regex of (…)* cannot contain enter calls
		final IDagOverlay<IIcfgTransition<IcfgLocation>> fullOverlay = new FullOverlay<>();
		IPredicate preState = starAndInput.getSecond();
		IPredicate postState = null;
		while (true) {
			if (!timer.continueProcessing()) {
				mLogger.warn("Timeout while computing loop summary. Using TOP as summary.");
				return mTools.top();
			}
			postState = mDagIpr.interpret(dag, fullOverlay, preState);
			if (mFluid.shallBeAbstracted(postState)) {
				postState = mDomain.alpha(postState);
			}
			final ResultForAlteredInputs postSubsetEqPre = mDomain.isSubsetEq(postState, preState);
			postState = postSubsetEqPre.getLhs();
			preState = postSubsetEqPre.getRhs();
			if (postSubsetEqPre.isTrue()) {
				break;
			}
			preState = mDomain.widen(preState, postState);
		}
		// not postState because postState ⊆ preState
		return preState;
	}

}
