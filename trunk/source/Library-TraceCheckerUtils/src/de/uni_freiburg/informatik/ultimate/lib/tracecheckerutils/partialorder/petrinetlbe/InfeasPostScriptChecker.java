/*
 * Copyright (C) 2021 Dennis Wölfing
 * Copyright (C) 2021 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2021 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceCheckerUtils Library.
 *
 * The ULTIMATE TraceCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.petrinetlbe;

import java.util.HashMap;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.partialorder.IPostScriptChecker;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.Transition;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Util;

/**
 * Checks whether a given set of transitions is a post-script of the language INFEAS of infeasible traces.
 *
 * For the definition of post-scripts, see {@link IPostScriptChecker}.
 *
 * In program verification, we consider the language INFEAS of all infeasible traces. There, firing a transition labeled
 * only with an assignment or havoc of a variable (in general, any statement with guard "true"), does not make a trace
 * infeasible. Hence a set of transitions labeled by such statements is a post-script of INFEAS.
 *
 * @param <L>
 *            The type of the letters in the Petri net.
 * @param <P>
 *            The type of the places in the Petri net.
 */
public class InfeasPostScriptChecker<L extends IIcfgTransition<?>, P> implements IPostScriptChecker<L, P> {
	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private final ManagedScript mScript;

	// TODO move caching out of mightGetStuck (don't know yet where to)
	private final Map<P, Boolean> mCache = new HashMap<>();

	/**
	 * Creates a new instance.
	 *
	 * @param services
	 *            A {@link IUltimateServiceProvider} instance.
	 * @param script
	 *            A {@link ManagedScript} used for SMT queries.
	 */
	public InfeasPostScriptChecker(final IUltimateServiceProvider services, final ManagedScript script) {
		mServices = services;
		mLogger = services.getLoggingService().getLogger(InfeasPostScriptChecker.class);
		mScript = script;
	}

	/**
	 * Checks whether the execution might get stuck in the given place.
	 *
	 * TODO Dominik 20221129: I don't understand the explanation below.
	 *
	 * We are caching the result to avoid rerunning the SMT solver. The cached results are still correct after applying
	 * the sequence rule in LiptonReduction even if the composition of two transitions was discarded due two duplicate
	 * pre-/post-conditions. This is because there will always be other non-discarded executable transitions as
	 * otherwise mightGetStuck would have returned true for the place where composition happened and therefore the
	 * transitions would not have been composed.
	 *
	 * TODO Dominik 20221129: I also don't understand why caching is safe even in cases where nothing is discarded
	 *
	 * @deprecated Use {@link #isPostScript(IPetriNet, Set)} as soon as caching is sorted out
	 */
	@Deprecated(since = "2021-09-13")
	@Override
	public boolean mightGetStuck(final IPetriNet<L, P> petriNet, final P place) {
		if (mCache.containsKey(place)) {
			return mCache.get(place);
		}

		final boolean result = !isPostScript(petriNet, petriNet.getSuccessors(place));
		mCache.put(place, result);
		return result;
	}

	@Override
	public boolean isPostScript(final IPetriNet<L, P> net, final Set<Transition<L, P>> transitions) {
		final UnmodifiableTransFormula[] tfs =
				transitions.stream().map(t -> t.getSymbol().getTransformula()).toArray(UnmodifiableTransFormula[]::new);
		try {
			final UnmodifiableTransFormula tf =
					TransFormulaUtils.constructRemainderGuard(mLogger, mServices, mScript, tfs);
			final LBool result = Util.checkSat(mScript.getScript(), tf.getFormula());
			return result == LBool.UNSAT;
		} catch (final UnsupportedOperationException e) {
			// May be thrown by constructRemainderGuard if some aux vars cannot be eliminated.
			return false;
		}
	}
}
