/*
 * Copyright (C) 2021 Dennis Wölfing
 * Copyright (C) 2021 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.petrinetlbe;

import java.util.HashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.automata.partialorder.IStuckPlaceChecker;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Util;

/**
 * Checks whether execution might get stuck in a place.
 *
 * @param <L>
 *            The type of the letters in the Petri net.
 * @param <P>
 *            The type of the places in the Petri net.
 */
public class StuckPlaceChecker<L extends IIcfgTransition<?>, P> implements IStuckPlaceChecker<L, P> {
	private final ILogger mLogger;
	private final IUltimateServiceProvider mServices;
	private final ManagedScript mScript;
	private final Map<P, Boolean> mCache;

	/**
	 * Creates a StuckPlaceChecker.
	 *
	 * @param logger
	 *            A logging service.
	 * @param services
	 *            A {@link IUltimateServiceProvider} instance.
	 * @param script
	 *            A ManagedScript.
	 */
	public StuckPlaceChecker(final ILogger logger, final IUltimateServiceProvider services,
			final ManagedScript script) {
		mLogger = logger;
		mServices = services;
		mScript = script;
		mCache = new HashMap<>();
	}

	/**
	 * Checks whether the execution might get stuck in the given place. We are caching the result to avoid rerunning the
	 * SMT solver. The cached results are still correct after applying the sequence rule in LiptonReduction even if the
	 * composition of two transitions was discarded due two duplicate pre-/post-conditions. This is because there will
	 * always be other non-discarded executable transitions as otherwise mightGetStuck would have returned true for the
	 * place where composition happened and therefore the transitions would not have been composed.
	 */
	@Override
	public boolean mightGetStuck(final IPetriNet<L, P> petriNet, final P place) {
		if (mCache.containsKey(place)) {
			return mCache.get(place);
		}

		final UnmodifiableTransFormula[] tfs = petriNet.getSuccessors(place).stream()
				.map(t -> t.getSymbol().getTransformula()).toArray(UnmodifiableTransFormula[]::new);
		final UnmodifiableTransFormula tf;
		try {
			tf = TransFormulaUtils.constructRemainderGuard(mLogger, mServices, mScript, tfs);
		} catch (final UnsupportedOperationException e) {
			return true;
		}

		final LBool result = Util.checkSat(mScript.getScript(), tf.getFormula());

		mCache.put(place, result != LBool.UNSAT);
		return result != LBool.UNSAT;
	}
}
