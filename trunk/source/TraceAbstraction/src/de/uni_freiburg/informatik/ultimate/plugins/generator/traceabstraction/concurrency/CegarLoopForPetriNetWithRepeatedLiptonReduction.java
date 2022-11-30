/*
 * Copyright (C) 2021 Dennis Wölfing
 * Copyright (C) 2021-2022 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2021-2022 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceAbstraction plug-in.
 *
 * The ULTIMATE TraceAbstractionConcurrent plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceAbstractionConcurrent plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceAbstractionConcurrent plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceAbstractionConcurrent plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceAbstractionConcurrent plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.concurrency;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.CachedIndependenceRelation.IIndependenceCache;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.DefaultIndependenceCache;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNetNot1SafeException;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.BoundedPetriNet;
import de.uni_freiburg.informatik.ultimate.core.lib.results.StatisticsResult;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.debugidentifiers.DebugIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.petrinetlbe.ICompositionFactoryWithBacktranslator;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.petrinetlbe.PetriNetLargeBlockEncoding;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PredicateFactoryRefinement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;

/**
 * A CEGAR loop for Petri nets that repeatedly applies Lipton Reduction after each iteration.
 *
 * @author Dennis Wölfing
 *
 * @param <L>
 *            The type of the letters of the transitions.
 */
public class CegarLoopForPetriNetWithRepeatedLiptonReduction<L extends IIcfgTransition<?>>
		extends CegarLoopForPetriNet<L> {

	private final ICompositionFactoryWithBacktranslator<L> mCompositionFactory;
	private final IIndependenceCache<?, L> mIndependenceCache = new DefaultIndependenceCache<>();

	/**
	 * Construct the CEGAR loop.
	 *
	 * @param name
	 * @param rootNode
	 * @param csToolkit
	 * @param predicateFactory
	 * @param taPrefs
	 * @param errorLocs
	 * @param services
	 * @param compositionFactory
	 * @param transitionClazz
	 */
	public CegarLoopForPetriNetWithRepeatedLiptonReduction(final DebugIdentifier name,
			final BoundedPetriNet<L, IPredicate> initialAbstraction, final IIcfg<?> rootNode,
			final CfgSmtToolkit csToolkit, final PredicateFactory predicateFactory, final TAPreferences taPrefs,
			final Set<IcfgLocation> errorLocs, final IUltimateServiceProvider services,
			final ICompositionFactoryWithBacktranslator<L> compositionFactory, final Class<L> transitionClazz,
			final PredicateFactoryRefinement stateFactoryForRefinement) {
		super(name, initialAbstraction, rootNode, csToolkit, predicateFactory, taPrefs, errorLocs, services,
				transitionClazz, stateFactoryForRefinement);
		mCompositionFactory = compositionFactory;
	}

	@Override
	protected boolean refineAbstraction() throws AutomataLibraryException {
		final boolean result = super.refineAbstraction();
		mAbstraction = applyLargeBlockEncoding(mAbstraction);
		return result;
	}

	protected BoundedPetriNet<L, IPredicate> applyLargeBlockEncoding(final BoundedPetriNet<L, IPredicate> cfg)
			throws AutomataOperationCanceledException, PetriNetNot1SafeException {
		final long start_time = System.currentTimeMillis();
		final PetriNetLargeBlockEncoding<L> lbe = new PetriNetLargeBlockEncoding<>(getServices(),
				mIcfg.getCfgSmtToolkit(), cfg, mPref.lbeIndependenceSettings(), mCompositionFactory, mPredicateFactory,
				mIndependenceCache, mFinitePrefixOfAbstraction, mCounterexampleCache.getCounterexample());
		final BoundedPetriNet<L, IPredicate> lbecfg = lbe.getResult();
		getServices().getBacktranslationService().addTranslator(mCompositionFactory.getBacktranslator());

		final var adaptedRun = lbe.getAdaptedRun();
		if (adaptedRun != null) {
			mCounterexampleCache.setCounterexample(adaptedRun);
		}

		final long end_time = System.currentTimeMillis();
		final long difference = end_time - start_time;
		mLogger.info("Time needed for LBE in milliseconds: " + difference);

		getServices().getResultService().reportResult(Activator.PLUGIN_ID, new StatisticsResult<>(Activator.PLUGIN_NAME,
				"PetriNetLargeBlockEncoding benchmarks", lbe.getStatistics()));
		return lbecfg;
	}
}
