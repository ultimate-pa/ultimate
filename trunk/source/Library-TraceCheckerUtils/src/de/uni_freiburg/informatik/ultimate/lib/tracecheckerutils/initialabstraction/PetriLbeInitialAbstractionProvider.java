/*
 * Copyright (C) 2022 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2022 University of Freiburg
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
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
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
package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.initialabstraction;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.BoundedPetriNet;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence.IndependenceSettings;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.petrinetlbe.PetriNetLargeBlockEncoding;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.petrinetlbe.PetriNetLargeBlockEncoding.IPLBECompositionFactory;
import de.uni_freiburg.informatik.ultimate.util.statistics.AbstractStatisticsDataProvider;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsDataProvider;
import de.uni_freiburg.informatik.ultimate.util.statistics.StatisticsData;

/**
 * Transforms an initial abstraction by applying one-shot Petri LBE.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 * @param <L>
 *            The type of transitions
 */
public class PetriLbeInitialAbstractionProvider<L extends IIcfgTransition<?>>
		implements IInitialAbstractionProvider<L, BoundedPetriNet<L, IPredicate>> {

	private final IUltimateServiceProvider mServices;
	private final IInitialAbstractionProvider<L, BoundedPetriNet<L, IPredicate>> mUnderlying;
	private final IPLBECompositionFactory<L> mCompositionFactory;
	private final Class<L> mTransitionClazz;
	private final IndependenceSettings mIndependenceSettings;

	private final Statistics mStatistics;

	/**
	 * Create a new instance.
	 *
	 * @param underlying
	 *            The underlying provider whose provided instance is transformed
	 * @param services
	 *            Ultimate services used for Petri net LBE, and to report statistics
	 * @param transitionClazz
	 *            The class of transitions
	 * @param independenceSettings
	 *            Settings for the independence relation used by Petri net LBE
	 * @param compositionFactory
	 *            A factory to fuse transitions for Petri net LBE
	 * @param pluginId
	 *            A plugin ID under which statistics are reported
	 */
	public PetriLbeInitialAbstractionProvider(final IUltimateServiceProvider services,
			final IInitialAbstractionProvider<L, BoundedPetriNet<L, IPredicate>> underlying,
			final Class<L> transitionClazz, final IndependenceSettings independenceSettings,
			final IPLBECompositionFactory<L> compositionFactory) {
		mUnderlying = underlying;
		mServices = services;
		mTransitionClazz = transitionClazz;
		mIndependenceSettings = independenceSettings;
		mCompositionFactory = compositionFactory;

		mStatistics = new Statistics();
	}

	@Override
	public BoundedPetriNet<L, IPredicate> getInitialAbstraction(final IIcfg<? extends IcfgLocation> icfg,
			final Set<? extends IcfgLocation> errorLocs) throws AutomataLibraryException {
		final BoundedPetriNet<L, IPredicate> net = mUnderlying.getInitialAbstraction(icfg, errorLocs);

		final PetriNetLargeBlockEncoding<L> lbe = new PetriNetLargeBlockEncoding<>(mServices, icfg.getCfgSmtToolkit(),
				net, mIndependenceSettings, mCompositionFactory, mTransitionClazz);
		final BoundedPetriNet<L, IPredicate> lbecfg = lbe.getResult();

		mServices.getBacktranslationService().addTranslator(lbe.getBacktranslator());
		mStatistics.reportLiptonStatistics(lbe);

		return lbecfg;
	}

	@Override
	public IStatisticsDataProvider getStatistics() {
		return mStatistics;
	}

	private class Statistics extends AbstractStatisticsDataProvider {
		private static final String LIPTON_STATISTICS = "PetriNetLargeBlockEncoding benchmarks";
		private static final String UNDERLYING_STATISTICS = "Statistics of underlying abstraction provider";

		public Statistics() {
			forward(UNDERLYING_STATISTICS, mUnderlying::getStatistics);
		}

		private void reportLiptonStatistics(final PetriNetLargeBlockEncoding<?> pnlbe) {
			final var data = new StatisticsData();
			data.aggregateBenchmarkData(pnlbe.getStatistics());
			include(LIPTON_STATISTICS, () -> data);
		}
	}
}
