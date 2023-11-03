/*
 * Copyright (C) 2018 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2018 Lars Nitzke (lars.nitzke@outlook.com)
 * Copyright (C) 2018 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg;

import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.translation.ITranslator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.ModelCheckerUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgForkTransitionThreadCurrent;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgJoinTransitionThreadCurrent;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgForkThreadCurrentTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgForkThreadOtherTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transformations.BlockEncodingBacktranslator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transformations.IcfgDuplicator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * Takes a given {@link IIcfg} that has {@link IcfgForkThreadCurrentTransition}s but no
 * {@link IcfgForkThreadOtherTransition}s and adds {@link ThreadInstance}s to the {@link IIcfg}s
 * {@link ConcurrencyInformation}.
 *
 * Currently the number of thread instances is hardcoded. We have one thread instance per
 * {@link IcfgForkThreadCurrentTransition}s. But in the future we will also allow that the amount of thread instances
 * becomes a parameter of this class.
 *
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 */
public class IcfgPetrifier {
	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;

	private final BasicIcfg<IcfgLocation> mPetrifiedIcfg;
	private final BlockEncodingBacktranslator mBacktranslator;

	public IcfgPetrifier(final IUltimateServiceProvider services, final IIcfg<?> icfg,
			final int numberOfThreadInstances, final boolean addSelfLoops) {

		mServices = services;
		mLogger = services.getLoggingService().getLogger(ModelCheckerUtils.PLUGIN_ID);

		final BlockEncodingBacktranslator backtranslator =
				new BlockEncodingBacktranslator(IcfgEdge.class, Term.class, mLogger);
		final IcfgDuplicator duplicator =
				new IcfgDuplicator(mLogger, mServices, icfg.getCfgSmtToolkit().getManagedScript(), backtranslator);
		mPetrifiedIcfg = duplicator.copy(icfg, true);
		final Map<IIcfgTransition<IcfgLocation>, IIcfgTransition<IcfgLocation>> old2newEdgeMapping =
				duplicator.getOld2NewEdgeMapping();
		final ConcurrencyInformation concurrency = icfg.getCfgSmtToolkit().getConcurrencyInformation();
		final List<IIcfgForkTransitionThreadCurrent<IcfgLocation>> forks = concurrency.getThreadInstanceMap().keySet()
				.stream().map(x -> (IIcfgForkTransitionThreadCurrent<IcfgLocation>) old2newEdgeMapping.get(x))
				.collect(Collectors.toList());
		final List<IIcfgJoinTransitionThreadCurrent<IcfgLocation>> joins = concurrency.getJoinTransitions().stream()
				.map(x -> (IIcfgJoinTransitionThreadCurrent<IcfgLocation>) old2newEdgeMapping.get(x))
				.collect(Collectors.toList());
		final ThreadInstanceAdder adder = new ThreadInstanceAdder(mServices, addSelfLoops);
		final Map<IIcfgForkTransitionThreadCurrent<IcfgLocation>, List<ThreadInstance>> threadInstanceMap =
				ThreadInstanceAdder.constructThreadInstances(mPetrifiedIcfg, forks, numberOfThreadInstances);
		final Map<IIcfgForkTransitionThreadCurrent<IcfgLocation>, IcfgLocation> inUseErrorNodeMap = new HashMap<>();
		final CfgSmtToolkit cfgSmtToolkit = adder.constructNewToolkit(mPetrifiedIcfg.getCfgSmtToolkit(),
				threadInstanceMap, inUseErrorNodeMap, joins);
		mPetrifiedIcfg.setCfgSmtToolkit(cfgSmtToolkit);
		final List<ThreadInstance> instances = getAllInstances(threadInstanceMap);
		// Note that threadInstanceMap, newForkCurrentThreads, and
		// newJoinCurrentThreads are modified because the
		// ProcedureMultiplier might introduce new
		// IcfgForkThreadCurrentTransitions, namely in the case where
		// a forked transition contains a fork.
		ProcedureMultiplier.duplicateProcedures(mServices, mPetrifiedIcfg, instances, backtranslator, threadInstanceMap,
				forks, joins);
		fillErrorNodeMap(threadInstanceMap.keySet(), inUseErrorNodeMap);
		inUseErrorNodeMap.values().forEach(x -> mPetrifiedIcfg.addLocation(x, false, true, false, false, false));
		adder.connectThreadInstances(mPetrifiedIcfg, forks, joins, threadInstanceMap, inUseErrorNodeMap,
				backtranslator);

		final Set<Term> idVars = instances.stream().flatMap(x -> Arrays.stream(x.getIdVars())).map(IProgramVar::getTerm)
				.collect(Collectors.toSet());
		backtranslator.setVariableBlacklist(idVars);
		mBacktranslator = backtranslator;
	}

	private static void fillErrorNodeMap(final Set<IIcfgForkTransitionThreadCurrent<IcfgLocation>> forkTransitions,
			final Map<IIcfgForkTransitionThreadCurrent<IcfgLocation>, IcfgLocation> inUseErrorNodeMap) {
		int errorNodeId = 0;
		for (final IIcfgForkTransitionThreadCurrent<IcfgLocation> fork : forkTransitions) {
			final IcfgLocation errNode = ThreadInstanceAdder.constructErrorLocation(errorNodeId, fork);
			inUseErrorNodeMap.put(fork, errNode);
			errorNodeId++;
		}
	}

	public IIcfg<IcfgLocation> getPetrifiedIcfg() {
		return mPetrifiedIcfg;
	}

	public ITranslator<IIcfgTransition<IcfgLocation>, IIcfgTransition<IcfgLocation>, Term, Term, IcfgLocation, IcfgLocation>
			getBacktranslator() {
		return mBacktranslator;
	}

	public static List<ThreadInstance> getAllInstances(
			final Map<IIcfgForkTransitionThreadCurrent<IcfgLocation>, List<ThreadInstance>> threadInstanceMap) {
		return threadInstanceMap.values().stream().flatMap(Collection::stream).collect(Collectors.toList());
	}

}
