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

import java.util.Collection;
import java.util.HashSet;
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
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

/**
 * Takes a given {@link IIcfg} that has {@link IcfgForkThreadCurrentTransition}s
 * but no {@link IcfgForkThreadOtherTransition}s and adds
 * {@link ThreadInstance}s to the {@link IIcfg}s {@link ConcurrencyInformation}.
 *
 * Currently the number of thread instances is hardcoded. We have one thread
 * instance per {@link IcfgForkThreadCurrentTransition}s. But in the future we
 * will also allow that the amount of thread instances becomes a parameter of
 * this class.
 *
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 */
public class IcfgPetrifier {

	public enum IcfgConstructionMode { CHECK_THREAD_INSTANCE_SUFFICIENCY, ASSUME_THREAD_INSTANCE_SUFFICIENCY };

	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;

	private final IIcfg<IcfgLocation> mPetrifiedIcfg;
	private final BlockEncodingBacktranslator mBacktranslator;


	public IcfgPetrifier(final IUltimateServiceProvider services, final IIcfg<?> icfg,
			final IcfgConstructionMode icfgConstructionMode) {

		mServices = services;
		mLogger = services.getLoggingService().getLogger(ModelCheckerUtils.PLUGIN_ID);

		final Collection<IIcfgForkTransitionThreadCurrent<IcfgLocation>> forkCurrentThreads = icfg.getCfgSmtToolkit()
				.getConcurrencyInformation().getThreadInstanceMap().keySet();
		final Collection<IIcfgJoinTransitionThreadCurrent<IcfgLocation>> joinCurrentThreads = icfg.getCfgSmtToolkit()
				.getConcurrencyInformation().getJoinTransitions();

		final BlockEncodingBacktranslator backtranslator = new BlockEncodingBacktranslator(IcfgEdge.class, Term.class,
				mLogger);
		final IcfgDuplicator duplicator = new IcfgDuplicator(mLogger, mServices,
				icfg.getCfgSmtToolkit().getManagedScript(), backtranslator);
		mPetrifiedIcfg = duplicator.copy(icfg);
		final Map<IIcfgTransition<IcfgLocation>, IIcfgTransition<IcfgLocation>> old2newEdgeMapping = duplicator
				.getOld2NewEdgeMapping();
		final List<IIcfgForkTransitionThreadCurrent<IcfgLocation>> newForkCurrentThreads = forkCurrentThreads.stream()
				.map(old2newEdgeMapping::get).map(x -> (IIcfgForkTransitionThreadCurrent<IcfgLocation>) x)
				.collect(Collectors.toList());
		final List<IIcfgJoinTransitionThreadCurrent<IcfgLocation>> newJoinCurrentThreads = joinCurrentThreads.stream()
				.map(old2newEdgeMapping::get).map(x -> (IIcfgJoinTransitionThreadCurrent<IcfgLocation>) x)
				.collect(Collectors.toList());
		final ThreadInstanceAdder adder = new ThreadInstanceAdder(mServices);
		final boolean addThreadInUseViolationVariablesAndErrorLocation = (icfgConstructionMode == IcfgConstructionMode.CHECK_THREAD_INSTANCE_SUFFICIENCY);
		final Map<IIcfgForkTransitionThreadCurrent<IcfgLocation>, ThreadInstance> threadInstanceMap = adder
				.constructThreadInstances(mPetrifiedIcfg, newForkCurrentThreads,
						addThreadInUseViolationVariablesAndErrorLocation);
		final CfgSmtToolkit cfgSmtToolkit = adder.constructNewToolkit(mPetrifiedIcfg.getCfgSmtToolkit(),
				threadInstanceMap, newJoinCurrentThreads, addThreadInUseViolationVariablesAndErrorLocation);
		((BasicIcfg<IcfgLocation>) mPetrifiedIcfg).setCfgSmtToolkit(cfgSmtToolkit);
		final HashRelation<String, String> copyDirectives = ProcedureMultiplier
				.generateCopyDirectives(threadInstanceMap.values());
		new ProcedureMultiplier(mServices, (BasicIcfg<IcfgLocation>) mPetrifiedIcfg, copyDirectives, backtranslator,
				threadInstanceMap, newForkCurrentThreads, newJoinCurrentThreads);
		if (icfgConstructionMode == IcfgConstructionMode.CHECK_THREAD_INSTANCE_SUFFICIENCY) {
			ThreadInstanceAdder.addInUseErrorLocations((BasicIcfg<IcfgLocation>) mPetrifiedIcfg,
					threadInstanceMap.values());
		}

		final boolean addThreadInUseViolationEdges = (icfgConstructionMode == IcfgConstructionMode.CHECK_THREAD_INSTANCE_SUFFICIENCY);
		adder.connectThreadInstances(mPetrifiedIcfg, newForkCurrentThreads, newJoinCurrentThreads,
				threadInstanceMap, backtranslator, addThreadInUseViolationEdges);

		final Set<Term> auxiliaryThreadVariables = collectAxiliaryThreadVariables(threadInstanceMap.values(), addThreadInUseViolationEdges);
		backtranslator.setVariableBlacklist(auxiliaryThreadVariables);
		mBacktranslator = backtranslator;
	}


	private static Set<Term> collectAxiliaryThreadVariables(final Collection<ThreadInstance> values,
			final boolean addThreadInUseViolationEdges) {
		final Set<Term> result = new HashSet<>();
		for (final ThreadInstance ti : values) {
			if (addThreadInUseViolationEdges) {
				result.add(ti.getInUseVar().getTerm());
			}
			for (final IProgramNonOldVar idVar : ti.getIdVars()) {
				result.add(idVar.getTerm());
			}
		}
		return result;
	}


	public IIcfg<IcfgLocation> getPetrifiedIcfg() {
		return mPetrifiedIcfg;
	}


	public ITranslator<IIcfgTransition<IcfgLocation>, IIcfgTransition<IcfgLocation>, Term, Term, IcfgLocation, IcfgLocation> getBacktranslator() {
		return mBacktranslator;
	}



}
