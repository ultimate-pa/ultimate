/*
 * Copyright (C) 2026 University of Freiburg
 *
 * This file is part of the ULTIMATE Library-Sifa plug-in.
 *
 * The ULTIMATE Library-Sifa plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Library-Sifa plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Library-Sifa plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Library-Sifa plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Library-Sifa plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.setup;

import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.bucketdomain.AbstractLocationPartitionedDomain;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.cfg.LocationAbstraction;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.ghostvariables.GhostVariableManager;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.GroupedInterferenceFactory;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.InterferenceEdgeCollector;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.methods.guardedupdate.GuardedUpdateInterferenceFactory;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.methods.poststate.PostStateInterferenceFactory;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.methods.strongestpostcondition.StrongestPostconditionInterferenceFactory;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.lockset.MustLocksetAnalysis;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.lockset.publish.PublishOnAcquire;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.relations.PrimedDefaultIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.relations.RelationalPredicatePostcondition;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.relations.TransFormulaToInterferencePredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.setup.ThreadModularSifaSettings.InterferenceApplicatorType;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.setup.threadactivity.ThreadActivityPreanalysis;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.setup.threadactivity.ThreadForkGraph;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.threadanalysis.ConcurrentSymbolicTools;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IDomain;
import de.uni_freiburg.informatik.ultimate.lib.sifa.statistics.SifaStats;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;

public final class ThreadModularSetup {
	private final IUltimateServiceProvider mServices;
	private final IIcfg<IcfgLocation> mIcfg;
	private final ThreadModularSifaSettings mSettings;
	private final PrimedDefaultIcfgSymbolTable mSymbolTable;
	private final ThreadForkGraph mForkGraph;
	private final Set<String> mJoinedThreads;
	private final ThreadActivityPreanalysis mActivityPreanalysis;
	private final MustLocksetAnalysis mLocksetInfo;
	private final Map<IcfgLocation, Integer> mAbstractLocationIds;
	private final Map<String, Set<IcfgLocation>> mPreForkSourcesByThread;
	private final GhostVariableManager mGhostVariables;

	public ThreadModularSetup(final IUltimateServiceProvider services, final IIcfg<IcfgLocation> icfg,
			final ThreadModularSifaSettings settings) {
		mServices = services;
		mIcfg = icfg;
		mSettings = settings;
		final var toolkit = icfg.getCfgSmtToolkit();
		mSymbolTable = new PrimedDefaultIcfgSymbolTable(toolkit.getSymbolTable(), toolkit.getProcedures(),
				toolkit.getManagedScript());
		final ILogger logger = services.getLoggingService().getLogger(ThreadModularSetup.class);
		mForkGraph = ThreadForkGraph.compute(icfg);
		mJoinedThreads = settings.joinPrecision() ? Set.copyOf(mForkGraph.getMatchedJoins().values()) : Set.of();
		if (settings.joinPrecision()) {
			logger.info("Join precision enabled, joined threads: %s", mJoinedThreads);
		}
		mActivityPreanalysis = ThreadActivityPreanalysis.compute(icfg, mForkGraph, settings.joinPrecision());
		final boolean needsLocksetAnalysis = settings.locksetAwareInterference() || settings.publishOnAcquire();
		mLocksetInfo = needsLocksetAnalysis
				? MustLocksetAnalysis.create(icfg, mActivityPreanalysis)
				: MustLocksetAnalysis.disabled();
		mAbstractLocationIds = Map.copyOf(computeLocationIds(settings, services, icfg, interferenceLocksetInfo()));
		mPreForkSourcesByThread = mForkGraph.computePreForkSourcesByThread(icfg,
				mActivityPreanalysis.getMultiForkedThreads());
		mGhostVariables = GhostVariableManager.create(toolkit.getManagedScript(), mAbstractLocationIds,
				new LinkedHashSet<>(mForkGraph.getThreadIds()), icfg.getProcedureEntryNodes(), mSymbolTable,
				mActivityPreanalysis.getMultiForkedThreads());
	}

	public ConcurrentSymbolicTools createTools(final SifaStats stats, final SimplificationTechnique simplification) {
		return new ConcurrentSymbolicTools(mServices, stats, mIcfg, simplification, mSymbolTable, mSettings,
				mGhostVariables, mActivityPreanalysis, mLocksetInfo, mForkGraph);
	}

	public SetupResult initialize(final IDomain baseDomain, final ConcurrentSymbolicTools tools) {
		final var factory = tools.getFactory();
		final ManagedScript script = tools.getManagedScript();
		final ILogger logger = mServices.getLoggingService().getLogger(ThreadModularSetup.class);
		final PublishOnAcquire mutexInvariants = mSettings.publishOnAcquire()
				? PublishOnAcquire.discover(mIcfg, mLocksetInfo, ThreadForkGraph.MAIN_THREAD, mActivityPreanalysis,
						mServices, script, factory)
				: PublishOnAcquire.disabled();
		if (mSettings.publishOnAcquire()) {
			logger.info("Publish-on-acquire enabled (protected globals discovered: %s)", !mutexInvariants.isEmpty());
		}
		final AbstractLocationPartitionedDomain partitionedDomain = mSettings.useBuckets()
				? AbstractLocationPartitionedDomain.create(baseDomain, tools,
						mGhostVariables.getLocationTermVariablesByThread(), mSettings.maxBuckets(),
						mSettings.maxDisjunctsPerBucket())
				: null;
		if (partitionedDomain != null) {
			logger.info("Abstract-location partitioned domain enabled");
		}
		final IDomain domain = partitionedDomain != null ? partitionedDomain : baseDomain;
		final var translator = new TransFormulaToInterferencePredicate(mServices, script, factory, mSymbolTable,
				mGhostVariables, mAbstractLocationIds, mIcfg.getProcedureEntryNodes());
		final RelationalPredicatePostcondition postcondition = new RelationalPredicatePostcondition(mServices, script,
				factory, mSymbolTable, true);
		final InterferenceEdgeCollector edgeTraverser = new InterferenceEdgeCollector(mIcfg, translator);
		final GroupedInterferenceFactory<?> interferenceFactory = createInterferenceFactory(
				mSettings.interferenceApplicatorType(), edgeTraverser, translator, postcondition, domain, factory,
				script, interferenceLocksetInfo(), mPreForkSourcesByThread);
		logger.info("Interference method: %s (%s)", mSettings.interferenceApplicatorType(),
				interferenceFactory.getClass().getSimpleName());
		logger.info("Interference grouping: abstract-location pairs via %s", mSettings.locationAbstractionType());

		return new SetupResult(mForkGraph, domain, interferenceFactory, postcondition, mJoinedThreads,
				mAbstractLocationIds, mutexInvariants);
	}

	private MustLocksetAnalysis interferenceLocksetInfo() {
		return mSettings.locksetAwareInterference() ? mLocksetInfo : MustLocksetAnalysis.disabled();
	}

	private static Map<IcfgLocation, Integer> computeLocationIds(final ThreadModularSifaSettings settings,
			final IUltimateServiceProvider services, final IIcfg<IcfgLocation> icfg,
			final MustLocksetAnalysis locksetInfo) {
		return new LocationAbstraction().computeLocationAbstraction(settings.locationAbstractionType(), services, icfg,
				locksetInfo);
	}

	private static GroupedInterferenceFactory<?> createInterferenceFactory(
			final InterferenceApplicatorType applicatorType, final InterferenceEdgeCollector edgeTraverser,
			final TransFormulaToInterferencePredicate translator, final RelationalPredicatePostcondition postcondition,
			final IDomain domain, final BasicPredicateFactory factory, final ManagedScript script,
			final MustLocksetAnalysis locksetInfo, final Map<String, Set<IcfgLocation>> preForkSourcesByThread) {
		return switch (applicatorType) {
		case STRONGEST_POSTCONDITION -> new StrongestPostconditionInterferenceFactory(edgeTraverser, translator,
				postcondition, factory, script, locksetInfo, preForkSourcesByThread);
		case GUARDED_EXACT_UPDATE -> new GuardedUpdateInterferenceFactory(edgeTraverser, translator, postcondition,
				script, factory, locksetInfo, preForkSourcesByThread);
		case POST_STATE -> new PostStateInterferenceFactory(edgeTraverser, translator, postcondition, domain, factory,
				script, locksetInfo, preForkSourcesByThread);
		};
	}

	public static record SetupResult(ThreadForkGraph forkGraph, IDomain domain,
			GroupedInterferenceFactory<?> interferenceFactory, RelationalPredicatePostcondition postcondition,
			Set<String> joinedThreads, Map<IcfgLocation, Integer> abstractLocationIds, PublishOnAcquire mutexInvariants) {
	}
}
