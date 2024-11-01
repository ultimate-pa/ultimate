/*
 * Copyright (C) 2024 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2024 University of Freiburg
 *
 * This file is part of the ULTIMATE ViewAbstraction plug-in.
 *
 * The ULTIMATE ViewAbstraction plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ViewAbstraction plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ViewAbstraction plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ViewAbstraction plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ViewAbstraction plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.viewabstraction;

import java.util.ArrayList;
import java.util.Set;
import java.util.function.Function;
import java.util.function.IntFunction;
import java.util.function.Predicate;

import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.IIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainCanceledException;
import de.uni_freiburg.informatik.ultimate.core.lib.results.AllSpecificationsHoldResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.StatisticsResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.UnprovableResult;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelType;
import de.uni_freiburg.informatik.ultimate.core.model.observers.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence.IndependenceBuilder;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgContainer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.viewabstraction.abstractdomain.IViewAbstraction;
import de.uni_freiburg.informatik.ultimate.plugins.generator.viewabstraction.abstractdomain.ProgramViewAbstraction;
import de.uni_freiburg.informatik.ultimate.plugins.generator.viewabstraction.por.PersistentSetReduction;
import de.uni_freiburg.informatik.ultimate.plugins.generator.viewabstraction.por.SleepSetReduction;
import de.uni_freiburg.informatik.ultimate.plugins.generator.viewabstraction.programs.IRule;
import de.uni_freiburg.informatik.ultimate.plugins.generator.viewabstraction.programs.IThreadBasedConfiguration;
import de.uni_freiburg.informatik.ultimate.plugins.generator.viewabstraction.programs.Program;
import de.uni_freiburg.informatik.ultimate.plugins.generator.viewabstraction.programs.cfg.CfgProgramConverter;
import de.uni_freiburg.informatik.ultimate.plugins.generator.viewabstraction.programs.cfg.CfgRuleIndependence;
import de.uni_freiburg.informatik.ultimate.plugins.generator.viewabstraction.programs.cfg.CfgThreadLocalState;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsDataProvider;
import de.uni_freiburg.informatik.ultimate.util.statistics.StatisticsData;

public class ViewAbstractionObserver implements IUnmanagedObserver {
	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private final VAPreferences mPreferences;

	private BoogieIcfgContainer mIcfg;
	private IElement mRootOfNewModel;
	private boolean mLastModel;

	private IIndependenceRelation<?, ? super CodeBlock> mCodeBlockIndependence;

	public ViewAbstractionObserver(final IUltimateServiceProvider services) {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(Activator.PLUGIN_ID);
		mPreferences = new VAPreferences(services);
	}

	@Override
	public boolean process(final IElement root) {
		if (root instanceof BoogieIcfgContainer) {
			mIcfg = (BoogieIcfgContainer) root;
		}
		return false;
	}

	@Override
	public void finish() {
		if (!mLastModel) {
			return;
		}

		if (mIcfg == null) {
			throw new IllegalArgumentException("No ICFG present, ViewAbstraction cannot run");
		}
		mLogger.info("Analyzing ICFG " + mIcfg.getIdentifier());

		final var converter = new CfgProgramConverter(mServices, mIcfg);
		final var program = converter.getProgram();

		if (mPreferences.enableSleepSets()) {
			final var cbIndependence = getOrConstructIndependence();
			final var reducer =
					SleepSetReduction.reduceWithGlobals(program, new CfgRuleIndependence<>(cbIndependence));
			final var reduced = reducer.getProgram();
			runAnalysis(new ProgramViewAbstraction<>(), reduced,
					i -> SleepSetReduction.wrapInitialProgramConfig(converter.getInitialConfiguration(i)),
					c -> converter.isErrorView(SleepSetReduction.underlyingProgramConfig(c)),
					cb -> reducer.getReducedRule(converter.getRuleForEdge(cb)), p -> p.getFirst().getLocation());
			reportIndependenceStatistics();
			return;
		}

		runAnalysis(new ProgramViewAbstraction<>(), program, converter::getInitialConfiguration, converter::isErrorView,
				converter::getRuleForEdge, CfgThreadLocalState::getLocation);
		reportIndependenceStatistics();
	}

	private <V, T, C extends IThreadBasedConfiguration<T, C>> void runAnalysis(
			final IViewAbstraction<C, V> viewAbstraction, final Program<C> program, final IntFunction<V> makeInitial,
			final Predicate<V> isBadView, final Function<CodeBlock, IRule<C>> edge2Rule,
			final Function<T, IcfgLocation> getThreadLocation) {
		final int maxLevel = mPreferences.maxAbstractionLevel();
		for (int k = mPreferences.minAbstractionLevel(); maxLevel <= 0 || k <= maxLevel; ++k) {
			mLogger.info("Computing view abstraction at level %d", k);
			final var iterationStatistics = new ArrayList<IStatisticsDataProvider>();

			final Program<C> analysedProgram;
			if (mPreferences.enablePersistentSets()) {
				mLogger.info("Persistent set reduction is enabled. Analysing persistent set-instrumented program.");

				// compute the number of threads to be considered for persistent sets
				final int delta = program.getExtensionSize();
				final int extendedThreads = k + delta;

				// create a persistent set-instrumented program
				final var persistent = new PersistentSetReduction<>(mServices, mIcfg, program,
						getOrConstructIndependence(), extendedThreads, getThreadLocation, edge2Rule);
				analysedProgram = persistent.getReducedProgram();
				iterationStatistics.add(persistent.getStatistics());
			} else {
				analysedProgram = program;
			}

			final var initial = makeInitial.apply(k);
			final var runner = new ViewAbstractionComputation<>(mServices, viewAbstraction, k, analysedProgram,
					Set.of(initial), isBadView::test);
			final var status = runner.run();
			final var currentAbstraction = runner.getCurrentAbstraction();

			for (final var stats : iterationStatistics) {
				final var statistics = new StatisticsData();
				statistics.aggregateBenchmarkData(stats);
				mServices.getResultService().reportResult(Activator.PLUGIN_ID,
						new StatisticsResult<>(Activator.PLUGIN_ID, "iteration " + k, statistics));
			}

			switch (status) {
			case CANCELLED:
				final var violation = currentAbstraction.stream().filter(isBadView).findFirst().get();
				mLogger.warn("Violation found in iteration %d: %s", runner.getCurrentIteration() + 1, violation);
				break;
			case COMPLETED:
				mLogger.info("Fixpoint computation completed after %d iterations with %d views",
						runner.getCurrentIteration(), currentAbstraction.size());
				mServices.getResultService().reportResult(Activator.PLUGIN_ID, new AllSpecificationsHoldResult(
						Activator.PLUGIN_ID, "ViewAbstraction proved that the parameterized program is correct."));
				return;
			case PAUSED:
				mLogger.warn("Fixpoint computation stopped after %d iterations (%d views in pre-fixpoint)",
						runner.getCurrentIteration(), currentAbstraction.size());
				break;
			default:
				break;
			}

			if (!mServices.getProgressMonitorService().continueProcessing()) {
				throw new ToolchainCanceledException(getClass());
			}

			// TODO interleave fixed point computation with unabstracted exploration
			// TODO possibly use diagonal pattern in case fixed point computation/exploration needs unbounded iterations
		}

		mServices.getResultService().reportResult(Activator.PLUGIN_ID,
				new UnprovableResult<>(Activator.PLUGIN_ID, mIcfg, null, null, "maximum abstraction level " + maxLevel
						+ " was reached without proving correctness or detecting a bug"));
	}

	private void reportIndependenceStatistics() {
		if (mCodeBlockIndependence == null) {
			return;
		}
		final var statistics = new StatisticsData();
		statistics.aggregateBenchmarkData(mCodeBlockIndependence.getStatistics());
		mServices.getResultService().reportResult(Activator.PLUGIN_ID,
				new StatisticsResult<>(Activator.PLUGIN_ID, "independence statistics", statistics));
	}

	public IElement getRootOfNewModel() {
		return mRootOfNewModel;
	}

	@Override
	public void init(final ModelType modelType, final int currentModelIndex, final int numberOfModels) {
		if (currentModelIndex == numberOfModels - 1) {
			mLastModel = true;
		}
	}

	@Override
	public boolean performedChanges() {
		return false;
	}

	// FIXME Independence must work on instantiated rules in order to properly handle local variables
	// TODO Take inspiration from IndependenceChecker::instantiate on sleep-threadmodular branch
	private IIndependenceRelation<?, ? super CodeBlock> getOrConstructIndependence() {
		if (mCodeBlockIndependence == null) {
			final var settings = mPreferences.independenceSettings();
			mCodeBlockIndependence = IndependenceBuilder
					.semantic(mServices, mIcfg.getCfgSmtToolkit().getManagedScript(), settings.useConditional(),
							!settings.useSemiCommutativity())
					.withSyntacticCheck().cached().build();
		}
		return mCodeBlockIndependence;
	}
}
