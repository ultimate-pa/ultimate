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

import java.util.Set;
import java.util.function.IntFunction;
import java.util.function.Predicate;

import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.IIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainCanceledException;
import de.uni_freiburg.informatik.ultimate.core.lib.results.AllSpecificationsHoldResult;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelType;
import de.uni_freiburg.informatik.ultimate.core.model.observers.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence.IndependenceBuilder;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgContainer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.viewabstraction.abstractdomain.IViewAbstraction;
import de.uni_freiburg.informatik.ultimate.plugins.generator.viewabstraction.abstractdomain.ProgramViewAbstraction;
import de.uni_freiburg.informatik.ultimate.plugins.generator.viewabstraction.por.PersistentSetSupport;
import de.uni_freiburg.informatik.ultimate.plugins.generator.viewabstraction.programs.Program;
import de.uni_freiburg.informatik.ultimate.plugins.generator.viewabstraction.programs.SleepReducedProgram;
import de.uni_freiburg.informatik.ultimate.plugins.generator.viewabstraction.programs.cfg.CfgProgramConverter;
import de.uni_freiburg.informatik.ultimate.plugins.generator.viewabstraction.programs.cfg.CfgRuleIndependence;

public class ViewAbstractionObserver implements IUnmanagedObserver {
	public static final boolean USE_SLEEP_REDUCTION = true;
	public static final boolean USE_PERSISTENT_REDUCTION = false;

	private final ILogger mLogger;
	private final IUltimateServiceProvider mServices;

	private BoogieIcfgContainer mIcfg;
	private IElement mRootOfNewModel;
	private boolean mLastModel;

	private IIndependenceRelation<?, ? super CodeBlock> mCodeBlockIndependence;

	public ViewAbstractionObserver(final IUltimateServiceProvider services) {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(Activator.PLUGIN_ID);
		mLastModel = false;
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

		if (USE_SLEEP_REDUCTION) {
			final var cbIndependence = getOrConstructIndependence();
			final var reduced =
					SleepReducedProgram.reduceWithGlobals(program, new CfgRuleIndependence<>(cbIndependence));
			runAnalysis(new ProgramViewAbstraction<>(), reduced,
					i -> SleepReducedProgram.wrapInitialProgramConfig(converter.getInitialConfiguration(i)),
					c -> converter.isErrorView(SleepReducedProgram.underlyingProgramConfig(c)));
			return;
		}

		runAnalysis(new ProgramViewAbstraction<>(), program, converter::getInitialConfiguration,
				converter::isErrorView);
	}

	private <V, C> void runAnalysis(final IViewAbstraction<C, V> viewAbstraction, final Program<C> program,
			final IntFunction<V> makeInitial, final Predicate<V> isBadView) {
		for (int k = 1; true; ++k) {
			mLogger.info("Computing view abstraction at level %d", k);

			if (USE_PERSISTENT_REDUCTION) {
				// compute the number of threads to be considered for persistent sets
				final int delta = program.getExtensionSize();
				final int extendedThreads = k + delta;

				final var persistent =
						new PersistentSetSupport(mServices, mIcfg, getOrConstructIndependence(), extendedThreads);
				final var persistentSets = persistent.getPersistentSets();

				// TODO create persistent set-instrumented program
				throw new UnsupportedOperationException("not yet implemented");
			}

			final var initial = makeInitial.apply(k);
			final var runner = new ViewAbstractionComputation<>(mServices, viewAbstraction, k, program, Set.of(initial),
					isBadView::test);
			final var status = runner.run();
			final var fp = runner.getCurrentAbstraction();

			switch (status) {
			case CANCELLED:
				final var violation = fp.stream().filter(isBadView).findFirst().get();
				mLogger.warn("Violation found in iteration %d: %s", runner.getCurrentIteration() + 1, violation);
				break;
			case COMPLETED:
				mLogger.info("Fixpoint computation completed after %d iterations with %d views",
						runner.getCurrentIteration(), fp.size());
				mServices.getResultService().reportResult(Activator.PLUGIN_ID, new AllSpecificationsHoldResult(
						Activator.PLUGIN_ID, "ViewAbstraction proved that the parameterized program is correct."));
				return;
			case PAUSED:
				mLogger.warn("Fixpoint computation stopped after %d iterations (%d views in pre-fixpoint)",
						runner.getCurrentIteration(), fp.size());
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

	private IIndependenceRelation<?, ? super CodeBlock> getOrConstructIndependence() {
		if (mCodeBlockIndependence == null) {
			mCodeBlockIndependence =
					IndependenceBuilder.semantic(mServices, mIcfg.getCfgSmtToolkit().getManagedScript(), false, false)
							.withSyntacticCheck().cached().build();
		}
		return mCodeBlockIndependence;
	}
}
