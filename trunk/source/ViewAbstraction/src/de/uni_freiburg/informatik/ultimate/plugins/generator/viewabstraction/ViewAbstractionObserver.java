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
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainCanceledException;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelType;
import de.uni_freiburg.informatik.ultimate.core.model.observers.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgContainer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.viewabstraction.programs.cfg.CfgProgramConverter;

public class ViewAbstractionObserver implements IUnmanagedObserver {
	public static final boolean USE_SLEEP_REDUCTION = false;
	public static final boolean USE_PERSISTENT_REDUCTION = false;

	private final ILogger mLogger;
	private final IUltimateServiceProvider mServices;

	private final List<BoogieIcfgContainer> mIcfgs;
	private IElement mRootOfNewModel;
	private boolean mLastModel;

	public ViewAbstractionObserver(final IUltimateServiceProvider services) {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(Activator.PLUGIN_ID);
		mLastModel = false;
		mIcfgs = new ArrayList<>();
	}

	@Override
	public boolean process(final IElement root) {
		if (root instanceof BoogieIcfgContainer) {
			mIcfgs.add((BoogieIcfgContainer) root);
		}
		return false;
	}

	@Override
	public void finish() {
		if (!mLastModel) {
			return;
		}

		if (mIcfgs.isEmpty()) {
			throw new IllegalArgumentException("No ICFG present, ViewAbstraction cannot run");
		}

		final BoogieIcfgContainer icfgRootNode = mIcfgs.get(mIcfgs.size() - 1);
		if (icfgRootNode == null) {
			throw new UnsupportedOperationException("ViewAbstraction needs an ICFG");
		}
		mLogger.info("Analyzing ICFG " + icfgRootNode.getIdentifier());

		final var converter = new CfgProgramConverter(mServices, icfgRootNode);
		final var program = converter.getProgram();

		if (USE_SLEEP_REDUCTION) {
			// TODO create sleep set-instrumented program
			throw new UnsupportedOperationException("not yet implemented");
		}
		if (USE_PERSISTENT_REDUCTION) {
			// TODO create persistent set-instrumented program
			throw new UnsupportedOperationException("not yet implemented");
		}

		for (int k = 1; true; ++k) {
			mLogger.info("Computing view abstraction at level %d", k);

			final var initial = converter.getInitialConfiguration(k);
			final var runner =
					new ViewAbstractionComputation<>(mServices, program, Set.of(initial), k, converter::isErrorView);
			final var status = runner.run();
			final var fp = runner.getCurrentAbstraction();

			switch (status) {
			case CANCELLED:
				final var violation = fp.stream().filter(converter::isErrorView).findFirst().get();
				mLogger.warn("Violation found in iteration %d: %s", runner.getCurrentIteration() + 1, violation);
				break;
			case COMPLETED:
				mLogger.info("Fixpoint computation completed after %d iterations with %d views: %s",
						runner.getCurrentIteration(), fp.size(), fp);
				break;
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
}
