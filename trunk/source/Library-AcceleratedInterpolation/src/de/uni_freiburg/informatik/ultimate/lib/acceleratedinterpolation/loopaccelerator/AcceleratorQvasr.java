/*
 * Copyright (C) 2021 Jonas Werner (wernerj@informatik.uni-freiburg.de)
 * Copyright (C) 2021 University of Freiburg
 *
 * This file is part of the ULTIMATE accelerated interpolation library .
 *
 * The ULTIMATE framework is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE framework is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE accelerated interpolation library . If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE PDR library , or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE accelerated interpolation library grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.lib.acceleratedinterpolation.loopaccelerator;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.qvasr.QvasrLoopSummarization;
import de.uni_freiburg.informatik.ultimate.lib.acceleratedinterpolation.AcceleratedInterpolation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;

/**
 * A loop accelerator used in accelerated inteprolation using the {@link QvasrLoopSummarization} method of acceleration.
 *
 * @author Jonas Werner (wernerj@informatik.uni-freiburg.de) This class represents the loop accelerator needed for
 *         {@link AcceleratedInterpolation}
 */
public class AcceleratorQvasr implements IAccelerator {
	private final ILogger mLogger;
	private final ManagedScript mScript;
	private final IUltimateServiceProvider mServices;
	private final IPredicateUnifier mPredUnifier;
	private boolean mFoundAcceleration;
	private boolean mIsOverapprox;

	/**
	 * Construct a new loop accelerator using {@link QvasrLoopSummarization}.
	 *
	 * @param logger
	 *            A {@link ILogger}
	 * @param managedScript
	 *            A {@link ManagedScript}
	 * @param services
	 *            {@link IUltimateServiceProvider}
	 * @param symbolTable
	 *            {@link IIcfgSymbolTable}
	 * @param predUnifier
	 *            A {@link IPredicateUnifier}
	 */
	public AcceleratorQvasr(final ILogger logger, final ManagedScript managedScript,
			final IUltimateServiceProvider services, final IPredicateUnifier predUnifier) {
		mLogger = logger;
		mScript = managedScript;
		mServices = services;
		mPredUnifier = predUnifier;
		mFoundAcceleration = false;
		mIsOverapprox = false;
	}

	/**
	 * Given a loop in form of an {@link UnmodifiableTransFormula} and specifiying which acceleration method, return a
	 * loop acceleration.
	 *
	 * @param loop
	 * @param accelerationMethod
	 * @return
	 */
	@Override
	public UnmodifiableTransFormula accelerateLoop(final UnmodifiableTransFormula loop, final IcfgLocation loopHead) {
		try {
			mLogger.debug("Accelerating Loop using Qvasr Summarization");
			final QvasrLoopSummarization qvasr = new QvasrLoopSummarization(mLogger, mServices, mScript, mPredUnifier);
			final UnmodifiableTransFormula loopSummary = qvasr.getQvasrAcceleration(loop);
			mFoundAcceleration = true;
			mIsOverapprox = qvasr.isOverapprox();
			return loopSummary;
		} catch (final UnsupportedOperationException ue) {
			mFoundAcceleration = false;
			mLogger.info("Qvasr could not accelerate loop because " + ue);
			return loop;
		}
	}

	@Override
	public boolean accelerationFinishedCorrectly() {
		return mFoundAcceleration;
	}

	@Override
	public boolean isOverapprox() {
		return mIsOverapprox;
	}
}
