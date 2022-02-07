/*
 * Copyright (C) 2021 Jonas Werner (wernerj@informatik.uni-freiburg.de)
 * Copyright (C) 2021 University of Freiburg
 *
 * This file is part of the ULTIMATE IcfgTransformer library.
 *
 * The ULTIMATE IcfgTransformer is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE IcfgTransformer is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE IcfgTransformer library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE IcfgTransformer library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE IcfgTransformer grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.qvasr;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;

/**
 *
 * A loop summarization class based on rational vector addition systems with resets (Q-VASR).
 *
 * @author Jonas Werner (wernerj@informatik.uni-freiburg.de)
 */

public class QvasrLoopSummarization {

	private final ILogger mLogger;
	private final IUltimateServiceProvider mServices;
	private final ManagedScript mScript;
	private final IPredicateUnifier mPredUnifier;
	private boolean mIsOverapprox;

	/**
	 * Construct a new Qvasr-Loopsummarizer.
	 *
	 * @param logger
	 *            A {@link ILogger}
	 * @param services
	 *            {@link IUltimateServiceProvider}
	 * @param script
	 *            {@link ManagedScript}
	 * @param predUnifier
	 *            A {@link IPredicateUnifier}
	 */
	public QvasrLoopSummarization(final ILogger logger, final IUltimateServiceProvider services,
			final ManagedScript script, final IPredicateUnifier predUnifier) {
		mLogger = logger;
		mServices = services;
		mScript = script;
		mPredUnifier = predUnifier;
		mIsOverapprox = false;
	}

	/**
	 * Compute a Q-VASR summary of a ({@link UnmodifiableTransFormula}) representing a loop in an error trace.
	 *
	 * @param loopTransitionFormula
	 *            A {@link UnmodifiableTransFormula} representing changes to variables in a loop.
	 * @return A loop acceleration computed using Qvasr in form of a{@link UnmodifiableTransFormula}
	 */
	public UnmodifiableTransFormula getQvasrAcceleration(final UnmodifiableTransFormula loopTransitionFormula) {

		if (!SmtUtils.isArrayFree(loopTransitionFormula.getFormula())) {
			throw new UnsupportedOperationException("Qvasr do not support arrays.");
		}

		final QvasrSummarizer qvasrSummarizer = new QvasrSummarizer(mLogger, mServices, mScript);
		final UnmodifiableTransFormula loopSummary = qvasrSummarizer.summarizeLoop(loopTransitionFormula);
		mIsOverapprox = qvasrSummarizer.isOverapprox();
		return loopSummary;
	}

	public boolean isOverapprox() {
		return mIsOverapprox;
	}

}
