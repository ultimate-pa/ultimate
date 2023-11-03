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

package de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.qvasrs;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.IcfgTransformer;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;

/**
 *
 * A loop summarization class based on rational vector addition systems with resets and states (QVASRS).
 *
 * @author Jonas Werner (wernerj@informatik.uni-freiburg.de)
 */

public class QvasrsLoopSummarization {

	private final ILogger mLogger;
	private final IUltimateServiceProvider mServices;
	private final ManagedScript mScript;

	/**
	 * Construct a new Qvasrs-Loopsummarizer.
	 *
	 * @param logger
	 *            A {@link ILogger}
	 * @param services
	 *            {@link IUltimateServiceProvider}
	 * @param script
	 *            {@link ManagedScript}
	 */
	public QvasrsLoopSummarization(final ILogger logger, final IUltimateServiceProvider services,
			final ManagedScript script) {
		mLogger = logger;
		mServices = services;
		mScript = script;
	}

	/**
	 * Compute the reachability relation of a QVASRS abstraction of a ({@link UnmodifiableTransFormula}) representing a
	 * loop in an error trace.
	 *
	 * @param loopTransitionFormula
	 *            A {@link UnmodifiableTransFormula} representing changes to variables in a loop.
	 * @param usedInIcfgTransformation
	 *            Indicate whether the instance is used in a {@link IcfgTransformer}
	 * @return A loop acceleration as reachability relation of a Qvasrs abstraction in form of a
	 *         {@link UnmodifiableTransFormula}
	 */
	public UnmodifiableTransFormula getQvasrsAcceleration(final UnmodifiableTransFormula loopTransitionFormula,
			final boolean usedInIcfgTransformation) {

		if (!SmtUtils.isArrayFree(loopTransitionFormula.getFormula())) {
			throw new UnsupportedOperationException("Qvasrs do not support arrays.");
		}

		final QvasrsSummarizer qvasrsSummarizer = new QvasrsSummarizer(mLogger, mServices, mScript);
		return QvasrsReach.reach(qvasrsSummarizer.computeQvasrsAbstraction(loopTransitionFormula, false), mScript);
	}

}
