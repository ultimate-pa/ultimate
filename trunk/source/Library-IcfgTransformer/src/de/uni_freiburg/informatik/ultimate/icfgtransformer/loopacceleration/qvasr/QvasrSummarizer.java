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

import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 *
 * A summarizer for an ({@link UnmodifiableTransFormula}).
 *
 * @author Jonas Werner (wernerj@informatik.uni-freiburg.de)
 *
 */
public class QvasrSummarizer {
	private final ILogger mLogger;
	private final ManagedScript mScript;
	private final IUltimateServiceProvider mServices;

	/**
	 * Construct a new ({@link UnmodifiableTransFormula}) summarizer based on rational vector addition systems with
	 * resets (Q-VASR)
	 *
	 * @param logger
	 * @param services
	 * @param script
	 */
	public QvasrSummarizer(final ILogger logger, final IUltimateServiceProvider services, final ManagedScript script) {
		mLogger = logger;
		mScript = script;
		mServices = services;

	}

	/**
	 * Summarize a {@link UnmodifiableTransFormula} using Q-Vasr.
	 *
	 * @param transitionFormula
	 * @return
	 */
	public UnmodifiableTransFormula summarizeLoop(final UnmodifiableTransFormula transitionFormula) {
		final Term transitionTerm = transitionFormula.getFormula();
		final Term transitionTermDnf = SmtUtils.toDnf(mServices, mScript, transitionTerm,
				XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION);

		final QvasrAbstractor qvasrAbstractor = new QvasrAbstractor(mScript, mLogger, mServices);

		final List<Term> disjuncts = QvasrUtils.splitDisjunction(transitionTermDnf);

		for (final Term disjunct : disjuncts) {
			final LBool isSat = SmtUtils.checkSatTerm(mScript.getScript(), disjunct);
			if (isSat == LBool.SAT) {
				final QvasrAbstraction qvasrAbstraction =
						qvasrAbstractor.computeAbstraction(disjunct, transitionFormula);
				// mLogger.debug(qvasrAbstraction);
			} else {
				// TODO:
				continue;
			}
		}
		return transitionFormula;
	}
}
