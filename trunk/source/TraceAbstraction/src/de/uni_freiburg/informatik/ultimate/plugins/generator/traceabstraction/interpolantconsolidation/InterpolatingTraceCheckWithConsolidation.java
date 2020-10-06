/*
 * Copyright (C) 2019 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2019 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceAbstraction plug-in.
 *
 * The ULTIMATE TraceAbstraction plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceAbstraction plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceAbstraction plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceAbstraction plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceAbstraction plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantconsolidation;

import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.interpolant.IInterpolantGenerator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.interpolant.IInterpolatingTraceCheck;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.tracecheck.ITraceCheck;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.tracecheck.TraceCheckReasonUnknown;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsDataProvider;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class InterpolatingTraceCheckWithConsolidation<TC extends IInterpolantGenerator<L> & ITraceCheck<L>, L extends IIcfgTransition<?>>
		extends InterpolantGeneratorWithConsolidation<TC, L> implements IInterpolatingTraceCheck<L> {

	public InterpolatingTraceCheckWithConsolidation(final CfgSmtToolkit csToolkit,
			final IUltimateServiceProvider services, final ILogger logger, final PredicateFactory predicateFactory,
			final TC tc) throws AutomataOperationCanceledException {
		super(csToolkit, services, logger, predicateFactory, tc);
	}

	@Override
	public LBool isCorrect() {
		return getInterpolantGenerator().isCorrect();
	}

	@Override
	public boolean providesRcfgProgramExecution() {
		return getInterpolantGenerator().providesRcfgProgramExecution();
	}

	@Override
	public IProgramExecution<L, Term> getRcfgProgramExecution() {
		return getInterpolantGenerator().getRcfgProgramExecution();
	}

	@Override
	public IStatisticsDataProvider getStatistics() {
		return super.getStatistics();
	}

	@Override
	public TraceCheckReasonUnknown getTraceCheckReasonUnknown() {
		return getInterpolantGenerator().getTraceCheckReasonUnknown();
	}

	@Override
	public boolean wasTracecheckFinishedNormally() {
		return getInterpolantGenerator().wasTracecheckFinishedNormally();
	}

}
