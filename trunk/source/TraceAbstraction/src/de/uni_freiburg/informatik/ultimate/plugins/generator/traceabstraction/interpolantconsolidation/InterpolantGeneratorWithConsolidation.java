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

import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.interpolant.IInterpolantGenerator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.interpolant.InterpolantComputationStatus;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsDataProvider;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class InterpolantGeneratorWithConsolidation<TC extends IInterpolantGenerator<LETTER>, LETTER extends IIcfgTransition<?>>
		extends InterpolantConsolidation<TC, LETTER> implements IInterpolantGenerator<LETTER> {

	public InterpolantGeneratorWithConsolidation(final CfgSmtToolkit csToolkit, final IUltimateServiceProvider services,
			final ILogger logger, final PredicateFactory predicateFactory, final TC tc)
			throws AutomataOperationCanceledException {
		super(csToolkit, services, logger, predicateFactory, tc);
	}

	@Override
	public List<LETTER> getTrace() {
		return getInterpolantGenerator().getTrace();
	}

	@Override
	public IPredicate[] getInterpolants() {
		return getConsolidatedInterpolants();
	}

	@Override
	public IPredicateUnifier getPredicateUnifier() {
		return getInterpolantGenerator().getPredicateUnifier();
	}

	@Override
	public boolean isPerfectSequence() {
		return isConsolidatedInterpolantsPerfectSequence();
	}

	@Override
	public InterpolantComputationStatus getInterpolantComputationStatus() {
		return getInterpolantGenerator().getInterpolantComputationStatus();
	}

	@Override
	public IPredicate getPrecondition() {
		return getInterpolantGenerator().getPrecondition();
	}

	@Override
	public IPredicate getPostcondition() {
		return getInterpolantGenerator().getPostcondition();
	}

	@Override
	public Map<Integer, IPredicate> getPendingContexts() {
		return getInterpolantGenerator().getPendingContexts();
	}

	@Override
	public IStatisticsDataProvider getStatistics() {
		return getInterpolantConsolidationBenchmarks();
	}
}
