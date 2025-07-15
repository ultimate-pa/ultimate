/*
 * Copyright (C) 2025 Matthias Heizmann (matthias.heizmann@iste.uni-stuttgart.de)
 * Copyright (C) 2025 University of Stuttgart
 *
 * This file is part of the ULTIMATE TraceCheckerUtils Library.
 *
 * The ULTIMATE TraceCheckerUtils Library is free software: you can redistribute it and/or modify it under the
 * terms of the GNU Lesser General Public License as published by the Free Software Foundation, either version 3
 * of the License, or (at your option) any later version.
 *
 * The ULTIMATE TraceCheckerUtils Library is distributed in the hope that it will be useful, but WITHOUT ANY
 * WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License along with the
 * ULTIMATE TraceCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7: If you modify the ULTIMATE TraceCheckerUtils Library,
 * or any covered work, by linking or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the licensors of the
 * ULTIMATE TraceCheckerUtils Library grant you additional permission to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.assertorders;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.Counterexample;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.dfg.CycleRemover;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.dfg.DfgBuilder;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.dfg.DfgContainer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.PathProgram;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.PathProgram.PathProgramConstructionResult;

/**
 * TODO
 *
 * @author Matthias Heizmann (matthias.heizmann@iste.uni-stuttgart.de)
 */
public class AssertOrderDfgBased<L extends IAction> implements IAssertOrder<L> {

	private static final boolean BRUTE_FORCE = false;

	IIcfg<?> mIcfg;
	ILogger mLogger;

	public AssertOrderDfgBased(final IUltimateServiceProvider services, final ILogger logger, final IIcfg<?> icfg) {
		mIcfg = icfg;
		mLogger = logger;

	}

	@Override
	public List<Set<Integer>> partition(final Counterexample<L> counterexample) {
		final PathProgramConstructionResult pp = PathProgram.constructPathProgram("For_assert_order", mIcfg,
				(Set<? extends IIcfgTransition<?>>) counterexample.getWord().asSet(), Collections.emptySet(),
				x -> true);

		final DfgContainer dfg = DfgBuilder.buildDfg(pp.getPathProgram().getInitialNodes().iterator().next(), mLogger);
		final Set<IcfgEdge> outsideBallEdges = CycleRemover.getOutsideBallEdges(dfg, mLogger);

		final Set<IcfgEdge> removedEdges;
		if (BRUTE_FORCE) {
			removedEdges = CycleRemover.computeFeedbackVertexBruteForce(dfg, mLogger);
		} else {
			removedEdges = CycleRemover.computeFeedbackVertexHeuristic(dfg, mLogger);
		}

		final Map<IIcfgTransition<?>, IIcfgTransition<?>> oldToNew = pp.getOldTransition2NewTransition();
		final Set<Integer> outsideBallNumbers = new HashSet<>();
		final Set<Integer> ballBallRemainers = new HashSet<>();
		final Set<Integer> ballBreakers = new HashSet<>();
		for (int i = 0; i < counterexample.getWord().length(); i++) {
			final IIcfgTransition<?> newEdge = oldToNew.get(counterexample.getWord().getSymbol(i));
			if (outsideBallEdges.contains(newEdge)) {
				outsideBallNumbers.add(i);
			} else if (removedEdges.contains(newEdge)) {
				ballBreakers.add(i);
			} else {
				ballBallRemainers.add(i);
			}
		}
		mLogger.warn(String.format("Edges outside balls: %s, remaining edges in broken balls: %s, ball-breakers: %s",
				outsideBallNumbers.size(), ballBallRemainers.size(), ballBreakers.size()));

		final List<Set<Integer>> list = new ArrayList<>();
		list.add(outsideBallNumbers);
		list.add(ballBallRemainers);
		list.add(ballBreakers);
		return list;
	}
}
