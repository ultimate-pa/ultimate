/*
 * Copyright (C) 2018 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2018 University of Freiburg
 *
 * This file is part of the ULTIMATE Util Library.
 *
 * The ULTIMATE Util Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Util Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Util Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Util Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Util Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.util;

import java.util.ArrayDeque;
import java.util.Deque;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.LinkedHashRelation;
import de.uni_freiburg.informatik.ultimate.util.scc.DefaultSccComputation;
import de.uni_freiburg.informatik.ultimate.util.scc.SccComputation.ISuccessorProvider;
import de.uni_freiburg.informatik.ultimate.util.scc.StronglyConnectedComponent;

/**
 * Please see {@link TransitiveClosure#computeClosure} for documentation.
 *
 * TODO: find a better name for this class.
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
public class TransitiveClosure {

	/**
	 * Input:
	 *  <li> a set of NODES
	 *  <li> a labeling function l : NODEs -> NODEs that assigns a set of labels to each node
	 *  <li> a graph over the nodes
	 *
	 * This procedure computes the minimal labeling l' where for each edge (n1, n2) in the node graph, the label of n2
	 * is a superset of the label of n1, i.e. l'(n1) \subseteq l'(n2).
	 *
	 * @param logger
	 * @param allNodes set of all nodes
	 * @param initialLabeling initial labeling function l
	 * @param graphSuccessorProvider graph over the nodes
	 * @return
	 */
	public static <NODE, LABEL> Map<NODE, Set<LABEL>> computeClosure(final ILogger logger,
			final Set<NODE> allNodes,
			final Function<NODE, Set<LABEL>> initialLabeling,
			final ISuccessorProvider<NODE> graphSuccessorProvider) {



		final Map<NODE, Set<LABEL>> closedProcToModGlobals;
		final int numberOfAllNodes = allNodes.size();
		final Set<NODE> startNodes = allNodes;
		final DefaultSccComputation<NODE> dssc = new DefaultSccComputation<>(logger,
				graphSuccessorProvider, numberOfAllNodes, startNodes);

		/*
		 * Initialize the modified globals for each SCC with the union of each method's
		 * modified globals. (within an SCC all procedure may call all others (possibly
		 * transitively) thus all must have the same modifies clause contents)
		 */
		final LinkedHashRelation<StronglyConnectedComponent<NODE>, LABEL> sccToLabel =
				new LinkedHashRelation<>();
		for (final StronglyConnectedComponent<NODE> scc : dssc.getSCCs()) {
			for (final NODE procInfo : scc.getNodes()) {
				for (final LABEL modGlobal : initialLabeling.apply(procInfo)) {
					sccToLabel.addPair(scc, modGlobal);
				}
			}
		}

		/*
		 * update the modified globals for the sccs according to the edges in the call
		 * graph that connect different SCCs
		 *
		 * algorithmic idea: start with the leafs of the graph and propagate all
		 * modified globals back along call edges. The frontier is where we have already
		 * propagated modified globals.
		 *
		 */
		final Deque<StronglyConnectedComponent<NODE>> frontier = new ArrayDeque<>();
		frontier.addAll(dssc.getRootComponents());
		while (!frontier.isEmpty()) {
			final StronglyConnectedComponent<NODE> currentScc = frontier.pollFirst();

			/*
			 * Note (concerns "transitive modified globals" application of this method):
			 * We have chosen the ISuccessorProvider for the SccComputation such that the caller is the successor of the
			 * callee. (i.e., the successor relation is the inverse of the call graph)
			 */
			final Set<LABEL> currentSccModGlobals = sccToLabel.getImage(currentScc);
			final Iterator<StronglyConnectedComponent<NODE>> callers = dssc
					.getComponentsSuccessorsProvider().getSuccessors(currentScc);
			while (callers.hasNext()) {
				final StronglyConnectedComponent<NODE> caller = callers.next();

				assert !caller.equals(currentScc) : "graph not irreflexive, but must be acyclic";

				frontier.add(caller);

				for (final LABEL currentSccModGlobal : currentSccModGlobals) {
					sccToLabel.addPair(caller, currentSccModGlobal);
				}
			}
		}

		/*
		 * compute the closed mapping
		 */
		closedProcToModGlobals = new HashMap<>();
		for (final NODE procInfo : allNodes) {

			final Set<LABEL> currModClause = sccToLabel
					.getImage(dssc.getNodeToComponents().get(procInfo));
			closedProcToModGlobals.put(procInfo, currModClause);
		}
		return closedProcToModGlobals;
	}
}
