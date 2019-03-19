/*
 * Code taken from https://github.com/johspaeth/PathExpression
 * Copyright (C) 2018 Johannes Spaeth
 * Copyright (C) 2018 Fraunhofer IEM, Paderborn, Germany
 * 
 * Copyright (C) 2019 Claus Schätzle (schaetzc@tf.uni-freiburg.de)
 * Copyright (C) 2019 University of Freiburg
 *
 * This file is part of the ULTIMATE Library-PathExpressions plug-in.
 *
 * The ULTIMATE Library-PathExpressions plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Library-PathExpressions plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Library-PathExpressions plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Library-PathExpressions plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Library-PathExpressions plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.pathexpressions;

import de.uni_freiburg.informatik.ultimate.lib.pathexpressions.regex.EmptySet;
import de.uni_freiburg.informatik.ultimate.lib.pathexpressions.regex.Epsilon;
import de.uni_freiburg.informatik.ultimate.lib.pathexpressions.regex.Literal;
import de.uni_freiburg.informatik.ultimate.lib.pathexpressions.regex.Regex;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

public class PathExpressionComputer<N, L> {

	private LabeledGraph<N, L> graph;
	private Map<N, Integer> nodeToIntMap = new HashMap<>();

	/**
	 * Entry with key [u,v] describes all paths from node with index u to node with index v.
	 * @see #nodeToIntMap
	 */
	private Map<Pair<Integer, Integer>, IRegex<L>> pathExpr = new HashMap<>();
	private Map<N, List<IRegex<L>>> allPathFromNode = new HashMap<>();
	private boolean eliminated;

	public PathExpressionComputer(LabeledGraph<N, L> graph) {
		this.graph = graph;
		initNodesToIntMap();
	}

	private void initNodesToIntMap() {
		int size = nodeToIntMap.size();
		for (N node : graph.getNodes()) {
			nodeToIntMap.put(node, (++size));
		}
	}

	private Integer getIntegerFor(N node) {
		assert nodeToIntMap.get(node) != null;
		return nodeToIntMap.get(node);
	}

	public IRegex<L> getExpressionBetween(N a, N b) {
		if (!graph.getNodes().contains(a)) {
			return Regex.emptySet();
		}
		List<IRegex<L>> allExpr = computeAllPathFrom(a);
		return allExpr.get(getIntegerFor(b) - 1);
	}

	private List<IRegex<L>> computeAllPathFrom(N a) {
		assert graph.getNodes().contains(a);
		if (allPathFromNode.get(a) != null) {
			return allPathFromNode.get(a);
		}

		eliminate();
		List<PathExpression<L>> extractPathSequence = extractPathSequence();
		List<IRegex<L>> regEx = new ArrayList<>();
		for (int i = 0; i < graph.getNodes().size(); i++) {
			regEx.add(Regex.emptySet());
		}
		regEx.set(getIntegerFor(a) - 1, Regex.epsilon());
		for (int i = 0; i < extractPathSequence.size(); i++) {
			PathExpression<L> tri = extractPathSequence.get(i);
			if (tri.getSource() == tri.getTarget()) {
				IRegex<L> expression = tri.getExpression();

				int vi = tri.getSource();
				IRegex<L> regExVi = regEx.get(vi - 1);
				regEx.set(vi - 1, Regex.<L>simplifiedConcatenation(regExVi, expression));

			} else {
				IRegex<L> expression = tri.getExpression();
				int vi = tri.getSource();
				int wi = tri.getTarget();
				IRegex<L> inter;
				IRegex<L> regExVi = regEx.get(vi - 1);
				inter = Regex.<L>simplifiedConcatenation(regExVi, expression);

				IRegex<L> regExWi = regEx.get(wi - 1);
				regEx.set(wi - 1, Regex.<L>simplifiedUnion(regExWi, inter));
			}
		}
		allPathFromNode.put(a, regEx);
		return regEx;
	}

	private List<PathExpression<L>> extractPathSequence() {
		int n = graph.getNodes().size();
		List<PathExpression<L>> list = new ArrayList<>();
		for (int u = 1; u <= n; u++) {
			for (int w = u; w <= n; w++) {
				IRegex<L> reg = pathExpr(u, w);
				if (!(reg instanceof EmptySet) && !(reg instanceof Epsilon)) {
					list.add(new PathExpression<L>(reg, u, w));
				}
			}
		}
		// TODO replace the following loop:
		// use loop above to add these elements into another list and concat/reverse lists
		// (think about order some more before doing this. Order is important)
		for (int u = n; u > 0; u--) {
			for (int w = 1; w < u; w++) {
				IRegex<L> reg = pathExpr(u, w);
				if (!(reg instanceof EmptySet)) {
					list.add(new PathExpression<L>(reg, u, w));
				}
			}
		}
		return list;
	}

	private void eliminate() {
		if (eliminated) {
			return;
		}
		int numberOfNodes = graph.getNodes().size();
		// TODO eliminate this n^2 loop by using default value EMPTY
		for (int v = 1; v <= numberOfNodes; v++) {
			for (int w = 1; w <= numberOfNodes; w++) {
				updatePathExpr(v, w, Regex.emptySet());
			}
		}
		for (Edge<N, L> e : graph.getEdges()) {
			Integer head = getIntegerFor(e.getStart());
			Integer tail = getIntegerFor(e.getTarget());
			IRegex<L> pht = pathExpr(head, tail);
			pht = Regex.<L>simplifiedUnion(Regex.literal(e.getLabel()), pht);
			updatePathExpr(head, tail, pht);
		}
		for (int v = 1; v <= numberOfNodes; v++) {
			IRegex<L> pvv = pathExpr(v, v);
			pvv = Regex.<L>simplifiedStar(pvv);
			updatePathExpr(v, v, pvv);
			for (int u = v + 1; u <= numberOfNodes; u++) {
				IRegex<L> puv = pathExpr(u, v);
				if (puv instanceof EmptySet) {
					continue;
				}
				puv = Regex.<L>simplifiedConcatenation(puv, pvv);
				updatePathExpr(u, v, puv);
				for (int w = v + 1; w <= numberOfNodes; w++) {
					IRegex<L> pvw = pathExpr(v, w);
					if (pvw instanceof EmptySet) {
						continue;
					}

					IRegex<L> old_puw = pathExpr(u, w);
					IRegex<L> a = Regex.<L>simplifiedConcatenation(puv, pvw);
					IRegex<L> puw = Regex.<L>simplifiedUnion(old_puw, a);
					updatePathExpr(u, w, puw);
				}
			}
		}
		eliminated = true;
	}

	private IRegex<L> pathExpr(final int source, final int target) {
		return pathExpr.get(new Pair<>(source, target));
	}
	
	private void updatePathExpr(Integer i, Integer j, IRegex<L> reg) {
		pathExpr.put(new Pair<>(i, j), reg);
	}

}
