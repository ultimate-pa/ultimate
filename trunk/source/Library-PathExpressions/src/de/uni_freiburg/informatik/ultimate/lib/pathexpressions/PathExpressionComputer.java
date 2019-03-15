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
import de.uni_freiburg.informatik.ultimate.lib.pathexpressions.regex.Plain;
import de.uni_freiburg.informatik.ultimate.lib.pathexpressions.regex.Regex;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

public class PathExpressionComputer<N, V> {

	private LabeledGraph<N, V> graph;
	private Map<N, Integer> nodeToIntMap = new HashMap<>();

	/**
	 * Entry with key [u,v] describes all paths from node with index u to node with index v.
	 * @see #nodeToIntMap
	 */
	private Map<Pair<Integer, Integer>, IRegex<V>> pathExpr = new HashMap<>();
	private IRegex<V> emptyRegEx = new EmptySet<>();
	private Map<N, List<IRegex<V>>> allPathFromNode = new HashMap<>();
	private boolean eliminated;

	public PathExpressionComputer(LabeledGraph<N, V> graph) {
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

	public IRegex<V> getExpressionBetween(N a, N b) {
		if (!graph.getNodes().contains(a)) {
			return emptyRegEx;
		}
		List<IRegex<V>> allExpr = computeAllPathFrom(a);
		return allExpr.get(getIntegerFor(b) - 1);
	}

	private List<IRegex<V>> computeAllPathFrom(N a) {
		assert graph.getNodes().contains(a);
		if (allPathFromNode.get(a) != null) {
			return allPathFromNode.get(a);
		}

		eliminate();
		List<PathExpression<V>> extractPathSequence = extractPathSequence();
		List<IRegex<V>> regEx = new ArrayList<>();
		for (int i = 0; i < graph.getNodes().size(); i++) {
			regEx.add(emptyRegEx);
		}
		regEx.set(getIntegerFor(a) - 1, new Epsilon<V>());
		for (int i = 0; i < extractPathSequence.size(); i++) {
			PathExpression<V> tri = extractPathSequence.get(i);
			if (tri.getSource() == tri.getTarget()) {
				IRegex<V> expression = tri.getExpression();

				int vi = tri.getSource();
				IRegex<V> regExVi = regEx.get(vi - 1);
				regEx.set(vi - 1, Regex.<V>concatenate(regExVi, expression));

			} else {
				IRegex<V> expression = tri.getExpression();
				int vi = tri.getSource();
				int wi = tri.getTarget();
				IRegex<V> inter;
				IRegex<V> regExVi = regEx.get(vi - 1);
				inter = Regex.<V>concatenate(regExVi, expression);

				IRegex<V> regExWi = regEx.get(wi - 1);
				regEx.set(wi - 1, Regex.<V>union(regExWi, inter));
			}
		}
		allPathFromNode.put(a, regEx);
		return regEx;
	}

	private List<PathExpression<V>> extractPathSequence() {
		int n = graph.getNodes().size();
		List<PathExpression<V>> list = new ArrayList<>();
		for (int u = 1; u <= n; u++) {
			for (int w = u; w <= n; w++) {
				IRegex<V> reg = pathExpr(u, w);
				if (!(reg instanceof EmptySet) && !(reg instanceof Epsilon)) {
					list.add(new PathExpression<V>(reg, u, w));
				}
			}
		}
		for (int u = n; u > 0; u--) {
			for (int w = 1; w < u; w++) {
				IRegex<V> reg = pathExpr(u, w);
				if (!(reg instanceof EmptySet)) {
					list.add(new PathExpression<V>(reg, u, w));
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
		for (int v = 1; v <= numberOfNodes; v++) {
			for (int w = 1; w <= numberOfNodes; w++) {
				if (v == w) {
					updatePathExpr(v, w, new Epsilon<>());
				} else {
					updatePathExpr(v, w, emptyRegEx);
				}
			}
		}
		for (Edge<N, V> e : graph.getEdges()) {
			Integer head = getIntegerFor(e.getStart());
			Integer tail = getIntegerFor(e.getTarget());
			IRegex<V> pht = pathExpr(head, tail);
			pht = Regex.<V>union(new Plain<V>(e.getLabel()), pht);
			updatePathExpr(head, tail, pht);
		}
		for (int v = 1; v <= numberOfNodes; v++) {
			IRegex<V> pvv = pathExpr(v, v);
			pvv = Regex.<V>star(pvv);
			updatePathExpr(v, v, pvv);
			for (int u = v + 1; u <= numberOfNodes; u++) {
				IRegex<V> puv = pathExpr(u, v);
				if (puv instanceof EmptySet) {
					continue;
				}
				puv = Regex.<V>concatenate(puv, pvv);
				updatePathExpr(u, v, puv);
				for (int w = v + 1; w <= numberOfNodes; w++) {
					IRegex<V> pvw = pathExpr(v, w);
					if (pvw instanceof EmptySet) {
						continue;
					}

					IRegex<V> old_puw = pathExpr(u, w);
					IRegex<V> a = Regex.<V>concatenate(puv, pvw);
					IRegex<V> puw = Regex.<V>union(old_puw, a);
					updatePathExpr(u, w, puw);
				}
			}
		}
		eliminated = true;
	}

	private IRegex<V> pathExpr(final int source, final int target) {
		return pathExpr.get(new Pair<>(source, target));
	}
	
	private void updatePathExpr(Integer i, Integer j, IRegex<V> reg) {
		pathExpr.put(new Pair<>(i, j), reg);
	}

}
