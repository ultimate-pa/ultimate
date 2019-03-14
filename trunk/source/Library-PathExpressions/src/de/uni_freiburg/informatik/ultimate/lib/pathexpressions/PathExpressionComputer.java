/*******************************************************************************
 * Copyright (c) 2018 Fraunhofer IEM, Paderborn, Germany.
 * This program and the accompanying materials are made available under the
 * terms of the Eclipse Public License 2.0 which is available at
 * http://www.eclipse.org/legal/epl-2.0.
 *
 * SPDX-License-Identifier: EPL-2.0
 *
 * Contributors:
 *     Johannes Spaeth - initial API and implementation
 *******************************************************************************/

package de.uni_freiburg.informatik.ultimate.lib.pathexpressions;

import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;
import de.uni_freiburg.informatik.ultimate.lib.pathexpressions.RegEx.EmptySet;

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
	private Map<Pair<Integer, Integer>, IRegEx<V>> pathExpr = new HashMap<>();
	private IRegEx<V> emptyRegEx = new RegEx.EmptySet<>();
	private Map<N, List<IRegEx<V>>> allPathFromNode = new HashMap<>();
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

	public IRegEx<V> getExpressionBetween(N a, N b) {
		if (!graph.getNodes().contains(a)) {
			return emptyRegEx;
		}
		List<IRegEx<V>> allExpr = computeAllPathFrom(a);
		return allExpr.get(getIntegerFor(b) - 1);
	}

	private List<IRegEx<V>> computeAllPathFrom(N a) {
		assert graph.getNodes().contains(a);
		if (allPathFromNode.get(a) != null) {
			return allPathFromNode.get(a);
		}

		eliminate();
		List<PathExpression<V>> extractPathSequence = extractPathSequence();
		List<IRegEx<V>> regEx = new ArrayList<>();
		for (int i = 0; i < graph.getNodes().size(); i++) {
			regEx.add(emptyRegEx);
		}
		regEx.set(getIntegerFor(a) - 1, new Epsilon<V>());
		for (int i = 0; i < extractPathSequence.size(); i++) {
			PathExpression<V> tri = extractPathSequence.get(i);
			if (tri.getSource() == tri.getTarget()) {
				IRegEx<V> expression = tri.getExpression();

				int vi = tri.getSource();
				IRegEx<V> regExVi = regEx.get(vi - 1);
				regEx.set(vi - 1, RegEx.<V>concatenate(regExVi, expression));

			} else {
				IRegEx<V> expression = tri.getExpression();
				int vi = tri.getSource();
				int wi = tri.getTarget();
				IRegEx<V> inter;
				IRegEx<V> regExVi = regEx.get(vi - 1);
				inter = RegEx.<V>concatenate(regExVi, expression);

				IRegEx<V> regExWi = regEx.get(wi - 1);
				regEx.set(wi - 1, RegEx.<V>union(regExWi, inter));
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
				IRegEx<V> reg = pathExpr(u, w);
				if (!(reg instanceof EmptySet) && !(reg instanceof Epsilon)) {
					list.add(new PathExpression<V>(reg, u, w));
				}
			}
		}
		for (int u = n; u > 0; u--) {
			for (int w = 1; w < u; w++) {
				IRegEx<V> reg = pathExpr(u, w);
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
			IRegEx<V> pht = pathExpr(head, tail);
			pht = RegEx.<V>union(new RegEx.Plain<V>(e.getLabel()), pht);
			updatePathExpr(head, tail, pht);
		}
		for (int v = 1; v <= numberOfNodes; v++) {
			IRegEx<V> pvv = pathExpr(v, v);
			pvv = RegEx.<V>star(pvv);
			updatePathExpr(v, v, pvv);
			for (int u = v + 1; u <= numberOfNodes; u++) {
				IRegEx<V> puv = pathExpr(u, v);
				if (puv instanceof EmptySet) {
					continue;
				}
				puv = RegEx.<V>concatenate(puv, pvv);
				updatePathExpr(u, v, puv);
				for (int w = v + 1; w <= numberOfNodes; w++) {
					IRegEx<V> pvw = pathExpr(v, w);
					if (pvw instanceof EmptySet) {
						continue;
					}

					IRegEx<V> old_puw = pathExpr(u, w);
					IRegEx<V> a = RegEx.<V>concatenate(puv, pvw);
					IRegEx<V> puw = RegEx.<V>union(old_puw, a);
					updatePathExpr(u, w, puw);
				}
			}
		}
		eliminated = true;
	}

	private IRegEx<V> pathExpr(final int source, final int target) {
		return pathExpr.get(new Pair<>(source, target));
	}
	
	private void updatePathExpr(Integer i, Integer j, IRegEx<V> reg) {
		pathExpr.put(new Pair<>(i, j), reg);
	}

}
