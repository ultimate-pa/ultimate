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

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.lib.pathexpressions.regex.EmptySet;
import de.uni_freiburg.informatik.ultimate.lib.pathexpressions.regex.Epsilon;
import de.uni_freiburg.informatik.ultimate.lib.pathexpressions.regex.IRegex;
import de.uni_freiburg.informatik.ultimate.lib.pathexpressions.regex.Regex;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Computes path expressions for a labeled graph.
 * <p>
 * A path expression is a regular expression describing all paths between two nodes in the labeled graph. The
 * implementation is according to chapter 2 of Tarjan's 1981 paper
 * <a href="https://dl.acm.org/citation.cfm?id=322273">Fast Algorithms for Solving Path Problems</a>. Please note that
 * this is neither the algorithm with runtime O(m α(m,n)) nor the algorithm with runtime O(m log n) mentioned in the
 * abstract of the paper.
 * <p>
 * For a fixed node v this implementation computes n path expressions -- one path expression from v to u for every node
 * u in the graph. Computing all these path expressions at once for a fixed v has time complexity of at most O(n³+m).
 * For sparse graphs the time complexity may be substantially lower.
 * <p>
 * n = number of nodes in the graph<br>
 * m = number of edges in the graph
 *
 * @param <N>
 *            Type of the graph's nodes
 * @param <L>
 *            Type of the graph's edge labels, also used as letters in the resulting regexes
 */
public class PathExpressionComputer<N, L> {

	private final ILabeledGraph<N, L> mGraph;
	/**
	 * Maps nodes from the graph to a unique number. Numbers are assigned sequentially starting from 0.
	 */
	private final Map<N, Integer> mNodeToInt = new HashMap<>();
	/**
	 * As in Tarjan's paper, P(u,v) is a regex describing all paths from node with index u to node with index v. If an
	 * entry is missing it has to be computed first.
	 * 
	 * @see #mNodeToInt
	 */
	private final Map<Pair<Integer, Integer>, IRegex<L>> mP = new HashMap<>();
	/**
	 * Caches the result of {@link #solve(N)}. Value is list which can be seen as a map. Entry i (starting with 0) of
	 * the list is the path expression from node <i>key</i> to node with number {@link #mNodeToInt}(<i>key</i>) to the
	 * node with number i (starting with 0).
	 */
	private final Map<N, List<IRegex<L>>> mAllPathsFromNode = new HashMap<>();
	/**
	 * Flag "{@link #eliminate()} executed once".
	 */
	private boolean mEliminated;

	public PathExpressionComputer(final ILabeledGraph<N, L> graph) {
		mGraph = graph;
		mapNodesToInt();
	}

	private void mapNodesToInt() {
		int nextInt = 0;
		for (final N node : mGraph.getNodes()) {
			mNodeToInt.put(node, nextInt);
			nextInt++;
		}
	}

	private Integer intOf(final N node) {
		return mNodeToInt.get(node);
	}

	public IRegex<L> exprBetween(final N source, final N target) {
		assert mGraph.getNodes().contains(source) : "Tried to compute path expression starting at non-existing node";
		assert mGraph.getNodes().contains(target) : "Tried to compute path expression ending at non-existing node";
		List<IRegex<L>> allPathsFromSource = mAllPathsFromNode.get(source);
		if (allPathsFromSource == null) {
			eliminate();
			allPathsFromSource = solve(source, extractPathSequence());
			mAllPathsFromNode.put(source, allPathsFromSource);
		}
		return allPathsFromSource.get(intOf(target));
	}

	private List<IRegex<L>> solve(final N source, final List<PathExpression<L>> pathSequence) {
		final List<IRegex<L>> allPathsFromSource =
				new ArrayList<>(Collections.nCopies(mGraph.getNodes().size(), Regex.emptySet()));
		allPathsFromSource.set(intOf(source), Regex.epsilon());
		for (final PathExpression<L> seqElement : pathSequence) {
			if (seqElement.getSource() == seqElement.getTarget()) {
				final int vi = seqElement.getSource();
				final IRegex<L> regexVi = allPathsFromSource.get(vi);
				allPathsFromSource.set(vi, Regex.simplifiedConcatenation(regexVi, seqElement.getExpression()));
			} else {
				final int vi = seqElement.getSource();
				final int wi = seqElement.getTarget();
				final IRegex<L> regexVi = allPathsFromSource.get(vi);
				final IRegex<L> inter = Regex.simplifiedConcatenation(regexVi, seqElement.getExpression());
				final IRegex<L> regexWi = allPathsFromSource.get(wi);
				allPathsFromSource.set(wi, Regex.simplifiedUnion(regexWi, inter));
			}
		}
		mAllPathsFromNode.put(source, allPathsFromSource);
		return allPathsFromSource;
	}

	private List<PathExpression<L>> extractPathSequence() {
		final int numberOfNodes = mGraph.getNodes().size();
		final List<PathExpression<L>> pathSequence = new ArrayList<>();
		for (int u = 0; u < numberOfNodes; u++) {
			for (int w = u; w < numberOfNodes; w++) {
				final IRegex<L> reg = pathExpr(u, w);
				if (!(reg instanceof EmptySet) && !(reg instanceof Epsilon)) {
					pathSequence.add(new PathExpression<>(reg, u, w));
				}
			}
		}
		for (int u = numberOfNodes - 1; u >= 0; u--) {
			for (int w = 0; w < u; w++) {
				final IRegex<L> reg = pathExpr(u, w);
				if (!(reg instanceof EmptySet)) {
					pathSequence.add(new PathExpression<>(reg, u, w));
				}
			}
		}
		return pathSequence;
	}

	private void eliminate() {
		if (mEliminated) {
			return;
		}
		final int numberOfNodes = mGraph.getNodes().size();
		// initialization of table P(u,v) not necessary due to default values
		for (final ILabeledEdge<N, L> edge : mGraph.getEdges()) {
			final Integer head = intOf(edge.getSource());
			final Integer tail = intOf(edge.getTarget());
			IRegex<L> pht = pathExpr(head, tail);
			pht = Regex.simplifiedUnion(Regex.literal(edge.getLabel()), pht);
			updatePathExpr(head, tail, pht);
		}
		for (int v = 0; v < numberOfNodes; v++) {
			IRegex<L> pvv = pathExpr(v, v);
			pvv = Regex.simplifiedStar(pvv);
			updatePathExpr(v, v, pvv);
			for (int u = v + 1; u < numberOfNodes; u++) {
				IRegex<L> puv = pathExpr(u, v);
				if (puv instanceof EmptySet) {
					continue;
				}
				puv = Regex.simplifiedConcatenation(puv, pvv);
				updatePathExpr(u, v, puv);
				for (int w = v + 1; w < numberOfNodes; w++) {
					final IRegex<L> pvw = pathExpr(v, w);
					if (pvw instanceof EmptySet) {
						continue;
					}
					final IRegex<L> oldPuw = pathExpr(u, w);
					final IRegex<L> a = Regex.simplifiedConcatenation(puv, pvw);
					final IRegex<L> puw = Regex.simplifiedUnion(oldPuw, a);
					updatePathExpr(u, w, puw);
				}
			}
		}
		mEliminated = true;
	}

	private IRegex<L> pathExpr(final Integer source, final Integer target) {
		return mP.getOrDefault(new Pair<>(source, target), Regex.emptySet());
	}

	private void updatePathExpr(final Integer source, final Integer target, final IRegex<L> newExpr) {
		mP.put(new Pair<>(source, target), newExpr);
	}

}
