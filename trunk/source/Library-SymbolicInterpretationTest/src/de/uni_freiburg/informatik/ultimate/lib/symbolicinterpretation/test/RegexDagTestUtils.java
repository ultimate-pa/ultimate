/*
 * Copyright (C) 2019 Claus Schätzle (schaetzc@tf.uni-freiburg.de)
 * Copyright (C) 2019 University of Freiburg
 *
 * This file is part of the ULTIMATE Library-SymbolicInterpretation plug-in.
 *
 * The ULTIMATE Library-SymbolicInterpretation plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Library-SymbolicInterpretation plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Library-SymbolicInterpretation plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Library-SymbolicInterpretation plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Library-SymbolicInterpretation plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.symbolicinterpretation.test;

import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.Map;
import java.util.function.Function;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import de.uni_freiburg.informatik.ultimate.lib.pathexpressions.regex.IRegex;
import de.uni_freiburg.informatik.ultimate.lib.pathexpressions.regex.Regex;
import de.uni_freiburg.informatik.ultimate.lib.symbolicinterpretation.regexdag.RegexDag;
import de.uni_freiburg.informatik.ultimate.lib.symbolicinterpretation.regexdag.RegexDagNode;

/**
 * Helper class to generate DAGs from human write-able strings.
 * DAGs can be specified in a heavily simplified version of the <i>trivial graph format</i> (TGF).
 * <p>
 * To specify a DAG its nodes and forward edges have to be listed as a space-separated list.
 * Each node or edge has two attributes.
 * Nodes have a an id (natural number) and a label (word, typically a single letter).
 * Edges have a source (id of the source node) and a target (id of the target node).
 * Both attributes are separated by a dot ".". The dot can be omitted ("1.a" = "1a"
 * and "1.2" = "1.2").
 * In ambiguous cases the first attribute takes up as much as possible ("123" = "12.3", "12a" = "12.a").
 * The source and sink of the dag are detected automatically.
 * 
 * @author schaetzc@tf.uni-freiburg.de
 */
public class RegexDagTestUtils {

	private final static String SPLIT_REGEX = "\\s+";
	private final static String NODE_REGEX = "(\\d+)\\.?(\\S*)";
	private final static String EDGE_REGEX = "(\\d+)\\.?(\\d+)";
	private final static Pattern NODE_PATTERN = Pattern.compile(NODE_REGEX);
	private final static Pattern EDGE_PATTERN = Pattern.compile(EDGE_REGEX);

	/**
	 * Creates a DAG from a human-writeable graph format.
	 * For more information on the graph format see class documentation of {@link RegexDagTestUtils}.
	 * @param listOfNodes Space-separated list of nodes of the form {@code 0.a} (the dot is optional).
	 * @param listOfEdges Space-separated list of edges of the form {@code 0.1} (the dot is optional).
	 *                    Backward edges are added automatically.
	 * @return DAG
	 */
	public static RegexDag<String> dag(final String listOfNodes, final String listOfEdges) {
		final Map<String, RegexDagNode<String>> idToNode = new HashMap<>();
		RegexDag<String> dag = new RegexDag<String>(null);
		for (final String nodeDescription : listOfNodes.split(SPLIT_REGEX)) {
			mapNewNode(nodeDescription, idToNode);
		}
		for (final String edgeDescription : listOfEdges.split(SPLIT_REGEX)) {
			connectNewEdge(edgeDescription, idToNode);
		}
		findAndSetSourceAndSink(idToNode.values(), dag);
		return dag;
	}

	private static RegexDagNode<String> mapNewNode(final String nodeDescription,
			final Map<String, RegexDagNode<String>> mapIdToNode) {
		final Matcher matcher = NODE_PATTERN.matcher(nodeDescription);
		if (!matcher.matches()) {
			throw new IllegalArgumentException("Cannot parse node: " + nodeDescription);
		}
		final String id = matcher.group(1);
		final String label = matcher.group(2);
		final RegexDagNode<String> node = new RegexDagNode<>(stringToRegexAtom(label));
		if (mapIdToNode.put(id, node) != null) {
			throw new IllegalStateException("Node id already used: " + id);
		}
		return node;
	}

	private static void connectNewEdge(final String edgeDescription,
			final Map<String, RegexDagNode<String>> mapIdToNode) {
		final Matcher matcher = EDGE_PATTERN.matcher(edgeDescription);
		if (!matcher.matches()) {
			throw new IllegalArgumentException("Cannot parse edge: " + edgeDescription);
		}
		final Function<String, RegexDagNode<String>> error = key -> {
			throw new IllegalArgumentException("Unknown node id: " + key);
		};
		final RegexDagNode<String> source = mapIdToNode.computeIfAbsent(matcher.group(1), error);
		final RegexDagNode<String> target = mapIdToNode.computeIfAbsent(matcher.group(2), error);
		source.connectOutgoing(target);
	}

	private static void findAndSetSourceAndSink(final Collection<RegexDagNode<String>> nodes, final RegexDag<String> dag) {
		for (final RegexDagNode<String> node : nodes) {
			if (node.getOutgoingNodes().isEmpty()) {
				if (dag.getSink() != null) {
					throw new IllegalArgumentException("Multiple sinks: " + dag.getSource() + " and " + node);
				}
				dag.setSink(node);
			}
			if (node.getIncomingNodes().isEmpty()) {
				if (dag.getSource() != null) {
					throw new IllegalArgumentException("Multiple sources: " + dag.getSource() + " and " + node);
				}
				dag.setSource(node);
			}
		}
	}

	public static RegexDag<String> linearDag(final String source, final String... successors) {
		final RegexDag<String> dag = RegexDag.singleNodeDag(stringToRegexAtom(source));
		for (final String next : successors) {
			RegexDagNode<String> nextNode = new RegexDagNode<>(stringToRegexAtom(next));
			dag.getSink().connectOutgoing(nextNode);
			dag.setSink(nextNode);
		}
		return dag;
	}

	public static IRegex<String> stringToRegexAtom(final String letter) {
		if ("".equals(letter) || "ε".equals(letter)) {
			return Regex.epsilon();
		} else if ("∅".equals(letter)) {
			return Regex.emptySet();
		}
		return Regex.literal(letter);
	}

	/**
	 * Creates a string in <i>trivial graph format</i> (TGF) from a simplified version of the format.
	 * For more information on the graph format see class documentation of {@link RegexDagTestUtils}.
	 * @param listOfNodes Space-separated list of nodes of the form {@code 0.a} (the dot is optional).
	 * @param listOfEdges Space-separated list of edges of the form {@code 0.1} (the dot is optional).
	 *                    Backward edges are added automatically.
	 * @return TGF
	 */
	public static String toTgf(final String listOfNodes, final String listOfEdges) {
		// Alternative: convert input to DAG and DAG to TGF 
		return listOfNodes
				.replaceAll(SPLIT_REGEX, "\n")
				.replaceAll(NODE_REGEX, "$1 $2")
				+ "\n#\n"
				+ listOfEdges
				.replaceAll(SPLIT_REGEX, "\n")
				.replaceAll(EDGE_REGEX, "$1 $2 forward\n$2 $1 backward")
				+ (listOfEdges.isEmpty() ? "" : "\n");
	}

	/**
	 * Sorts each section of a TGF file line-wise.
	 * @param tgf String trivial graph format (TGF)
	 * @return String in trivial graph format such that in each section the lines are sorted alphabetically
	 */
	public static String sortTgf(final String tgf) {
		final String[] parts = tgf.split("\n#\n");
		for (int i = 0; i < parts.length; ++i) {
			parts[i] = sortLinewise(parts[i]);
		}
		return String.join("\n#\n", parts) + "\n";
	}

	private static String sortLinewise(final String string) {
		final String[] lines = string.split("\n");
		Arrays.sort(lines);
		return String.join("\n", lines);
	}
}
