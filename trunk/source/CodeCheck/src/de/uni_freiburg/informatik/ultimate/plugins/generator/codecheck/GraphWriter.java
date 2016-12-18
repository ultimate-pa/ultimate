/*
 * Copyright (C) 2013-2015 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2013-2015 Mostafa Mahmoud Amin
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE CodeCheck plug-in.
 * 
 * The ULTIMATE CodeCheck plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE CodeCheck plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE CodeCheck plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE CodeCheck plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE CodeCheck plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck;

import java.io.File;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.FormulaUnLet;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.generator.appgraph.AnnotatedProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.appgraph.AppEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.appgraph.AppHyperEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;

public class GraphWriter {

	private boolean mAnnotateEdges = true;
	private boolean mAnnotateNodes = true;
	private boolean mShowUnreachableEdges = false;
	private final boolean mShowNodeToCopy = true;

	private boolean mHideUnreachableOnce = true;

	private final StripAnnotationsTermTransformer mStripAnnotTermTransformer;

	private final String mImagePath;

	private boolean mDontWrite = true;

	private int mGraphCounter = 0;

	/**
	 * Initialize the Graphwriter with some options
	 * @param annotateEdges
	 *            annotate the edges?
	 * @param annotateNodes
	 * @param showUnreachableEdges
	 */
	public GraphWriter(final String imagePath, final boolean annotateEdges, final boolean annotateNodes,
			final boolean showUnreachableEdges) {
		mImagePath = imagePath;
		if (imagePath == "") {
			mDontWrite = true;
		}
		mAnnotateEdges = annotateEdges;
		mAnnotateNodes = annotateNodes;
		mShowUnreachableEdges = showUnreachableEdges;
		mStripAnnotTermTransformer = new StripAnnotationsTermTransformer();
	}

	public void writeGraphAsImage(final AnnotatedProgramPoint root, final String fileName) {
		if (mDontWrite) {
			return;
		}
		final GraphViz gv = new GraphViz();
		new HashMap<>();

		gv.addln(GraphViz.start_graph());

		final HashSet<AnnotatedProgramPoint> allNodes = collectNodes(root);
		final ArrayList<GraphEdge> allEdges = collectEdges(allNodes);

		gv.addln(writeNodesToString(allNodes).toString());
		gv.addln(writeEdgesToString(allEdges).toString());

		gv.addln(GraphViz.end_graph());

		// }

		GraphViz.writeGraphToFile(GraphViz.getGraph(gv.getDotSource(), "png"),
				new File(mImagePath + "/" + fileName + ".png"));
		// index++;
		mGraphCounter++;
	}

	public void writeGraphAsImage(final AnnotatedProgramPoint root, final String fileName,
			final AnnotatedProgramPoint[] error_trace) {

		if (mDontWrite) {
			return;
		}
		final GraphViz gv = new GraphViz();
		new HashMap<>();

		gv.addln(GraphViz.start_graph());

		final HashSet<AnnotatedProgramPoint> allNodes = collectNodes(root);
		final ArrayList<GraphEdge> allEdges = collectEdges(allNodes);

		gv.addln(writeNodesToString(allNodes).toString());

		final Set<AnnotatedProgramPoint> error_trace_al = new HashSet<>();
		for (int i = 0; i < error_trace.length; i++) {
			error_trace_al.add(error_trace[i]);
		}
		gv.addln(writeEdgesToString(allEdges, error_trace_al).toString());

		gv.addln(GraphViz.end_graph());

		// }

		GraphViz.writeGraphToFile(GraphViz.getGraph(gv.getDotSource(), "png"),
				new File(mImagePath + "/" + fileName + ".png"));
		// index++;
		mGraphCounter++;
	}

	public void writeGraphAsImage(final AnnotatedProgramPoint root, final String fileName,
			final HashMap<AnnotatedProgramPoint, AnnotatedProgramPoint> nodeToCopy_current,
			final HashMap<AnnotatedProgramPoint, AnnotatedProgramPoint> nodeToCopy) {
		if (mDontWrite) {
			return;
		}
		final GraphViz gv = new GraphViz();
		new HashMap<>();

		gv.addln(GraphViz.start_graph());

		final HashSet<AnnotatedProgramPoint> allNodes = collectNodes(root);
		final ArrayList<GraphEdge> allEdges = collectEdges(allNodes);

		gv.addln(writeString(allNodes, allEdges, nodeToCopy_current, nodeToCopy));

		gv.addln(GraphViz.end_graph());

		// }

		GraphViz.writeGraphToFile(GraphViz.getGraph(gv.getDotSource(), "png"),
				new File(mImagePath + "/" + fileName + ".png"));
		// index++;
		mGraphCounter++;
	}

	HashSet<AnnotatedProgramPoint> collectNodes(final AnnotatedProgramPoint root) {
		final ArrayList<AnnotatedProgramPoint> openNodes = new ArrayList<>();
		final HashSet<AnnotatedProgramPoint> allNodes = new HashSet<>();
		boolean hasChanged = true;

		openNodes.add(root);
		allNodes.add(root);

		while (hasChanged) {
			hasChanged = false;

			final ArrayList<AnnotatedProgramPoint> currentOpenNodes =
					(ArrayList<AnnotatedProgramPoint>) openNodes.clone();

			for (final AnnotatedProgramPoint node : currentOpenNodes) {
				final ArrayList<AnnotatedProgramPoint> inOutNodes =
						node.getOutgoingNodes() == null ? new ArrayList<>() : new ArrayList<>(node.getOutgoingNodes());

				if (mShowUnreachableEdges && !mHideUnreachableOnce && node.getIncomingNodes() != null) {
					inOutNodes.addAll(node.getIncomingNodes());
				}

				for (final AnnotatedProgramPoint n : inOutNodes) {
					if (!allNodes.contains(n)) {
						allNodes.add(n);
						openNodes.add(n);
						hasChanged = true;
					}
				}
				openNodes.remove(node);
			}
		}
		return allNodes;
	}

	ArrayList<GraphEdge> collectEdges(final HashSet<AnnotatedProgramPoint> allNodes) {
		final ArrayList<GraphEdge> allEdges = new ArrayList<>();

		// for(Iterator<AnnotatedProgramPoint> it = allNodes.iterator(); it.hasNext();){
		// AnnotatedProgramPoint node = it.next();
		for (final AnnotatedProgramPoint node : allNodes) {
			for (final AppEdge outEdge : node.getOutgoingEdges()) {
				allEdges.add(
						new GraphEdge(node, outEdge instanceof AppHyperEdge ? ((AppHyperEdge) outEdge).getHier() : null,
								outEdge.getStatement(), outEdge.getTarget()));
			}
		}
		return allEdges;
	}

	StringBuilder writeNodesToString(final HashSet<AnnotatedProgramPoint> allNodes) {
		final StringBuilder graph = new StringBuilder();

		for (final Iterator<AnnotatedProgramPoint> it = allNodes.iterator(); it.hasNext();) {
			if (mAnnotateNodes) {
				graph.append(getLabeledNode(it.next()) + "\n");
			} else {
				graph.append(convertNodeNameQuot(it.next()) + "\n");
			}
		}

		return graph;
	}

	StringBuilder writeEdgesToString(final ArrayList<GraphEdge> allEdges) {
		final StringBuilder graph = new StringBuilder();

		for (final Iterator<GraphEdge> it = allEdges.iterator(); it.hasNext();) {
			graph.append(convertEdgeName(it.next()) + "\n");
		}

		return graph;
	}

	private Object writeEdgesToString(final ArrayList<GraphEdge> allEdges,
			final Set<AnnotatedProgramPoint> error_trace) {
		if (error_trace == null) {
			return writeEdgesToString(allEdges);
		}

		final StringBuilder graph = new StringBuilder();

		String label = "";

		for (final Iterator<GraphEdge> it = allEdges.iterator(); it.hasNext();) {
			final GraphEdge current = it.next();
			if (error_trace.contains(current.source) && error_trace.contains(current.target)
					&& !current.source.equals(current.target)) {
				label = "[color=blue]";
			}
			graph.append(convertEdgeName(current) + label + "\n");
			label = "";
		}

		return graph;
	}

	StringBuilder writeEdgesToString(final ArrayList<GraphEdge> allEdges,
			final HashMap<AnnotatedProgramPoint, AnnotatedProgramPoint> nodeToCopy) {
		final StringBuilder graph = new StringBuilder();

		for (final Iterator<GraphEdge> it = allEdges.iterator(); it.hasNext();) {
			final GraphEdge edge = it.next();
			graph.append(convertEdgeName(edge) + (nodeToCopy.values().contains(edge.source) ? " [style=dashed] " : "")
					+ "\n");
		}

		return graph;
	}

	String writeString(final HashSet<AnnotatedProgramPoint> allNodes, final ArrayList<GraphEdge> allEdges,
			final HashMap<AnnotatedProgramPoint, AnnotatedProgramPoint> nodeToCopy_current,
			final HashMap<AnnotatedProgramPoint, AnnotatedProgramPoint> nodeToCopy) {
		final StringBuilder graph = new StringBuilder();

		graph.append(writeNodesToString(allNodes));
		graph.append(this.writeEdgesToString(allEdges, nodeToCopy_current));

		for (final Entry<AnnotatedProgramPoint, AnnotatedProgramPoint> en : nodeToCopy_current.entrySet()) {
			graph.append(
					// "subgraph \"cluster" + ctr++ + "\" " +
					"{ rank=same; rankdir=LR; "
							+ (mAnnotateNodes ? getLabeledNode(en.getKey(), "color=grey, style=filled")
									: convertNodeNameQuot(en.getKey()) + " [color=grey, style=filled] ; ")
							+ (mAnnotateNodes ? getLabeledNode(en.getValue(), "color=lightblue, style=filled")
									: convertNodeNameQuot(en.getValue()) + " [color=lightblue, style=filled] ;")
							+ "}");
		}
		if (mShowNodeToCopy) {
			for (final Entry<AnnotatedProgramPoint, AnnotatedProgramPoint> en : nodeToCopy.entrySet()) {
				graph.append(convertNodeNameQuot(en.getKey()) + " -> " + convertNodeNameQuot(en.getValue())
						+ "[weight=0, color=red] ;");
			}
		}
		return graph.toString();
	}

	private String getLabeledNode(final AnnotatedProgramPoint node) {
		return getLabeledNode(node, "");
	}

	private String getLabeledNode(final AnnotatedProgramPoint node, final String additionalOptions) {
		final String name = convertNodeName(node);
		final String quotName = convertNodeNameQuot(node);
		String assertionString;
		if (node.getPredicate() != null) {
			Term assertion = node.getPredicate().getFormula();

			final FormulaUnLet unLet = new FormulaUnLet();
			assertion = unLet.unlet(assertion);
			assertionString = prettifyFormula(assertion);
		} else {
			assertionString = "noAssertion";
		}

		final String nodeLabel =
				"\n" + quotName + "[label = \"" + name + "\\n" + assertionString + "\\n" + node.getOutgoingHyperEdges()
				// getNodesThatThisIsReturnCallPredOf()
						+ "\" , " + additionalOptions + "];" + "\n";

		return nodeLabel;
	}

	String convertNodeName(final AnnotatedProgramPoint node) {
		// String name = node.toString();
		// // name = "\"" + name;
		// name = name.replace("[", "");
		// name = name.replace("ERROR_LOCATION", "EL");
		// name = name.replace("ERROR_Pseudo", "PEL");
		// name = name.replace(", $Ultimate#", "");
		// name = name.replace("$Ultimate#", "");
		// name = name.replace("]", "");
		// String sUID = node.getPayload().getID().toString();
		// String sUID = (new Integer(node.hashCode())).toString();//.getPayload().getID().toString();
		// name = name + "-" + sUID.substring(0, sUID.length()/8);
		// name = name + "-" + sUID.substring(0, sUID.length()/2);
		final String name = node.toString();
		return name;
	}

	String convertNodeNameQuot(final AnnotatedProgramPoint node) {
		final String quotName = "\"" + convertNodeName(node) + "\"";
		return quotName;
	}

	String convertEdgeName(final GraphEdge edge) {
		final StringBuilder edgeName = new StringBuilder();
		edgeName.append(convertNodeNameQuot(edge.source) + " -> " + convertNodeNameQuot(edge.target));

		if (mAnnotateEdges) {
			String edgeLabel;
			if (edge.code == null) {
				edgeLabel = "-";
			} else if (edge.code instanceof Call) {
				edgeLabel = "Call";
			} else if (edge.code instanceof Return) {
				edgeLabel = "Return\\n" + convertNodeName(edge.hier);
			} else {
				edgeLabel = edge.code.getPrettyPrintedStatements();
			}

			edgeName.append("[label=\"" + edgeLabel + "\"]");
		}
		return edgeName.toString();
	}

	String prettifyFormula(final Term f) {
		final boolean prettify = true;
		if (prettify) {
			// String toReturn = f.toString().replaceAll("(_b[0-9]*)|(_[0-9]*)", ""); //obsolete since evren's change
			// String toReturn = f.toString().split("location")[0].trim();

			final Term f1 = mStripAnnotTermTransformer.transform(f);
			final String toReturn = f1.toString();
			// String toReturn = f.toString().replaceAll(":location(\\w|\\s|:|/|.|[|])*?\\)", "\\)");
			return toReturn;
		}
		return f.toString();
	}

	public boolean getHideUnreachableOnce() {
		return mHideUnreachableOnce;
	}

	public void setHideUnreachableOnce(final boolean mhideUnreachableOnce) {
		mHideUnreachableOnce = mhideUnreachableOnce;
	}

	public int getGraphCounter() {
		return mGraphCounter;
	}

	class GraphEdge {
		AnnotatedProgramPoint source;
		AnnotatedProgramPoint target;
		AnnotatedProgramPoint hier;
		CodeBlock code;

		public GraphEdge(final AnnotatedProgramPoint source, final AnnotatedProgramPoint hier, final CodeBlock code,
				final AnnotatedProgramPoint target) {
			this.source = source;
			this.hier = hier;
			this.code = code;
			this.target = target;
		}

		@Override
		public String toString() {
			return source.toString() + " --" + (hier == null ? "" : hier.toString()) + "-"
					+ (code == null ? "null" : code.toString()) + "--> " + target.toString();
		}
	}
}
