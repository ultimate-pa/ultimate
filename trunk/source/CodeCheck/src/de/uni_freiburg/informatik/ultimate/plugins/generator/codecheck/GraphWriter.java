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
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgCallTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgReturnTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.AnnotationRemover;
import de.uni_freiburg.informatik.ultimate.logic.FormulaUnLet;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.generator.appgraph.AnnotatedProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.appgraph.AppEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.appgraph.AppHyperEdge;

public class GraphWriter {

	private boolean mAnnotateEdges = true;
	private boolean mAnnotateNodes = true;
	private boolean mShowUnreachableEdges = false;
	private final boolean mShowNodeToCopy = true;
	private boolean mHideUnreachableOnce = true;
	private boolean mDontWrite = true;

	private final AnnotationRemover mAnnotationRemover;
	private final String mImagePath;
	private int mGraphCounter = 0;
	private final ILogger mLogger;

	/**
	 * Initialize the Graphwriter with some options
	 *
	 * @param annotateEdges
	 *            annotate the edges?
	 * @param annotateNodes
	 * @param showUnreachableEdges
	 */
	public GraphWriter(final ILogger logger, final String imagePath, final boolean annotateEdges,
			final boolean annotateNodes, final boolean showUnreachableEdges) {
		mLogger = logger;
		mImagePath = imagePath;
		if (imagePath == "") {
			mDontWrite = true;
		}
		mAnnotateEdges = annotateEdges;
		mAnnotateNodes = annotateNodes;
		mShowUnreachableEdges = showUnreachableEdges;
		mAnnotationRemover = new AnnotationRemover();
	}

	public void writeGraphAsImage(final AnnotatedProgramPoint root, final String fileName) {
		if (mDontWrite) {
			return;
		}
		final GraphViz gv = new GraphViz(mLogger);

		gv.addLine(GraphViz.START_GRAPH);

		final Set<AnnotatedProgramPoint> allNodes = collectNodes(root);
		final List<GraphEdge> allEdges = collectEdges(allNodes);

		gv.addLine(writeNodesToString(allNodes).toString());
		gv.addLine(writeEdgesToString(allEdges).toString());

		gv.addLine(GraphViz.END_GRAPH);

		GraphViz.writeGraphToFile(gv.getGraph(gv.getDotSource(), "png"),
				new File(mImagePath + "/" + fileName + ".png"));
		mGraphCounter++;
	}

	public void writeGraphAsImage(final AnnotatedProgramPoint root, final String fileName,
			final AnnotatedProgramPoint[] errorTrace) {

		if (mDontWrite) {
			return;
		}
		final GraphViz gv = new GraphViz(mLogger);

		gv.addLine(GraphViz.START_GRAPH);

		final Set<AnnotatedProgramPoint> allNodes = collectNodes(root);
		final List<GraphEdge> allEdges = collectEdges(allNodes);

		gv.addLine(writeNodesToString(allNodes).toString());

		final Set<AnnotatedProgramPoint> errorTraceAl = new HashSet<>();
		for (int i = 0; i < errorTrace.length; i++) {
			errorTraceAl.add(errorTrace[i]);
		}
		gv.addLine(writeEdgesToString(allEdges, errorTraceAl).toString());

		gv.addLine(GraphViz.END_GRAPH);

		GraphViz.writeGraphToFile(gv.getGraph(gv.getDotSource(), "png"),
				new File(mImagePath + "/" + fileName + ".png"));
		mGraphCounter++;
	}

	public void writeGraphAsImage(final AnnotatedProgramPoint root, final String fileName,
			final Map<AnnotatedProgramPoint, AnnotatedProgramPoint> nodeToCopyCurrent,
			final Map<AnnotatedProgramPoint, AnnotatedProgramPoint> nodeToCopy) {
		if (mDontWrite) {
			return;
		}
		final GraphViz gv = new GraphViz(mLogger);

		gv.addLine(GraphViz.START_GRAPH);

		final Set<AnnotatedProgramPoint> allNodes = collectNodes(root);
		final List<GraphEdge> allEdges = collectEdges(allNodes);

		gv.addLine(writeString(allNodes, allEdges, nodeToCopyCurrent, nodeToCopy));

		gv.addLine(GraphViz.END_GRAPH);

		GraphViz.writeGraphToFile(gv.getGraph(gv.getDotSource(), "png"),
				new File(mImagePath + "/" + fileName + ".png"));
		mGraphCounter++;
	}

	private Set<AnnotatedProgramPoint> collectNodes(final AnnotatedProgramPoint root) {
		final List<AnnotatedProgramPoint> openNodes = new ArrayList<>();
		final Set<AnnotatedProgramPoint> allNodes = new HashSet<>();
		boolean hasChanged = true;

		openNodes.add(root);
		allNodes.add(root);

		while (hasChanged) {
			hasChanged = false;
			final List<AnnotatedProgramPoint> currentOpenNodes = new ArrayList<>(openNodes);

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

	private static List<GraphEdge> collectEdges(final Set<AnnotatedProgramPoint> allNodes) {
		final List<GraphEdge> allEdges = new ArrayList<>();
		for (final AnnotatedProgramPoint node : allNodes) {
			for (final AppEdge outEdge : node.getOutgoingEdges()) {
				allEdges.add(
						new GraphEdge(node, outEdge instanceof AppHyperEdge ? ((AppHyperEdge) outEdge).getHier() : null,
								outEdge.getStatement(), outEdge.getTarget()));
			}
		}
		return allEdges;
	}

	private StringBuilder writeNodesToString(final Set<AnnotatedProgramPoint> allNodes) {
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

	private StringBuilder writeEdgesToString(final List<GraphEdge> allEdges) {
		final StringBuilder graph = new StringBuilder();

		for (final Iterator<GraphEdge> it = allEdges.iterator(); it.hasNext();) {
			graph.append(convertEdgeName(it.next()) + "\n");
		}

		return graph;
	}

	private Object writeEdgesToString(final List<GraphEdge> allEdges, final Set<AnnotatedProgramPoint> errorTrace) {
		if (errorTrace == null) {
			return writeEdgesToString(allEdges);
		}

		final StringBuilder graph = new StringBuilder();

		String label = "";

		for (final Iterator<GraphEdge> it = allEdges.iterator(); it.hasNext();) {
			final GraphEdge current = it.next();
			if (errorTrace.contains(current.mSource) && errorTrace.contains(current.mTarget)
					&& !current.mSource.equals(current.mTarget)) {
				label = "[color=blue]";
			}
			graph.append(convertEdgeName(current) + label + "\n");
			label = "";
		}

		return graph;
	}

	private StringBuilder writeEdgesToString(final List<GraphEdge> allEdges,
			final Map<AnnotatedProgramPoint, AnnotatedProgramPoint> nodeToCopy) {
		final StringBuilder graph = new StringBuilder();

		for (final Iterator<GraphEdge> it = allEdges.iterator(); it.hasNext();) {
			final GraphEdge edge = it.next();
			graph.append(convertEdgeName(edge) + (nodeToCopy.values().contains(edge.mSource) ? " [style=dashed] " : "")
					+ "\n");
		}

		return graph;
	}

	private String writeString(final Set<AnnotatedProgramPoint> allNodes, final List<GraphEdge> allEdges,
			final Map<AnnotatedProgramPoint, AnnotatedProgramPoint> nodeToCopyCurrent,
			final Map<AnnotatedProgramPoint, AnnotatedProgramPoint> nodeToCopy) {
		final StringBuilder graph = new StringBuilder();

		graph.append(writeNodesToString(allNodes));
		graph.append(this.writeEdgesToString(allEdges, nodeToCopyCurrent));

		for (final Entry<AnnotatedProgramPoint, AnnotatedProgramPoint> en : nodeToCopyCurrent.entrySet()) {
			graph.append("{ rank=same; rankdir=LR; "
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

		return "\n" + quotName + "[label = \"" + name + "\\n" + assertionString + "\\n" + node.getOutgoingHyperEdges()
				+ "\" , " + additionalOptions + "];" + "\n";
	}

	private static String convertNodeName(final AnnotatedProgramPoint node) {
		return node.toString();
	}

	private static String convertNodeNameQuot(final AnnotatedProgramPoint node) {
		return "\"" + convertNodeName(node) + "\"";
	}

	private String convertEdgeName(final GraphEdge edge) {
		final StringBuilder edgeName = new StringBuilder();
		edgeName.append(convertNodeNameQuot(edge.mSource) + " -> " + convertNodeNameQuot(edge.mTarget));

		if (mAnnotateEdges) {
			String edgeLabel;
			if (edge.mLabel == null) {
				edgeLabel = "-";
			} else if (edge.mLabel instanceof IIcfgCallTransition<?>) {
				edgeLabel = "IIcfgCallTransition<?>";
			} else if (edge.mLabel instanceof IIcfgReturnTransition<?, ?>) {
				edgeLabel = "IIcfgReturnTransition<?,?>\\n" + convertNodeName(edge.mHier);
			} else {
				edgeLabel = edge.mLabel.toString();
			}

			edgeName.append("[label=\"" + edgeLabel + "\"]");
		}
		return edgeName.toString();
	}

	private String prettifyFormula(final Term f) {
		final Term f1 = mAnnotationRemover.transform(f);
		return f1.toString();
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

	private static final class GraphEdge {
		private final AnnotatedProgramPoint mSource;
		private final AnnotatedProgramPoint mTarget;
		private final AnnotatedProgramPoint mHier;
		private final IIcfgTransition<?> mLabel;

		public GraphEdge(final AnnotatedProgramPoint source, final AnnotatedProgramPoint hier,
				final IIcfgTransition<?> code, final AnnotatedProgramPoint target) {
			mSource = source;
			mHier = hier;
			mLabel = code;
			mTarget = target;
		}

		@Override
		public String toString() {
			return mSource.toString() + " --" + (mHier == null ? "" : mHier.toString()) + "-"
					+ (mLabel == null ? "null" : mLabel.toString()) + "--> " + mTarget.toString();
		}
	}
}
