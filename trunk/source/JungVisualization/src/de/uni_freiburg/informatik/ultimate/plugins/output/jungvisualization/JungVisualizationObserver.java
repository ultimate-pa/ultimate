/*
 * Copyright (C) 2013-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * Copyright (C) 2009-2015 pashko
 * 
 * This file is part of the ULTIMATE JungVisualization plug-in.
 * 
 * The ULTIMATE JungVisualization plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE JungVisualization plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE JungVisualization plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE JungVisualization plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE JungVisualization plug-in grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.output.jungvisualization;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;

import org.apache.log4j.Logger;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.progress.UIJob;

import de.uni_freiburg.informatik.ultimate.access.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.access.WalkerOptions;
import de.uni_freiburg.informatik.ultimate.core.services.model.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.core.util.CoreUtil;
import de.uni_freiburg.informatik.ultimate.model.GraphType;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.structure.IVisualizable;
import de.uni_freiburg.informatik.ultimate.model.structure.VisualizationEdge;
import de.uni_freiburg.informatik.ultimate.model.structure.VisualizationNode;
import de.uni_freiburg.informatik.ultimate.plugins.output.jungvisualization.editor.JungEditor;
import de.uni_freiburg.informatik.ultimate.plugins.output.jungvisualization.editor.JungEditorInput;
import de.uni_freiburg.informatik.ultimate.plugins.output.jungvisualization.graph.GraphProperties;
import de.uni_freiburg.informatik.ultimate.result.CounterExampleResult;
import de.uni_freiburg.informatik.ultimate.result.IProgramExecution;
import de.uni_freiburg.informatik.ultimate.result.NonterminatingLassoResult;
import edu.uci.ics.jung.algorithms.layout.FRLayout2;
import edu.uci.ics.jung.algorithms.layout.Layout;
import edu.uci.ics.jung.graph.DirectedOrderedSparseMultigraph;
import edu.uci.ics.jung.graph.Graph;
import edu.uci.ics.jung.graph.util.EdgeType;
import edu.uci.ics.jung.visualization.VisualizationViewer;

public class JungVisualizationObserver implements IUnmanagedObserver {

	private Map<IElement, String> mSeenList;
	private int mNumberOfRoots;
	private VisualizationNode mUltimateRootNode;
	private Graph<VisualizationNode, VisualizationEdge> mGraph;
	private Layout<VisualizationNode, VisualizationEdge> mGraphLayout;
	private VisualizationViewer<VisualizationNode, VisualizationEdge> mVisualizationViewer;

	private final Logger mLogger;

	private boolean mOpenWindow;
	private final GraphType mInputGraphType;
	private final IUltimateServiceProvider mServices;

	public JungVisualizationObserver(Logger logger, GraphType graphType, IUltimateServiceProvider services) {
		mLogger = logger;
		mGraph = new DirectedOrderedSparseMultigraph<VisualizationNode, VisualizationEdge>();
		mGraphLayout = new FRLayout2<VisualizationNode, VisualizationEdge>(mGraph);
		mVisualizationViewer = new VisualizationViewer<VisualizationNode, VisualizationEdge>(mGraphLayout);
		mInputGraphType = graphType;
		mServices = services;
	}

	@Override
	public void init(GraphType modelType, int currentModelIndex, int numberOfModels) {
		mSeenList = new HashMap<IElement, String>();
		mNumberOfRoots = -1;
	}

	@Override
	public boolean process(IElement root) {
		if (root instanceof IVisualizable) {
			mUltimateRootNode = ((IVisualizable) root).getVisualizationGraph();
			mGraph.addVertex(mUltimateRootNode);
			dfstraverse(mUltimateRootNode, Integer.toString(++mNumberOfRoots));
//			GraphHandler.getInstance().addVisualizationViewer(mVisualizationViewer);

			GraphProperties.setGraphProperties(mVisualizationViewer, mGraph, mUltimateRootNode,
					getCounterExampleTraces(mServices));
			mOpenWindow = true;
		} else {
			mLogger.error("Model is not visualizable: " + root);
			mOpenWindow = false;
		}
		return false;
	}

	@SuppressWarnings("rawtypes")
	private ArrayList<LinkedHashSet<Object>> getCounterExampleTraces(IUltimateServiceProvider services) {
		Collection<CounterExampleResult> finiteCounterExamples = CoreUtil.filterResults(services.getResultService()
				.getResults(), CounterExampleResult.class);
		Collection<NonterminatingLassoResult> infiniteCounterExamples = CoreUtil.filterResults(services
				.getResultService().getResults(), NonterminatingLassoResult.class);

		ArrayList<LinkedHashSet<Object>> traces = new ArrayList<>();
		for (CounterExampleResult cex : finiteCounterExamples) {
			traces.add(getTrace(cex.getProgramExecution()));
		}

		for (NonterminatingLassoResult cex : infiniteCounterExamples) {
			traces.add(getTrace(cex.getStem(), cex.getLasso()));
		}

		return traces;
	}

	@SuppressWarnings("rawtypes")
	private LinkedHashSet<Object> getTrace(IProgramExecution... programExecutions) {
		LinkedHashSet<Object> trace = new LinkedHashSet<>();
		for (IProgramExecution programExecution : programExecutions) {
			for (int i = 0; i < programExecution.getLength(); ++i) {
				trace.add(programExecution.getTraceElement(i).getTraceElement());
			}
		}
		return trace;
	}

	@Override
	public void finish() {
		if (mOpenWindow) {
			// Calls UIJob.
			UIJob job = new UIJob("Jung Graph View Display") {
				public IStatus runInUIThread(IProgressMonitor mon) {
					// here we are in UI-thread so we can call
					IWorkbenchWindow window = PlatformUI.getWorkbench().getActiveWorkbenchWindow();
					openGraphEditor(window);
					return Status.OK_STATUS;
				}
			};
			job.setPriority(UIJob.INTERACTIVE); // the fastest execution
												// possible.
			job.schedule(); // start job.
		}

	}

	/**
	 * open graph editor
	 * 
	 * @param workbenchWindow
	 *            active IWorkbenchWindow
	 */
	private void openGraphEditor(IWorkbenchWindow workbenchWindow) {
		String name = getName(mInputGraphType);
		JungEditorInput editorInput = new JungEditorInput(name, mVisualizationViewer);
		try {
			workbenchWindow.getActivePage().openEditor(editorInput, JungEditor.ID, true);
		} catch (PartInitException pie) {
			MessageDialog.openError(workbenchWindow.getShell(), "Error",
					"Error opening JungEditor:\n" + pie.getMessage());
		} catch (Exception ex) {
		}
	}

	private String getName(GraphType graphType) {
		StringBuilder sb = new StringBuilder();

		String[] parts = graphType.getCreator().split("\\.");
		if (parts.length - 1 > 0) {
			sb.append(parts[parts.length - 1]);
		} else {
			if (graphType.getCreator().length() < 8) {
				sb.append(graphType.getCreator());
			} else {
				sb.append(graphType.getCreator().substring(graphType.getCreator().length() - 8));
			}
		}

		return sb.toString();
	}

	@Override
	public WalkerOptions getWalkerOptions() {
		return null;
	}

	private void dfstraverse(VisualizationNode node, String numbering) {

		mSeenList.put(node, numbering);
		List<VisualizationNode> newnodes = new ArrayList<VisualizationNode>();
		List<VisualizationNode> children = node.getOutgoingNodes();

		if (children != null) {
			int num = -1;
			// Add new nodes and detect back edges...
			for (VisualizationNode n : children) {
				String backedge = mSeenList.get(n);

				if (backedge != null) {
				} else {
					String newnumbering = String.format("%s.%s", numbering, ++num);
					mSeenList.put(n, newnumbering);
					newnodes.add(n);
					// add nodes to the graph
					mGraph.addVertex(n);

				}
				// add edges to the graph
				Iterator<VisualizationEdge> outEdges = node.getOutgoingEdges().iterator();
				while (outEdges.hasNext()) {
					VisualizationEdge tmpEdge = outEdges.next();

					if (tmpEdge.getTarget().equals(n) && (!mSeenList.containsKey(tmpEdge))) {
						mGraph.addEdge(tmpEdge, node, n, EdgeType.DIRECTED);
						mSeenList.put(tmpEdge, "Edge");
					}
				}

			}
		}
		for (VisualizationNode n : newnodes) {
			dfstraverse(n, mSeenList.get(n));
		}
	}

	@Override
	public boolean performedChanges() {
		return false;
	}

}
