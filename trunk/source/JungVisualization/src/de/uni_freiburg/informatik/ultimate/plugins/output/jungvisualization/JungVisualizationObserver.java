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

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.progress.UIJob;

import de.uni_freiburg.informatik.ultimate.core.lib.models.VisualizationEdge;
import de.uni_freiburg.informatik.ultimate.core.lib.models.VisualizationNode;
import de.uni_freiburg.informatik.ultimate.core.lib.results.CounterExampleResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.NonterminatingLassoResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.ResultUtil;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.IVisualizable;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelType;
import de.uni_freiburg.informatik.ultimate.core.model.observers.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution;
import de.uni_freiburg.informatik.ultimate.plugins.output.jungvisualization.editor.JungEditor;
import de.uni_freiburg.informatik.ultimate.plugins.output.jungvisualization.editor.JungEditorInput;
import de.uni_freiburg.informatik.ultimate.plugins.output.jungvisualization.graph.GraphProperties;
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
	private final Graph<VisualizationNode, VisualizationEdge> mGraph;
	private final Layout<VisualizationNode, VisualizationEdge> mGraphLayout;
	private final VisualizationViewer<VisualizationNode, VisualizationEdge> mVisualizationViewer;
	
	private final ILogger mLogger;
	
	private boolean mOpenWindow;
	private final ModelType mInputGraphType;
	private final IUltimateServiceProvider mServices;
	
	public JungVisualizationObserver(final ILogger logger, final ModelType graphType,
			final IUltimateServiceProvider services) {
		mLogger = logger;
		mGraph = new DirectedOrderedSparseMultigraph<>();
		mGraphLayout = new FRLayout2<>(mGraph);
		mVisualizationViewer = new VisualizationViewer<>(mGraphLayout);
		mInputGraphType = graphType;
		mServices = services;
	}
	
	@Override
	public void init(final ModelType modelType, final int currentModelIndex, final int numberOfModels) {
		mSeenList = new HashMap<>();
		mNumberOfRoots = -1;
	}
	
	@Override
	public boolean process(final IElement root) {
		if (root instanceof IVisualizable) {
			final Object unknownVisualizationGraph = ((IVisualizable<?>) root).getVisualizationGraph();
			if (unknownVisualizationGraph instanceof VisualizationNode) {
				mUltimateRootNode = (VisualizationNode) unknownVisualizationGraph;
				mGraph.addVertex(mUltimateRootNode);
				dfstraverse(mUltimateRootNode, Integer.toString(++mNumberOfRoots));
				GraphProperties.setGraphProperties(mVisualizationViewer, mGraph, mUltimateRootNode,
						getCounterExampleTraces(mServices));
				mOpenWindow = true;
				return false;
			}
		}
		mLogger.error("Model is not visualizable: " + root);
		mOpenWindow = false;
		return false;
	}
	
	@SuppressWarnings("rawtypes")
	private static ArrayList<LinkedHashSet<Object>> getCounterExampleTraces(final IUltimateServiceProvider services) {
		final Collection<CounterExampleResult> finiteCounterExamples =
				ResultUtil.filterResults(services.getResultService().getResults(), CounterExampleResult.class);
		final Collection<NonterminatingLassoResult> infiniteCounterExamples =
				ResultUtil.filterResults(services.getResultService().getResults(), NonterminatingLassoResult.class);
		
		final ArrayList<LinkedHashSet<Object>> traces = new ArrayList<>();
		for (final CounterExampleResult cex : finiteCounterExamples) {
			traces.add(getTrace(cex.getProgramExecution()));
		}
		
		for (final NonterminatingLassoResult cex : infiniteCounterExamples) {
			traces.add(getTrace(cex.getStem(), cex.getLasso()));
		}
		
		return traces;
	}
	
	@SuppressWarnings("rawtypes")
	private static LinkedHashSet<Object> getTrace(final IProgramExecution... programExecutions) {
		final LinkedHashSet<Object> trace = new LinkedHashSet<>();
		for (final IProgramExecution programExecution : programExecutions) {
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
			final UIJob job = new UIJob("Jung Graph View Display") {
				@Override
				public IStatus runInUIThread(final IProgressMonitor mon) {
					// here we are in UI-thread so we can call
					final IWorkbenchWindow window = PlatformUI.getWorkbench().getActiveWorkbenchWindow();
					openGraphEditor(window);
					return Status.OK_STATUS;
				}
			};
			job.setPriority(Job.INTERACTIVE); // the fastest execution
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
	private void openGraphEditor(final IWorkbenchWindow workbenchWindow) {
		final String name = getName(mInputGraphType);
		final JungEditorInput editorInput = new JungEditorInput(name, mVisualizationViewer);
		try {
			workbenchWindow.getActivePage().openEditor(editorInput, JungEditor.ID, true);
		} catch (final PartInitException pie) {
			MessageDialog.openError(workbenchWindow.getShell(), "Error",
					"Error opening JungEditor:\n" + pie.getMessage());
		}
	}
	
	private static String getName(final ModelType graphType) {
		final StringBuilder sb = new StringBuilder();
		
		final String[] parts = graphType.getCreator().split("\\.");
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
	
	private void dfstraverse(final VisualizationNode node, final String numbering) {
		
		mSeenList.put(node, numbering);
		final List<VisualizationNode> newnodes = new ArrayList<>();
		final List<VisualizationNode> children = node.getOutgoingNodes();
		
		if (children != null) {
			int num = -1;
			// Add new nodes and detect back edges...
			for (final VisualizationNode n : children) {
				final String backedge = mSeenList.get(n);
				
				if (backedge == null) {
					final String newnumbering = String.format("%s.%s", numbering, ++num);
					mSeenList.put(n, newnumbering);
					newnodes.add(n);
					// add nodes to the graph
					mGraph.addVertex(n);
				}
				// add edges to the graph
				final Iterator<VisualizationEdge> outEdges = node.getOutgoingEdges().iterator();
				while (outEdges.hasNext()) {
					final VisualizationEdge tmpEdge = outEdges.next();
					
					if (tmpEdge.getTarget().equals(n) && !mSeenList.containsKey(tmpEdge)) {
						mGraph.addEdge(tmpEdge, node, n, EdgeType.DIRECTED);
						mSeenList.put(tmpEdge, "Edge");
					}
				}
				
			}
		}
		for (final VisualizationNode n : newnodes) {
			dfstraverse(n, mSeenList.get(n));
		}
	}
	
	@Override
	public boolean performedChanges() {
		return false;
	}
	
}
