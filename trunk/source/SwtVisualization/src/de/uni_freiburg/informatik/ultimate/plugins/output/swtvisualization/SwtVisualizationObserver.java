/*
 * Copyright (C) 2026 University of Freiburg
 *
 * This file is part of the ULTIMATE SwtVisualization plug-in.
 *
 * The ULTIMATE SwtVisualization plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE SwtVisualization plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE SwtVisualization plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE SwtVisualization plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE SwtVisualization plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.output.swtvisualization;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
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
import de.uni_freiburg.informatik.ultimate.plugins.output.swtvisualization.editor.SwtEditor;
import de.uni_freiburg.informatik.ultimate.plugins.output.swtvisualization.editor.SwtEditorInput;

/**
 * Observer that traverses the {@link VisualizationNode} tree, collects nodes and edges, and opens the
 * {@link SwtEditor}.
 */
public class SwtVisualizationObserver implements IUnmanagedObserver {

	private final ILogger mLogger;
	private final ModelType mInputGraphType;
	private final IUltimateServiceProvider mServices;

	private Map<Object, String> mSeenList;
	private final List<VisualizationNode> mNodes;
	private final List<VisualizationEdge> mEdges;
	private final List<LinkedHashSet<Object>> mErrorTraces;
	private VisualizationNode mRootNode;
	private boolean mOpenWindow;

	public SwtVisualizationObserver(final ILogger logger, final ModelType graphType,
			final IUltimateServiceProvider services) {
		mLogger = logger;
		mInputGraphType = graphType;
		mServices = services;
		mNodes = new ArrayList<>();
		mEdges = new ArrayList<>();
		mErrorTraces = new ArrayList<>();
	}

	@Override
	public void init(final ModelType modelType, final int currentModelIndex, final int numberOfModels) {
		mSeenList = new HashMap<>();
		mNodes.clear();
		mEdges.clear();
		mErrorTraces.clear();
		mRootNode = null;
		mOpenWindow = false;
	}

	@Override
	public boolean process(final IElement root) {
		if (root instanceof IVisualizable) {
			final Object unknownVisualizationGraph = ((IVisualizable<?>) root).getVisualizationGraph();
			if (unknownVisualizationGraph instanceof VisualizationNode) {
				mRootNode = (VisualizationNode) unknownVisualizationGraph;
				mNodes.add(mRootNode);
				mSeenList.put(mRootNode, "0");
				dfsTraverse(mRootNode, "0");
				mErrorTraces.addAll(getCounterExampleTraces(mServices));
				mOpenWindow = true;
				return false;
			}
		}
		mLogger.error("Model is not visualizable: " + root);
		mOpenWindow = false;
		return false;
	}

	private void dfsTraverse(final VisualizationNode node, final String numbering) {
		mSeenList.put(node, numbering);
		final List<VisualizationNode> newNodes = new ArrayList<>();
		final List<VisualizationNode> children = node.getOutgoingNodes();
		if (children != null) {
			int num = -1;
			for (final VisualizationNode child : children) {
				final String backEdge = mSeenList.get(child);
				if (backEdge == null) {
					num++;
					final String newNumbering = String.format("%s.%s", numbering, num);
					mSeenList.put(child, newNumbering);
					newNodes.add(child);
					mNodes.add(child);
				}
				for (final VisualizationEdge edge : node.getOutgoingEdges()) {
					if (edge.getTarget().equals(child) && !mSeenList.containsKey(edge)) {
						mEdges.add(edge);
						mSeenList.put(edge, "Edge");
					}
				}
			}
		}
		for (final VisualizationNode n : newNodes) {
			dfsTraverse(n, mSeenList.get(n));
		}
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
			final UIJob job = new UIJob("SWT Graph View Display") {
				@Override
				public IStatus runInUIThread(final IProgressMonitor mon) {
					final IWorkbenchWindow window = PlatformUI.getWorkbench().getActiveWorkbenchWindow();
					openGraphEditor(window);
					return Status.OK_STATUS;
				}
			};
			job.setPriority(Job.INTERACTIVE);
			job.schedule();
		}
	}

	private void openGraphEditor(final IWorkbenchWindow workbenchWindow) {
		final String name = getName(mInputGraphType);
		final SwtEditorInput editorInput = new SwtEditorInput(name, mRootNode, mNodes, mEdges, mErrorTraces);
		try {
			workbenchWindow.getActivePage().openEditor(editorInput, SwtEditor.ID, true);
		} catch (final PartInitException pie) {
			MessageDialog.openError(workbenchWindow.getShell(), "Error",
					"Error opening SwtEditor:\n" + pie.getMessage());
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

	@Override
	public boolean performedChanges() {
		return false;
	}
}
