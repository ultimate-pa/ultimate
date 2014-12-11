package de.uni_freiburg.informatik.ultimate.plugins.output.jungvisualization;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.access.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.access.WalkerOptions;
import de.uni_freiburg.informatik.ultimate.model.GraphType;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.structure.IVisualizable;
import de.uni_freiburg.informatik.ultimate.model.structure.VisualizationEdge;
import de.uni_freiburg.informatik.ultimate.model.structure.VisualizationNode;
import de.uni_freiburg.informatik.ultimate.plugins.output.jungvisualization.editor.JungEditor;
import de.uni_freiburg.informatik.ultimate.plugins.output.jungvisualization.editor.JungEditorInput;
import de.uni_freiburg.informatik.ultimate.plugins.output.jungvisualization.graph.GraphHandler;
import de.uni_freiburg.informatik.ultimate.plugins.output.jungvisualization.graph.GraphProperties;

import org.apache.log4j.Logger;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.progress.UIJob;

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

	public JungVisualizationObserver(Logger logger, GraphType graphType) {
		mLogger = logger;
		mGraph = new DirectedOrderedSparseMultigraph<VisualizationNode, VisualizationEdge>();
		mGraphLayout = new FRLayout2<VisualizationNode, VisualizationEdge>(mGraph);
		mVisualizationViewer = new VisualizationViewer<VisualizationNode, VisualizationEdge>(mGraphLayout);
		mInputGraphType = graphType;
	}

	@Override
	public void init() {
		mSeenList = new HashMap<IElement, String>();
		mNumberOfRoots = -1;
	}

	@Override
	public boolean process(IElement root) {
		if (root instanceof IVisualizable) {
			mUltimateRootNode = ((IVisualizable) root).getVisualizationGraph();
			mGraph.addVertex(mUltimateRootNode);
			dfstraverse(mUltimateRootNode, Integer.toString(++mNumberOfRoots));
			GraphHandler.getInstance().addVisualizationViewer(mVisualizationViewer);
			GraphProperties.getInstance().setGraphProperties(mVisualizationViewer, mGraph, mUltimateRootNode);
			mOpenWindow = true;
		} else {
			mLogger.error("Model is not visualizable: " + root);
			mOpenWindow = false;
		}
		return false;
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
		JungEditorInput editorInput = new JungEditorInput(name);
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