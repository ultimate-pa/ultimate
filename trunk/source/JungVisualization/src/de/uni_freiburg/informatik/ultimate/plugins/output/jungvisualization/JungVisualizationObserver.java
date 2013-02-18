package de.uni_freiburg.informatik.ultimate.plugins.output.jungvisualization;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.access.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.access.WalkerOptions;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
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

	private Map<IElement, String> mseenlist;
	private int mnumroots;
	private VisualizationNode rootNode;
	private Graph<VisualizationNode, VisualizationEdge> g = new DirectedOrderedSparseMultigraph<VisualizationNode, VisualizationEdge>();
	private Layout<VisualizationNode, VisualizationEdge> layout = new FRLayout2<VisualizationNode, VisualizationEdge>(
			g);
	private VisualizationViewer<VisualizationNode, VisualizationEdge> vv = new VisualizationViewer<VisualizationNode, VisualizationEdge>(
			layout);

	private static Logger sLogger = UltimateServices.getInstance().getLogger(
			Activator.PLUGIN_ID);

	private boolean mOpenWindow;

	@Override
	public boolean process(IElement root) {
		if (root instanceof IVisualizable) {
			rootNode = ((IVisualizable) root).getVisualizationGraph();
			g.addVertex(rootNode);
			dfstraverse(rootNode, "" + (++mnumroots));
			GraphHandler.getInstance().addVisualizationViewer(vv);
			GraphProperties.getInstance().setGraphProperties(vv, g, rootNode);
			mOpenWindow = true;
		} else {
			sLogger.error("Model is not visualizable: " + root);
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
					IWorkbenchWindow window = PlatformUI.getWorkbench()
							.getActiveWorkbenchWindow();

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
		JungEditorInput editorInput = new JungEditorInput("JUNG");

		try {
			workbenchWindow.getActivePage().openEditor(editorInput,
					JungEditor.ID, true);
		} catch (PartInitException pie) {
			MessageDialog.openError(workbenchWindow.getShell(), "Error",
					"Error opening JungEditor:\n" + pie.getMessage());
			// s_Logger.error(pie.getMessage() + " ~~ " + pie.getCause() +
			// " ~~ "
			// + Arrays.toString(pie.getStackTrace()));
		} catch (Exception ex) {
			// s_Logger.fatal("An unknown exception has occured: "
			// + ex.getMessage());
		}
	}

	@Override
	public WalkerOptions getWalkerOptions() {
		// Not needed...
		return null;
	}

	@Override
	public void init() {
		mseenlist = new HashMap<IElement, String>();
		mnumroots = -1;
		// m_Logger = Logger.getRootLogger();
	}

	private void dfstraverse(VisualizationNode node, String numbering) {

		mseenlist.put(node, numbering);
		// m_Logger.info("Node " + numbering + "; Name: " + node.toString() +
		// ";Annotations: " + node.getPayload().toString());
		List<VisualizationNode> newnodes = new ArrayList<VisualizationNode>();
		List<VisualizationNode> children = node.getOutgoingNodes();

		if (children != null) {
			int num = -1;
			// Add new nodes and detect back edges...
			for (VisualizationNode n : children) {
				String backedge = mseenlist.get(n);

				if (backedge != null) {
					// m_Logger.info("Back edge from " + numbering + " to " +
					// backedge);
				} else {
					String newnumbering = numbering + "." + (++num);
					mseenlist.put(n, newnumbering);
					newnodes.add(n);
					// add nodes to the graph
					g.addVertex(n);

				}
				// add edges to the graph
				Iterator<VisualizationEdge> outEdges = node.getOutgoingEdges()
						.iterator();
				while (outEdges.hasNext()) {
					VisualizationEdge tmpEdge = outEdges.next();

					if (tmpEdge.getTarget().equals(n)
							&& (!mseenlist.containsKey(tmpEdge))) {
						g.addEdge(tmpEdge, node, n, EdgeType.DIRECTED);
						mseenlist.put(tmpEdge, "Edge");
					}
				}

			}
		}
		for (VisualizationNode n : newnodes) {
			dfstraverse(n, mseenlist.get(n));
		}
	}

	@Override
	public boolean performedChanges() {
		// TODO Auto-generated method stub
		return false;
	}

}