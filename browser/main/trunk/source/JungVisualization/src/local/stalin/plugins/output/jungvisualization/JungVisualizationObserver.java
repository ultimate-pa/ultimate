package local.stalin.plugins.output.jungvisualization;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;

import local.stalin.access.IUnmanagedObserver;
import local.stalin.access.WalkerOptions;
import local.stalin.model.AbstractEdgeNode;
import local.stalin.model.AbstractNoEdgeNode;
import local.stalin.model.Edge;
import local.stalin.model.IEdge;
import local.stalin.model.IElement;
import local.stalin.model.INode;
import local.stalin.plugins.output.jungvisualization.editor.JungEditor;
import local.stalin.plugins.output.jungvisualization.editor.JungEditorInput;
import local.stalin.plugins.output.jungvisualization.graph.GraphHandler;
import local.stalin.plugins.output.jungvisualization.graph.GraphProperties;

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
import edu.uci.ics.jung.graph.DirectedSparseMultigraph;
import edu.uci.ics.jung.graph.Forest;
import edu.uci.ics.jung.graph.Graph;
import edu.uci.ics.jung.graph.SparseMultigraph;
import edu.uci.ics.jung.graph.util.EdgeType;
import edu.uci.ics.jung.visualization.VisualizationViewer;

public class JungVisualizationObserver implements IUnmanagedObserver {

	private Map<IElement,String> mseenlist;
	private int mnumroots;
    //private Logger m_Logger;
    //private List<IEdge> backEdges;
    private INode rootNode;
    
//	private Graph<INode,String> g = new SparseMultigraph<INode, String>();
//	private Layout<INode, String> layout = new FRLayout2<INode, String> (g);
//	private VisualizationViewer<INode, String> vv = new VisualizationViewer<INode, String>(layout);
	
	private Graph<INode,IEdge> g = new DirectedOrderedSparseMultigraph<INode, IEdge>();
	private Layout<INode, IEdge> layout = new FRLayout2<INode, IEdge> (g);
	private VisualizationViewer<INode, IEdge> vv = new VisualizationViewer<INode, IEdge>(layout);


	@Override
	public boolean process(IElement root) {
		rootNode = (INode) root;
		if (rootNode != null) g.addVertex(rootNode);
		dfstraverse(rootNode, "" + (++mnumroots));
		GraphHandler.getInstance().addVisualizationViewer(vv);
		GraphProperties.getInstance().setGraphProperties(vv, g, rootNode);	
		return false;
	}
	
	
	
	@Override
	public void finish() {
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
		job.setPriority(UIJob.INTERACTIVE); // the fastest execution possible.
		job.schedule(); // start job.
		
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
//			s_Logger.error(pie.getMessage() + " ~~ " + pie.getCause() + " ~~ "
//					+ Arrays.toString(pie.getStackTrace()));
		} catch (Exception ex) {
//			s_Logger.fatal("An unknown exception has occured: "
//					+ ex.getMessage());
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
        //m_Logger = Logger.getRootLogger();
	}
	

	private void dfstraverse(INode node,String numbering) {

		mseenlist.put(node, numbering);
		//m_Logger.info("Node " + numbering + "; Name: " + node.toString() + ";Annotations: " + node.getPayload().toString());
		List<INode> newnodes = new ArrayList<INode>();
		List<INode> children = node.getOutgoingNodes();


		if(children != null){
			int num = -1;
			// Add new nodes and detect back edges...
			for( INode n : children ) {
				String backedge = mseenlist.get(n);

				if( backedge != null )
				{
					//m_Logger.info("Back edge from " + numbering + " to " + backedge);
				}
				else {
					String newnumbering = numbering + "." + (++num);
					mseenlist.put(n,newnumbering);
					newnodes.add(n);
					//add nodes to the graph
					g.addVertex(n);

				}
				//add edges to the graph
				Iterator<IEdge> outEdges = node.getOutgoingEdges().iterator();
				while (outEdges.hasNext()){					
					IEdge tmpEdge = outEdges.next();
					
					if (tmpEdge.getTarget().equals(n) && (!mseenlist.containsKey(tmpEdge))){
						g.addEdge(tmpEdge, node, n,EdgeType.DIRECTED);
						mseenlist.put(tmpEdge, "Edge");
					}
				}

			}
		}
		for( INode n : newnodes )
		{
			dfstraverse(n, mseenlist.get(n));	
		}
	}



	@Override
	public boolean performedChanges() {
		// TODO Auto-generated method stub
		return false;
	}
	
}