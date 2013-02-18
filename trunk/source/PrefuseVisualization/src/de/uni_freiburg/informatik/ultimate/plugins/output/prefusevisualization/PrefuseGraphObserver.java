package de.uni_freiburg.informatik.ultimate.plugins.output.prefusevisualization;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;

import de.uni_freiburg.informatik.ultimate.access.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.access.WalkerOptions;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.model.GraphType;
import de.uni_freiburg.informatik.ultimate.model.IEdge;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.INode;
import de.uni_freiburg.informatik.ultimate.model.structure.IWalkable;
import de.uni_freiburg.informatik.ultimate.model.structure.VisualizationEdge;
import de.uni_freiburg.informatik.ultimate.model.structure.VisualizationNode;
import de.uni_freiburg.informatik.ultimate.plugins.output.prefusevisualization.displays.CompleteHorizontalTreeView;
import de.uni_freiburg.informatik.ultimate.plugins.output.prefusevisualization.displays.CompleteRadialGraphView;
import de.uni_freiburg.informatik.ultimate.plugins.output.prefusevisualization.displays.CompleteVerticalTreeView;
import de.uni_freiburg.informatik.ultimate.plugins.output.prefusevisualization.displays.PartialHorizontalTreeView;
import de.uni_freiburg.informatik.ultimate.plugins.output.prefusevisualization.displays.PartialVerticalTreeView;
import de.uni_freiburg.informatik.ultimate.plugins.output.prefusevisualization.displays.RotateRadialGraphView;
import de.uni_freiburg.informatik.ultimate.plugins.output.prefusevisualization.editor.PrefuseEditor;
import de.uni_freiburg.informatik.ultimate.plugins.output.prefusevisualization.editor.PrefuseEditorInput;
import de.uni_freiburg.informatik.ultimate.plugins.output.prefusevisualization.gui.DisplayChooseDialog;
import de.uni_freiburg.informatik.ultimate.plugins.output.prefusevisualization.preferences.PreferenceValues;

import org.apache.log4j.Logger;
import org.eclipse.core.runtime.Assert;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.preferences.ScopedPreferenceStore;
import org.eclipse.ui.progress.UIJob;

import prefuse.Display;
import prefuse.data.Edge;
import prefuse.data.Graph;
import prefuse.data.Node;

/**
 * This class is a AST-Visitor for creating 2D representations of the tree.
 * 
 * @author keil
 * @version 0.0.1 $LastChangedDate: 2008-03-19 15:47:15 +0100 (Mi, 19 Mrz 2008)
 *          $ $LastChangedBy: keilr $ $LastChangedRevision: 509 $
 */

public class PrefuseGraphObserver implements IUnmanagedObserver {

	private static Logger s_Logger;

	private Graph m_Graph;

	private ScopedPreferenceStore preference = PreferenceValues.Preference;
	private String choosendisplay = "";
	private GraphType m_GraphType;

	private Display m_Display;

	static {
		s_Logger = UltimateServices.getInstance()
				.getLogger(Activator.PLUGIN_ID);
	}

	/**
	 * @param graph
	 *            the prefuse graph object
	 * @param graphType
	 *            The GraphType of the current model
	 */
	public PrefuseGraphObserver(Graph graph, GraphType graphType) {
		super();
		this.m_Graph = graph;
		// this.m_Graph.clear();
		this.m_GraphType = graphType;
	}

	/** **************** p r e f u s e ****************** */

	/**
	 * @param name
	 *            the name of the node
	 * @param uid
	 *            the uid of the node
	 * @return the node
	 */
	public Node createNode(String name, String uid) {
		Assert.isNotNull(name);
		Assert.isNotNull(uid);
		Node input = m_Graph.addNode();
		input.setString("name", name);
		input.setString("uid", uid);
		input.setString("type", "node");
		return input;
	}

	/**
	 * @param source
	 *            source node
	 * @param target
	 *            target node
	 * @return the edge
	 */
	public Edge createEdge(Node source, Node target) {
		Assert.isNotNull(source);
		Assert.isNotNull(target);
		Edge input = m_Graph.addEdge(source, target);

		/*
		 * for edge labels
		 * 
		 * @name the name of the edge label input.setString("name", name);
		 */

		input.setString("uid", "");
		input.setString("type", "edge");
		return input;
	}

	// @Override
	public void finish() {
		this.m_Display = chooseDisplay(this.m_Graph);

		// Calls UIJob.
		UIJob job = new UIJob("Prefuse Editor Display") {
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

	// @Override
	public WalkerOptions getWalkerOptions() {
		// TODO Auto-generated method stub
		return null;
	}

	// @Override
	public void init() {

	}

	/**
	 * open graph editor
	 * 
	 * @param workbenchWindow
	 *            active IWorkbenchWindow
	 */
	private void openGraphEditor(IWorkbenchWindow workbenchWindow) {
		// TODO: What to display if model results from multiple files
		PrefuseEditorInput editorInput = new PrefuseEditorInput(
				this.m_GraphType.getFileName(0));

		editorInput.setGraph(m_Graph);
		editorInput.setDisplay(m_Display);
		editorInput.setGraphType(m_GraphType);

		try {
			workbenchWindow.getActivePage().openEditor(editorInput,
					PrefuseEditor.ID, true);
		} catch (PartInitException pie) {
			MessageDialog.openError(workbenchWindow.getShell(), "Error",
					"Error opening PrefuseEditor:\n" + pie.getMessage());
			s_Logger.error(pie.getMessage() + " ~~ " + pie.getCause() + " ~~ "
					+ Arrays.toString(pie.getStackTrace()));
		} catch (Exception ex) {
			s_Logger.fatal("An unknown exception has occured: "
					+ ex.getMessage());
		}
	}

	/**
	 * @return Returns the choosen Display or the default Display
	 */
	private Display chooseDisplay(Graph graph) {

		String standartDisplay = preference
				.getString(PreferenceValues.NAME_STANDARDDISPLAY);
		boolean runDisplayChooser = preference
				.getBoolean(PreferenceValues.NAME_DISPLAYCHOOSERECUTABLE);

		// String choosendisplay = "";

		if (runDisplayChooser) {
			// Shell shell = new Shell(PlatformUI.createDisplay());
			org.eclipse.swt.widgets.Display.getDefault().syncExec(
					new Runnable() {
						public void run() {
							Shell shell = new Shell();

							ArrayList<String> displays = new ArrayList<String>();

							displays.add("horizontal TreeView (partial)");
							displays.add("horizontal TreeView (complete)");
							displays.add("vertical TreeView (partial)");
							displays.add("vertical TreeView (complete)");
							displays.add("RadialGraphView (complete)");
							displays.add("RadialGraphView (rotate)");

							DisplayChooseDialog displayChooser = new DisplayChooseDialog(
									shell, displays, "Prefuse Display Chooser");
							ArrayList<String> choosenDisplays = displayChooser
									.open();

							if (choosenDisplays.size() != 0) {
								choosendisplay = choosenDisplays
										.get(choosenDisplays.size() - 1);
							}
						}
					});
		}

		Display gview;

		String display;
		if (choosendisplay != "")
			display = choosendisplay;
		else
			display = standartDisplay;

		if (display.equals("horizontal TreeView (partial)")) {
			gview = new PartialHorizontalTreeView(graph, "name");
		} else if (display.equals("horizontal TreeView (complete)")) {
			gview = new CompleteHorizontalTreeView(graph, "name");
		} else if (display.equals("vertical TreeView (partial)")) {
			gview = new PartialVerticalTreeView(graph, "name");
		} else if (display.equals("vertical TreeView (complete)")) {
			gview = new CompleteVerticalTreeView(graph, "name");
		} else if (display.equals("RadialGraphView (complete)")) {
			gview = new CompleteRadialGraphView(graph, "name");
		} else if (display.equals("RadialGraphView (rotate)")) {
			gview = new RotateRadialGraphView(graph, "name");
		} else {
			gview = new CompleteVerticalTreeView(graph, "name");
		}

		return gview;
	}

	@Override
	public boolean process(IElement root) {
		walk(root,
				new HashMap<IElement, Node>(),
				createNode(root.getPayload().getName(), root.getPayload()
						.getID().toString()));
		return false;
	}

	public void walk(IElement current, HashMap<IElement, Node> visited,
			Node parent) {
		if (current instanceof VisualizationNode) {
			for (VisualizationNode n : ((VisualizationNode) current).getOutgoingNodes()) {
				if (visited.containsKey(n)) {
					createEdge(parent, visited.get(n));
				} else {
					Node target = createNode(n.getPayload().getName(), n
							.getPayload().getID().toString());
					createEdge(parent, target);
					visited.put(n, target);
					walk(n, visited, target);
				}
			}
		} else if (current instanceof VisualizationEdge) {
			VisualizationNode n = ((VisualizationEdge) current).getTarget();
			if (visited.containsKey(n)) {
				createEdge(parent, visited.get(n));
				return;
			}
			Node target = createNode(n.getPayload().getName(), n.getPayload()
					.getID().toString());
			createEdge(parent, target);
			visited.put(n, target);
			walk(n, visited, target);
		}
	}

	@Override
	public boolean performedChanges() {
		// TODO Auto-generated method stub
		return false;
	}
}