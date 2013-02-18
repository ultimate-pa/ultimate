package local.stalin.plugins.output.jungvisualization.actions;

import java.awt.event.WindowAdapter;
import java.awt.event.WindowEvent;
import java.io.BufferedReader;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.net.URL;
import java.util.Collection;
import java.util.HashMap;
import java.util.Iterator;

import javax.swing.JFileChooser;
import javax.swing.JFrame;
import javax.swing.JLabel;
import javax.swing.SwingConstants;

import local.stalin.model.IEdge;
import local.stalin.model.INode;
import local.stalin.plugins.output.jungvisualization.Activator;
import local.stalin.plugins.output.jungvisualization.editor.JungEditor;
import local.stalin.plugins.output.jungvisualization.graph.GraphHandler;
import local.stalin.plugins.output.jungvisualization.preferences.PreferenceValues;

import org.apache.batik.dom.GenericDOMImplementation;
import org.apache.batik.dom.svg.SVGDOMImplementation;
import org.apache.batik.svggen.SVGGraphics2D;
import org.eclipse.core.runtime.Platform;
import org.eclipse.core.runtime.preferences.ConfigurationScope;
import org.eclipse.core.runtime.preferences.IEclipsePreferences;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.IWorkbenchWindowActionDelegate;
import org.eclipse.ui.PlatformUI;
import org.w3c.dom.DOMImplementation;
import org.w3c.dom.Document;

import edu.uci.ics.jung.visualization.VisualizationViewer;
import edu.uci.ics.jung.visualization.control.DefaultModalGraphMouse;
import edu.uci.ics.jung.visualization.control.ModalGraphMouse;

/**
 * Contains actions of the main menu.
 * @see {@link IWorkbenchWindowActionDelegate}
 * @author lena
 *
 */
public class MenuActions implements IWorkbenchWindowActionDelegate {
	
	public static HashMap<String, IAction> radioActions = new HashMap<String, IAction>();
	public final static String MODE_PICKING = "Picking";
	public final static String MODE_TRANSFORMING = "Transforming";
	public final static String SYSTEM_MODE = "Mode";
	private final static String SYSTEM_KEY_HELP_STATE = "KeyHelpState";
	private static String activeEditorVVID;
	
	public static String getMode() {
		String mode = System.getProperty(SYSTEM_MODE);
		if(mode == null)
		{
			mode = MODE_PICKING;
		}
		return mode;
	}
	
	/**
	 * Sets the working mode in the system propery MenuActions.SYSTEM_MODE.
	 * Is called when a user switches between Picking and Transforming modes.
	 * Synchronizes radio buttons in the context menu with those in the main menu.
	 * 
	 * @param mode String either MenuActions.MODE_PICKING or MenuActions.MODE_TRANSFORMING
	 */
	public static void setMode(String mode){

		if (mode.equals(MODE_PICKING) || mode.equals(MODE_TRANSFORMING)){
			System.setProperty(SYSTEM_MODE, mode);

			if (radioActions.containsKey(MODE_PICKING) && radioActions.containsKey(MODE_TRANSFORMING)){
				IAction pickingAction = radioActions.get(MODE_PICKING);
				IAction transformingAction = radioActions.get(MODE_TRANSFORMING);
				if (mode.equals(MODE_PICKING)) 
				{
					pickingAction.setChecked(true);
					transformingAction.setChecked(false);
				}
				else 
				{
					pickingAction.setChecked(false);
					transformingAction.setChecked(true);
				}
			}
		}
		else
		{
			System.setProperty(SYSTEM_MODE, MODE_PICKING);
		}
	}
	
	@Override
	public void dispose() {
		// TODO Auto-generated method stub
	}

	@Override
	public void init(IWorkbenchWindow window) {
		
	}

	/*
	 * (non-Javadoc)
	 * @see org.eclipse.ui.IActionDelegate#run(org.eclipse.jface.action.IAction)
	 */
	@Override
	public void run(IAction action) {
		
		String actionID = action.getId();
		
		if (actionID.endsWith("ExportAsSVG")){
			exportAsSVG();
		}
		if (actionID.endsWith("Mode")){
			changeMode(action);
		}
		if (actionID.endsWith("KeyHelp")){
			openKeyHelp();
		}
			
	}
	
	/*
	 * (non-Javadoc)
	 * @see org.eclipse.ui.IActionDelegate#selectionChanged(org.eclipse.jface.action.IAction, org.eclipse.jface.viewers.ISelection)
	 */
	@Override
	public void selectionChanged(IAction action, ISelection selection) {
		boolean editorOpened = PlatformUI.getWorkbench().getActiveWorkbenchWindow().getActivePage().getActiveEditor() instanceof JungEditor;
		action.setEnabled(editorOpened);
		if (editorOpened){
			activeEditorVVID = ((JungEditor)PlatformUI.getWorkbench().getActiveWorkbenchWindow().getActivePage().getActiveEditor()).getPartProperty(JungEditor.VV_ID_EDITOR_PROPERTY_KEY);
			if ( action.getId().endsWith("PickingMode") ) {
				radioActions.put(MODE_PICKING, action);
			}
			if ( action.getId().endsWith("TransformingMode") ) {
				radioActions.put(MODE_TRANSFORMING, action);
			}
		}
	}
	
	/**
	 * Exports the graph of the active editor part to a SVG format and saves it.
	 */
	public static void exportAsSVG(){
		ConfigurationScope scope = new ConfigurationScope();
		IEclipsePreferences prefs = scope.getNode(Activator.PLUGIN_ID);
		
		String svgFilePath = prefs.get(PreferenceValues.NAME_PATH, PreferenceValues.VALUE_PATH_DEFAULT);
		
		JFileChooser chooser = new JFileChooser();
		chooser.setSelectedFile(new File(svgFilePath + "/default.svg"));
		chooser.showSaveDialog(null);
		
		String filename = chooser.getSelectedFile().getPath();
		
		DOMImplementation impl = GenericDOMImplementation.getDOMImplementation();
		String svgNS = SVGDOMImplementation.SVG_NAMESPACE_URI;
		Document doc = impl.createDocument(svgNS, "svg", null);
		
		SVGGraphics2D g = new SVGGraphics2D(doc);
		VisualizationViewer<?, ?> vv = GraphHandler.getInstance().getVisualizationViewer(activeEditorVVID);
		vv.setDoubleBuffered(false);
		vv.paint(g);
		vv.setDoubleBuffered(true);
		
		try
        {
        FileWriter fileWriter = new FileWriter(filename);
        g.stream(fileWriter);
        }
        catch (IOException ioEx)
        {
        	ioEx.printStackTrace();
        }
	}
	
	/**
	 * Switches between PICKING and TRANSFORMING modes.
	 * 
	 * @param action The action of the main menu.
	 */
	public static void changeMode(IAction action){
		Collection<VisualizationViewer<INode, IEdge>> openedVVs = GraphHandler.getInstance().getVisualizationViewers().values();
		Iterator<VisualizationViewer<INode, IEdge>> itr = openedVVs.iterator();

		while (itr.hasNext()){

			DefaultModalGraphMouse<?, ?> gm = (DefaultModalGraphMouse<?, ?>)itr.next().getGraphMouse();

			if (action.getId().endsWith("PickingMode"))
			{
				if (action.isChecked()){

					gm.setMode(ModalGraphMouse.Mode.PICKING);
					setMode(MODE_PICKING);
				}

			}
			else if (action.getId().endsWith("TransformingMode"))
			{

				if (action.isChecked()){

					gm.setMode(ModalGraphMouse.Mode.TRANSFORMING);
					setMode(MODE_TRANSFORMING);
				}

			}
		}
	} 
	
	
	/**
	 * Opens a help window.
	 */
	public static void openKeyHelp(){
		String keyHelpState;
		keyHelpState = System.getProperty(SYSTEM_KEY_HELP_STATE);
		
		if (keyHelpState == null)
		{
			keyHelpState = "closed";
		}
		
		if (!keyHelpState.equals("open")){
			URL loc = Platform.getBundle(Activator.PLUGIN_ID).getEntry("data/KeyHelp.html");
			String s = "Help file not found.";

			try {
				InputStream is = loc.openStream();
				BufferedReader in = new BufferedReader(new InputStreamReader(is));
				s = "";
				String temp = in.readLine();
				while (temp != null){
					s += temp;
					temp = in.readLine();
				}
			} catch (IOException e1) {
				e1.printStackTrace(System.err);
			}

			JFrame hf = new JFrame("Key Help");
			JLabel label = new JLabel(s, SwingConstants.CENTER);

			hf.addWindowListener(new WindowAdapter() {
				public void windowClosing(WindowEvent e){
					System.setProperty(SYSTEM_KEY_HELP_STATE, "closed");
				}
			});

			hf.getContentPane().add(label);
			hf.setDefaultCloseOperation(JFrame.HIDE_ON_CLOSE);
			hf.setAlwaysOnTop(true);
			hf.setResizable(false);
			hf.setFocusableWindowState(false);
			hf.pack();
			hf.setVisible(true);
			System.setProperty(SYSTEM_KEY_HELP_STATE, "open");
		}
	}

}
