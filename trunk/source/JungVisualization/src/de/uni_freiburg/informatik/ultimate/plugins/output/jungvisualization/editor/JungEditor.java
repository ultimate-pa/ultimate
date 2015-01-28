package de.uni_freiburg.informatik.ultimate.plugins.output.jungvisualization.editor;

import java.awt.BorderLayout;
import java.awt.Frame;

import javax.swing.JPanel;

import de.uni_freiburg.informatik.ultimate.model.structure.VisualizationEdge;
import de.uni_freiburg.informatik.ultimate.model.structure.VisualizationNode;
import de.uni_freiburg.informatik.ultimate.plugins.output.jungvisualization.actions.MenuActions.Mode;
import de.uni_freiburg.informatik.ultimate.plugins.output.jungvisualization.graph.GraphListener;
import de.uni_freiburg.informatik.ultimate.plugins.output.jungvisualization.selection.JungSelectionProvider;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.swt.SWT;
import org.eclipse.swt.awt.SWT_AWT;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorSite;
import org.eclipse.ui.IPartListener;
import org.eclipse.ui.IWorkbenchPart;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.part.EditorPart;

import edu.uci.ics.jung.visualization.VisualizationViewer;
import edu.uci.ics.jung.visualization.control.DefaultModalGraphMouse;
import edu.uci.ics.jung.visualization.control.ModalGraphMouse;

/**
 * Defines an editor for the JungVisualization plug-in.
 * 
 * @see {@link EditorPart}
 * @see {@link IPartListener}
 * @author lenalena
 */
public class JungEditor extends EditorPart implements IPartListener {

	public static final String ID = "de.uni_freiburg.informatik.ultimate.plugins.output.jungvisualization.editor.JungEditor";
	public static final String VV_ID_EDITOR_PROPERTY_KEY = "VisualizationViewerID";

	@Override
	public void doSave(IProgressMonitor monitor) {

	}

	@Override
	public void doSaveAs() {

	}

	@Override
	public void init(IEditorSite site, IEditorInput input) throws PartInitException {
		setSite(site);
		setInput(input);
		setPartName(((JungEditorInput) input).getName());
		site.getWorkbenchWindow().getPartService().addPartListener(this);
	}

	@Override
	public boolean isDirty() {
		return false;
	}

	@Override
	public boolean isSaveAsAllowed() {
		return false;
	}

	@Override
	public boolean isSaveOnCloseNeeded() {
		return false;
	}

	@Override
	public void createPartControl(Composite parent) {
		JungEditorInput ei = (JungEditorInput) getEditorInput();
		String currentVVID = ei.getId();
		setPartProperty(VV_ID_EDITOR_PROPERTY_KEY, currentVVID);

		Composite comp = new Composite(parent, SWT.EMBEDDED);
		Frame awt = SWT_AWT.new_Frame(comp);

		JPanel panel = new JPanel();
		panel.setLayout(new BorderLayout());
		final VisualizationViewer<VisualizationNode, VisualizationEdge> vv = ei.getViewer();
		vv.setPreferredSize(panel.getSize());

		JungSelectionProvider jsp = new JungSelectionProvider();
		getSite().setSelectionProvider(jsp);

		GraphListener gl = new GraphListener(jsp,ei);

		DefaultModalGraphMouse<VisualizationNode, VisualizationEdge> graphMouse = new DefaultModalGraphMouse<VisualizationNode, VisualizationEdge>();
		graphMouse.setZoomAtMouse(true);

		ei.setMode(Mode.PICKING);
		graphMouse.setMode(ModalGraphMouse.Mode.PICKING);
		
		graphMouse.add(gl);

		vv.setGraphMouse(graphMouse);

		panel.add(vv, BorderLayout.CENTER);

		panel.setVisible(true);
		awt.add(panel);
		

	}

	@Override
	public void setFocus() {
	}

	@Override
	public void partActivated(IWorkbenchPart part) {
		// TODO Auto-generated method stub

	}

	@Override
	public void partBroughtToTop(IWorkbenchPart part) {
		// TODO Auto-generated method stub

	}

	@Override
	public void partClosed(IWorkbenchPart part) {
		if (part == this) {
			part.getSite().getWorkbenchWindow().getPartService().removePartListener(this);
		}
	}

	@Override
	public void partDeactivated(IWorkbenchPart part) {
		// TODO Auto-generated method stub

	}

	@Override
	public void partOpened(IWorkbenchPart part) {
		// TODO Auto-generated method stub

	}

}
