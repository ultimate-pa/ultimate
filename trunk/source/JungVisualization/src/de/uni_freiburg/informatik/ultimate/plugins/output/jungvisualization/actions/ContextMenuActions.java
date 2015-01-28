package de.uni_freiburg.informatik.ultimate.plugins.output.jungvisualization.actions;

import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;

import de.uni_freiburg.informatik.ultimate.model.structure.VisualizationEdge;
import de.uni_freiburg.informatik.ultimate.model.structure.VisualizationNode;
import de.uni_freiburg.informatik.ultimate.plugins.output.jungvisualization.actions.MenuActions.Mode;
import de.uni_freiburg.informatik.ultimate.plugins.output.jungvisualization.editor.JungEditorInput;
import edu.uci.ics.jung.visualization.VisualizationViewer;
import edu.uci.ics.jung.visualization.control.DefaultModalGraphMouse;
import edu.uci.ics.jung.visualization.control.ModalGraphMouse;

/**
 * Implements ActionListener and overrides the actionPerformed(ActionEvent)
 * method, which manages the logic for the JV context menu.
 * 
 * @see {@link ActionListener}
 * @author lena
 * 
 */
public class ContextMenuActions implements ActionListener {

	public static final String ACTION_EXPORT = "Export as SVG"; // 1
	public static final String ACTION_PICKING = "Picking";// 2
	public static final String ACTION_TRANSFORMING = "Transforming";// 3
	public static final String ACTION_KEYHELP = "Key help";// 4
	public static final String ACTION_COLLAPSE = "Collapse";// 5
	public static final String ACTION_EXTEND = "Extend";// 6
	private final JungEditorInput mEditorInput;

	public ContextMenuActions(JungEditorInput editorInput) {
		assert editorInput != null;
		mEditorInput = editorInput;
	}

	@Override
	public void actionPerformed(ActionEvent e) {

		String actionCommmand = e.getActionCommand();

		if (actionCommmand.equals(ACTION_EXPORT)) {
			CommandExportAsSVG cmd = new CommandExportAsSVG();
			cmd.exportAsSVG(mEditorInput);
		} else if (actionCommmand.equals(ACTION_PICKING)) {
			((DefaultModalGraphMouse<?, ?>) mEditorInput.getViewer().getGraphMouse())
					.setMode(ModalGraphMouse.Mode.PICKING);
			mEditorInput.setMode(Mode.PICKING);
		} else if (actionCommmand.equals(ACTION_TRANSFORMING)) {
			VisualizationViewer<VisualizationNode, VisualizationEdge> current = mEditorInput.getViewer();
			DefaultModalGraphMouse<?, ?> mouse = ((DefaultModalGraphMouse<?, ?>) current.getGraphMouse());
			mouse.setMode(ModalGraphMouse.Mode.TRANSFORMING);
			mEditorInput.setMode(Mode.TRANSFORMING);
		} else if (actionCommmand.equals(ACTION_KEYHELP)) {
			CommandShowKeyHelp cmd = new CommandShowKeyHelp();
			cmd.openKeyHelp();
		}
	}
}
