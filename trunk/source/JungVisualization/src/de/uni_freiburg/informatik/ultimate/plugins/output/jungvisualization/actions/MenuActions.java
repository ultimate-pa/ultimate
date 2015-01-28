package de.uni_freiburg.informatik.ultimate.plugins.output.jungvisualization.actions;

import java.util.HashMap;

import org.eclipse.jface.action.IAction;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.IWorkbenchWindowActionDelegate;
import org.eclipse.ui.PlatformUI;

import de.uni_freiburg.informatik.ultimate.plugins.output.jungvisualization.editor.JungEditor;
import de.uni_freiburg.informatik.ultimate.plugins.output.jungvisualization.editor.JungEditorInput;
import edu.uci.ics.jung.visualization.control.DefaultModalGraphMouse;
import edu.uci.ics.jung.visualization.control.ModalGraphMouse;

/**
 * Contains actions of the main menu.
 * 
 * @see {@link IWorkbenchWindowActionDelegate}
 * @author lena
 * 
 */
public class MenuActions implements IWorkbenchWindowActionDelegate {

	public enum Mode {
		PICKING, TRANSFORMING
	}

	private final HashMap<Mode, IAction> mRadioActions;

	public MenuActions() {
		mRadioActions = new HashMap<Mode, IAction>();
	}

	public Mode getMode() {
		JungEditorInput editorInput = getActiveEditorInput();
		if (editorInput == null) {

			return Mode.PICKING;
		}

		return editorInput.getMode();
	}

	/**
	 * Sets the working mode in the system propery MenuActions.SYSTEM_MODE. Is
	 * called when a user switches between Picking and Transforming modes.
	 * Synchronizes radio buttons in the context menu with those in the main
	 * menu.
	 * 
	 * @param mode
	 *            String either MenuActions.MODE_PICKING or
	 *            MenuActions.MODE_TRANSFORMING
	 */
	public void setMode(JungEditorInput editorInput, Mode mode) {
		assert editorInput != null;
		editorInput.setMode(mode);

		if (mRadioActions.containsKey(Mode.PICKING) && mRadioActions.containsKey(Mode.TRANSFORMING)) {
			IAction pickingAction = mRadioActions.get(Mode.PICKING);
			IAction transformingAction = mRadioActions.get(Mode.TRANSFORMING);
			if (mode.equals(Mode.PICKING)) {
				pickingAction.setChecked(true);
				transformingAction.setChecked(false);
			} else {
				pickingAction.setChecked(false);
				transformingAction.setChecked(true);
			}
		}
	}

	@Override
	public void dispose() {
	}

	@Override
	public void init(IWorkbenchWindow window) {
	
	}

	@Override
	public void run(IAction action) {

		String actionID = action.getId();
		JungEditorInput input = getActiveEditorInput();

		if (input == null) {
			return;
		}

		if (actionID.endsWith("ExportAsSVG")) {
			CommandExportAsSVG cmd = new CommandExportAsSVG();
			cmd.exportAsSVG(input);
		} else if (actionID.endsWith("Mode")) {
			changeMode(action, input);
		} else if (actionID.endsWith("KeyHelp")) {
			CommandShowKeyHelp cmd = new CommandShowKeyHelp();
			cmd.openKeyHelp();
		}

	}

	private JungEditorInput getActiveEditorInput() {
		IWorkbenchWindow wbwindow = PlatformUI.getWorkbench().getActiveWorkbenchWindow();
		if (wbwindow != null) {
			IWorkbenchPage wbpage = wbwindow.getActivePage();
			if (wbpage != null) {
				IEditorPart activeEditor = wbpage.getActiveEditor();
				if (activeEditor != null) {
					IEditorInput editorInput = activeEditor.getEditorInput();
					if (editorInput instanceof JungEditorInput) {
						return (JungEditorInput) editorInput;
					}
				}
			}
		}
		return null;
	}
	
	
	@Override
	public void selectionChanged(IAction action, ISelection selection) {

		IWorkbenchWindow wbwindow = PlatformUI.getWorkbench().getActiveWorkbenchWindow();
		if (wbwindow != null) {
			boolean editorOpened = false;
			IWorkbenchPage wbpage = wbwindow.getActivePage();
			if (wbpage != null) {
				editorOpened = wbpage.getActiveEditor() instanceof JungEditor;
			}

			action.setEnabled(editorOpened);
			if (editorOpened) {
				if (action.getId().endsWith("PickingMode")) {
					mRadioActions.put(Mode.PICKING, action);
				}
				if (action.getId().endsWith("TransformingMode")) {
					mRadioActions.put(Mode.TRANSFORMING, action);
				}
			}
		}
	}

	/**
	 * Switches between PICKING and TRANSFORMING modes.
	 * 
	 * @param action
	 *            The action of the main menu.
	 */
	public void changeMode(IAction action, JungEditorInput editorInput) {
		assert editorInput != null;
		DefaultModalGraphMouse<?, ?> gm = (DefaultModalGraphMouse<?, ?>) editorInput.getViewer().getGraphMouse();

		if (action.getId().endsWith("PickingMode")) {
			if (action.isChecked()) {
				gm.setMode(ModalGraphMouse.Mode.PICKING);
				editorInput.setMode(Mode.PICKING);
			}
		} else if (action.getId().endsWith("TransformingMode")) {
			if (action.isChecked()) {
				gm.setMode(ModalGraphMouse.Mode.TRANSFORMING);
				editorInput.setMode(Mode.TRANSFORMING);
			}
		}

	}

}
