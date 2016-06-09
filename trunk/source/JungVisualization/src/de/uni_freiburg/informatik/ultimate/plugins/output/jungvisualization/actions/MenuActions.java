/*
 * Copyright (C) 2012-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Jelena Barth
 * Copyright (C) 2015 University of Freiburg
 * Copyright (C) 2010-2015 pashko
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
		final JungEditorInput editorInput = getActiveEditorInput();
		if (editorInput == null) {

			return Mode.PICKING;
		}

		return editorInput.getMode();
	}

	/**
	 * Sets the working mode in the system propery MenuActions.SYSTEmMODE. Is
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
			final IAction pickingAction = mRadioActions.get(Mode.PICKING);
			final IAction transformingAction = mRadioActions.get(Mode.TRANSFORMING);
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

		final String actionID = action.getId();
		final JungEditorInput input = getActiveEditorInput();

		if (input == null) {
			return;
		}

		if (actionID.endsWith("ExportAsSVG")) {
			final CommandExportAsSVG cmd = new CommandExportAsSVG();
			cmd.exportAsSVG(input);
		} else if (actionID.endsWith("Mode")) {
			changeMode(action, input);
		} else if (actionID.endsWith("KeyHelp")) {
			final CommandShowKeyHelp cmd = new CommandShowKeyHelp();
			cmd.openKeyHelp();
		}

	}

	private JungEditorInput getActiveEditorInput() {
		final IWorkbenchWindow wbwindow = PlatformUI.getWorkbench().getActiveWorkbenchWindow();
		if (wbwindow != null) {
			final IWorkbenchPage wbpage = wbwindow.getActivePage();
			if (wbpage != null) {
				final IEditorPart activeEditor = wbpage.getActiveEditor();
				if (activeEditor != null) {
					final IEditorInput editorInput = activeEditor.getEditorInput();
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

		final IWorkbenchWindow wbwindow = PlatformUI.getWorkbench().getActiveWorkbenchWindow();
		if (wbwindow != null) {
			boolean editorOpened = false;
			final IWorkbenchPage wbpage = wbwindow.getActivePage();
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
		final DefaultModalGraphMouse<?, ?> gm = (DefaultModalGraphMouse<?, ?>) editorInput.getViewer().getGraphMouse();

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
