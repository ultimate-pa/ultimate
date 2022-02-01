/*
 * Copyright (C) 2013-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
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

import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;

import de.uni_freiburg.informatik.ultimate.core.lib.models.VisualizationEdge;
import de.uni_freiburg.informatik.ultimate.core.lib.models.VisualizationNode;
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

		final String actionCommmand = e.getActionCommand();

		if (actionCommmand.equals(ACTION_EXPORT)) {
			final CommandExportAsSVG cmd = new CommandExportAsSVG();
			cmd.exportAsSVG(mEditorInput);
		} else if (actionCommmand.equals(ACTION_PICKING)) {
			((DefaultModalGraphMouse<?, ?>) mEditorInput.getViewer().getGraphMouse())
					.setMode(ModalGraphMouse.Mode.PICKING);
			mEditorInput.setMode(Mode.PICKING);
		} else if (actionCommmand.equals(ACTION_TRANSFORMING)) {
			final VisualizationViewer<VisualizationNode, VisualizationEdge> current = mEditorInput.getViewer();
			final DefaultModalGraphMouse<?, ?> mouse = ((DefaultModalGraphMouse<?, ?>) current.getGraphMouse());
			mouse.setMode(ModalGraphMouse.Mode.TRANSFORMING);
			mEditorInput.setMode(Mode.TRANSFORMING);
		} else if (actionCommmand.equals(ACTION_KEYHELP)) {
			final CommandShowKeyHelp cmd = new CommandShowKeyHelp();
			cmd.openKeyHelp();
		}
	}
}
