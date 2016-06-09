/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
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

import javax.swing.ButtonGroup;
import javax.swing.JMenuItem;
import javax.swing.JPopupMenu;
import javax.swing.JRadioButtonMenuItem;

import de.uni_freiburg.informatik.ultimate.plugins.output.jungvisualization.actions.MenuActions.Mode;
import de.uni_freiburg.informatik.ultimate.plugins.output.jungvisualization.editor.JungEditorInput;

/**
 * The context menu for JV.
 * 
 * @see {@link JPopupMenu}
 * @author lena
 * 
 */
public class JVContextMenu extends JPopupMenu {

	private static final long serialVersionUID = 1L;

	private final ButtonGroup group = new ButtonGroup();
	private final JRadioButtonMenuItem jmi_mode_p = new JRadioButtonMenuItem("Picking");
	private final JRadioButtonMenuItem jmi_mode_t = new JRadioButtonMenuItem("Transforming");

	// private JMenuItem jmi_collapse = new JMenuItem("Collapse");
	// private JMenuItem jmi_extend = new JMenuItem("Extend");

	public JVContextMenu(JungEditorInput editorInput) {
		final ContextMenuActions actions = new ContextMenuActions(editorInput);
		
		
		final JMenuItem jmi_export = new JMenuItem("Export as SVG");
		final JMenuItem jmi_help = new JMenuItem("Key Help");
		
		if (editorInput.getMode().equals(Mode.PICKING)) {
			jmi_mode_p.setSelected(true);
		} else {
			jmi_mode_t.setSelected(true);
		}

		group.add(jmi_mode_p);
		group.add(jmi_mode_t);

		jmi_mode_p.addActionListener(actions);
		jmi_mode_t.addActionListener(actions);
		jmi_help.addActionListener(actions);
		jmi_export.addActionListener(actions);

		jmi_export.setActionCommand(ContextMenuActions.ACTION_EXPORT);
		jmi_mode_p.setActionCommand(ContextMenuActions.ACTION_PICKING);
		jmi_mode_t.setActionCommand(ContextMenuActions.ACTION_TRANSFORMING);
		jmi_help.setActionCommand(ContextMenuActions.ACTION_KEYHELP);

		this.add(jmi_export);
		addSeparator();
		this.add(jmi_mode_p);
		this.add(jmi_mode_t);
		addSeparator();
		this.add(jmi_help);
		// jpm.addSeparator();
		// jpm.add(jmi_collapse);
	}

}
