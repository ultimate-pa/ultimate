/*
 * Copyright 2009 Dorothea Jansen <d.jansen@uni-muenster.de>, Martin Mohr <mohrfrosch@uni-muenster.de>, Irene Thesing <i_thes01@uni-muenster.de>, Anton Reis <antonreis@gmx.de>, Maria Schatz <m_scha17@uni-muenster.de>, Philipp Claves <philipp.claves@uni-muenster.de>, Sezar Jarrous <sezar.jarrous@gmail.com>
 *
 * This file is part of LETHAL.
 *
 * LETHAL is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * LETHAL is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with LETHAL.  If not, see <http://www.gnu.org/licenses/>.
 */
package de.uni_muenster.cs.sev.lethal.gui;

import de.uni_muenster.cs.sev.lethal.gui.Project.ProjectEventListener;

import java.awt.BorderLayout;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.util.Arrays;
import java.util.List;

import javax.swing.*;
/**
 * Abstract superclass for FTA and Hedge Automaton editors.
 * @author Philipp, Sezar
 *
 */
public abstract class AbstractTreeAutomatonEditor extends Editor {
	
	/** Last hope for despaired users. */
	protected JButton helpButton = new JButton("Help",Resources.loadIcon("help.png"));
	/** Button to apply some operations. */
	protected JButton quickApplyButton = new JButton("Quick Operations", Resources.loadIcon("fta-quickops.png"));

	/** Text field in which the user enters new rules. */
	protected JTextArea editorTextField = new JTextArea();

	/** Index for the current parser. */
	protected int inputMode = AbstractTreeAutomatonItem.INPUT_MODE_RULES;

	/** Button to select how the Automaton will be given. */
	protected JButton selectInputButton = new JButton("Input mode", Resources.loadIcon("input-mode.png"));
	
	/** Names for the two input modes: Rules and Grammar.*/
	protected final List<String> inputModeNames = Arrays.asList("Rules", "Grammar");
	
	/** Event listener for project events, used to monitor if the item has been changed while opened in the editor */
	protected ProjectEventListener projectListener;
	
	/**
	 * Constructs editor window from given AbstractTreeAutomatonItem.
	 * @param item @see("AbstractTreeAutomatonItem#.")
	 */
	public AbstractTreeAutomatonEditor(final AbstractTreeAutomatonItem item){
		super(item);
		setInputMode(item.inputMode);
		
		this.setLayout(new BorderLayout());
		this.add(toolbar, BorderLayout.NORTH);
		
		this.toolbar.add(this.selectInputButton,2);
		this.selectInputButton.addActionListener(new ActionListener(){
			public void actionPerformed(ActionEvent e) {
				ActionListener l = new ActionListener(){
					public void actionPerformed(ActionEvent e) {
						AbstractTreeAutomatonEditor.this.setInputMode(inputModeNames.indexOf( ((JMenuItem)e.getSource()).getText() ));
					}
				};
				
				JPopupMenu menu = new JPopupMenu();
				for (int i = 0; i < inputModeNames.size(); i++){
					JMenuItem item = new JRadioButtonMenuItem(inputModeNames.get(i), AbstractTreeAutomatonEditor.this.inputMode == i);
					item.addActionListener(l);
					menu.add(item);
				}
				menu.show(AbstractTreeAutomatonEditor.this.selectInputButton, 0, AbstractTreeAutomatonEditor.this.selectInputButton.getHeight());
			} 
		});
		
		this.toolbar.add(this.quickApplyButton);
		this.toolbar.add(new JToolBar.Separator());
		this.toolbar.add(this.helpButton);

		this.add(new JScrollPane(editorTextField), BorderLayout.CENTER);
	}
	
	/**
	 * Sets the input mode.
	 * 
	 * @param mode new input mode.
	 */
	protected void setInputMode(int mode){
		this.inputMode = mode;
		this.selectInputButton.setText(inputModeNames.get(mode) + " input mode");
	}
	
	/**
	 * Action on close of the editor window, unregister the project event listener if any.
	 */
	@Override
	public void close(){
		if (this.projectListener != null) this.getItem().getProject().removeProjectListener(this.projectListener);
		super.close();
	}

}
