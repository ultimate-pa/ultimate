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

import java.awt.BorderLayout;
import java.awt.event.*;
import javax.swing.*;

import de.uni_muenster.cs.sev.lethal.parser.fta.FTAParser;
import de.uni_muenster.cs.sev.lethal.parser.fta.ParseException;
import de.uni_muenster.cs.sev.lethal.parser.fta.TokenMgrError;

import de.uni_muenster.cs.sev.lethal.gui.Project.InvalidItemNameException;

import de.uni_muenster.cs.sev.lethal.treeautomata.easy.EasyFTA;
import de.uni_muenster.cs.sev.lethal.hedgeautomaton.EasyHedgeAutomaton;


/**
 * Window showing a Tree/Hedge automaton to the user.
 * Depending on the constructor parameters, the automaton may be added to the current project.
 * @author Philipp
 *
 */
public class TreeAutomatonDisplayWindow extends JFrame {
	
	private JTextArea ftaDisplay = new JTextArea();
	private JToolBar toolbar = new JToolBar();
	private JButton closeButton = new JButton("Discard");
	private JTextField itemNameField = new JTextField();
	private JButton saveButton = new JButton("Add to Project");
	private JButton overwriteButton = new JButton("Overwrite");
	
	/**
	 * Creates and shows a new TreeAutomatonDisplayWindow for a finite tree automaton.
	 * @param fta finite tree automaton to show
	 * @param project project to add the automaton to when the user clicks "Add to Project". 
	 * If null, the automaton cannot be added to a project and the controls for that will be removed.
	 * @param suggestedName suggested name when added to the project. may be null
	 * @param sourceItem if the automaton is derived from an existing item in the project and this is 
	 * passed here, the user can replace the FTA in that item with the one shown here by clicking "Overwrite". 
	 * If sourceItem is null this feature is disabled.
	 * @param title title of the window. May be null, the window title will just be "FTAView" in this case.
	 */
	public TreeAutomatonDisplayWindow(final EasyFTA fta, final Project project, String suggestedName, final FTAItem sourceItem, String title){
		this.setTitle("FTA View" + ((title != null) ? " - " + title : ""));
		
		this.ftaDisplay.setText(fta.toString());
		this.ftaDisplay.setEditable(false);
		
		initCommon(project, suggestedName);
				
		if (sourceItem != null){
			this.toolbar.add(overwriteButton);
			this.overwriteButton.addActionListener(new ActionListener(){
				@Override
				public void actionPerformed(ActionEvent e) {
					sourceItem.setAutomaton(fta, fta.rulesToString(), AbstractTreeAutomatonItem.INPUT_MODE_RULES);
					TreeAutomatonDisplayWindow.this.dispose();
				}
				
			});
		}
		
		if (project != null){
			this.saveButton.addActionListener(new ActionListener(){
				@Override
				public void actionPerformed(ActionEvent e) {
					String name = TreeAutomatonDisplayWindow.this.itemNameField.getText();
					try{
						project.checkValidNewItemName(name);
					} catch (InvalidItemNameException ex){
						JOptionPane.showMessageDialog(TreeAutomatonDisplayWindow.this, ex.getMessage(), "Invalid Name", JOptionPane.ERROR_MESSAGE);
						return;
					}
					String s = fta.rulesToString();
					
					try {
						//use FTAParser to convert possible complex states/symbol to their string version, so that they actually are what they look like on the GUI
						project.addItem(new FTAItem(name, project, FTAParser.parseString(s),s)); 
					} catch (ParseException e1) {
						e1.printStackTrace();
					}
					TreeAutomatonDisplayWindow.this.dispose();
				}
			});
			
			try{
				FTAParser.parseString(fta.rulesToString());
			} catch (TokenMgrError ex){
				JOptionPane.showMessageDialog(this, "Can't parse automaton back in. This is a bug probably caused by bogus or parser unsupported toString implementation for Symbol or States in the FTA", "FTA Parse Exception", JOptionPane.ERROR_MESSAGE);
				this.overwriteButton.setEnabled(false);
				this.itemNameField.setEnabled(false);
				this.saveButton.setEnabled(false);
			} catch (ParseException ex){
				JOptionPane.showMessageDialog(this, "Can't parse automaton back in. This is a bug probably caused by bogus or parser unsupported toString implementation for Symbol or States in the FTA", "FTA Parse Exception", JOptionPane.ERROR_MESSAGE);
				this.overwriteButton.setEnabled(false);
				this.itemNameField.setEnabled(false);
				this.saveButton.setEnabled(false);
			}
			
		}
		
		this.setVisible(true);
	}

	/**
	 * Creates and shows a new TreeAutomatonDisplayWindow for a hedge automaton.
	 * @param project project to add the automaton to when the user clicks "Add to Project".
	 *  FIXME: HA's don't have a parseable output, so this does NOT work and is disabled.
	 * @param suggestedName suggested name when added to the project. may be null
	 * @param sourceItem if the automaton is derived from an existing item in the project and this is passed here, 
	 * the user can replace the finite tree automaton in that item with the one shown here by clicking "Overwrite".  
	 * FIXME: HA's don't have a parse able output, so this does NOT work and is disabled.
	 * @param title title of the window. May be null, the window title will just be "Hedge Automaton View" in this case.
	 * @param ha hedge automaton to show
	*/
	public TreeAutomatonDisplayWindow(final EasyHedgeAutomaton ha, final Project project, String suggestedName, final HedgeAutomatonItem sourceItem, String title){
		this.setTitle("Hedge Automaton View" + ((title != null) ? " - " + title : ""));
		
		this.ftaDisplay.setText(ha.toString());
		this.ftaDisplay.setEditable(false);
		
		initCommon(project, suggestedName);
		
		if (sourceItem != null){
			this.toolbar.add(overwriteButton);
			this.overwriteButton.addActionListener(new ActionListener(){
				@Override
				public void actionPerformed(ActionEvent e) {
					sourceItem.setAutomaton(ha, ha.toString(), AbstractTreeAutomatonItem.INPUT_MODE_RULES);
					TreeAutomatonDisplayWindow.this.dispose();
				}
				
			});
		}
		
		if (project != null){
			this.saveButton.addActionListener(new ActionListener(){
				@Override
				public void actionPerformed(ActionEvent e) {
					String name = TreeAutomatonDisplayWindow.this.itemNameField.getText();
					try{
						project.checkValidNewItemName(name);
					} catch (InvalidItemNameException ex){
						JOptionPane.showMessageDialog(TreeAutomatonDisplayWindow.this, ex.getMessage(), "Invalid Name", JOptionPane.ERROR_MESSAGE);
						return;
					}
					project.addItem(new HedgeAutomatonItem(name, project, ha, ha.toString()));
					TreeAutomatonDisplayWindow.this.dispose();
				}
			});
		}
		
		//FIXME: Can't parse the HA.toString() text representation back in and thus not create an user-reditable item. 
		this.overwriteButton.setEnabled(false);
		this.itemNameField.setEnabled(false);
		this.saveButton.setEnabled(false);
		
		this.setVisible(true);
	}

	
	
	
	private void initCommon(Project project, String suggestedName){
		this.setLayout(new BorderLayout());
		this.add(new JScrollPane(ftaDisplay), BorderLayout.CENTER);
		
		this.add(this.toolbar, BorderLayout.NORTH);
		
		this.toolbar.add(this.closeButton);
		this.closeButton.addActionListener(new ActionListener(){
			@Override
			public void actionPerformed(ActionEvent e) {
				TreeAutomatonDisplayWindow.this.dispose();
			}
		});
		
		if (project != null){
			this.toolbar.addSeparator();
			this.toolbar.add(new JLabel("Name:"));
			this.toolbar.add(this.itemNameField);
			if (suggestedName == null) suggestedName = "newautomaton";
			suggestedName = project.convertToValidNewItemName(suggestedName);
			this.itemNameField.setText(suggestedName);
			
			this.toolbar.add(saveButton);
		}

		this.setSize(500,400);
	}
	
}
