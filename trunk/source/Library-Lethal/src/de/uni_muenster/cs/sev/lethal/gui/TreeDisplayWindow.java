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
import java.util.*;

import javax.swing.*;

import de.uni_muenster.cs.sev.lethal.parser.tree.ParseException;
import de.uni_muenster.cs.sev.lethal.parser.tree.TokenMgrError;
import de.uni_muenster.cs.sev.lethal.parser.tree.TreeParser;

import de.uni_muenster.cs.sev.lethal.states.State;
import de.uni_muenster.cs.sev.lethal.symbol.common.*;
import de.uni_muenster.cs.sev.lethal.tree.common.Tree;
import de.uni_muenster.cs.sev.lethal.treeautomata.common.FTARule;

import de.uni_muenster.cs.sev.lethal.gui.Project.InvalidItemNameException;


/**
 * Window that shows a tree (or hedge) to the user.<br>
 * Tree Annotations with states are supported.
 * Final state highlighting is supported.
 * The window optionally allows adding the shown tree to the project.
 * @author Philipp
 *
 */
public class TreeDisplayWindow extends JFrame {

	private JToolBar toolbar = new JToolBar();
	private JButton closeButton = new JButton("Discard");
	private JButton addButton = new JButton("Add to Project");
	private JTextField nameField = new JTextField("newtree");
	
	/**
	 * Creates and shows a new TreeDisplayWindow.
	 * @param tree tree or hedge to show
	 * @param project project to add the tree to when the user clicks "Add to Project". 
	 * If null, the tree cannot be added to a project and the controls for that will be removed.
	 * @param suggestedName suggested name when added to the project. It may be null.
	 * @param finalStates final state to highlight. This parameter may be null.
	 * @param stateAnnotations hashmap that stores the state annotations for (sub)trees.
	 * @param title window title. If null it just reads "Tree Display".
	 */
	public TreeDisplayWindow(final Tree<? extends Symbol> tree, final Project project, String suggestedName, Set<? extends State> finalStates, Map<Tree<RankedSymbol>, Set<FTARule<RankedSymbol,State>>> stateAnnotations, String title){
		Map<Tree<? extends Symbol>,NodeAnnotation> nodeAnnotations = new HashMap<Tree<? extends Symbol>,NodeAnnotation>();
		if (stateAnnotations != null){
			for (Tree<? extends Symbol> key : stateAnnotations.keySet()){
				Set<FTARule<RankedSymbol,State>> rules = stateAnnotations.get(key);
				Set<State> states = new HashSet<State>(rules.size());
				StringBuffer toolTip = new StringBuffer();
				toolTip.append("<html><b>Applied Rules:</b>");
				boolean isFinal = false;
				for (FTARule<RankedSymbol,State> rule : rules){
					states.add(rule.getDestState());
					
					toolTip.append("<br />");
					toolTip.append(rule.toString().replaceAll(">", "&gt;") );
					
					if (finalStates.contains(rule.getDestState())){
						toolTip.append("<i>!</i>");
						isFinal = true;
					}
				}
				toolTip.append("</html>");
				if (!states.isEmpty()) nodeAnnotations.put(key, new NodeAnnotation(states.toString(), toolTip.toString(), isFinal));
			}
		}
		
		this.closeButton.addActionListener(new ActionListener(){
			@Override
			public void actionPerformed(ActionEvent e) {
				TreeDisplayWindow.this.dispose();
			}
		});
		this.addButton.addActionListener(new ActionListener(){
			@Override
			public void actionPerformed(ActionEvent e) {
				String name = TreeDisplayWindow.this.nameField.getText();
				try{
					project.checkValidNewItemName(name);
				} catch (InvalidItemNameException ex){
					JOptionPane.showMessageDialog(TreeDisplayWindow.this, ex.getMessage(), "Invalid Name", JOptionPane.ERROR_MESSAGE);
					return;
				}
				try {
					project.addItem(AbstractTreeItem.fromTree(name, project, TreeParser.parseString(tree.toString(), tree.getSymbolClass())));
				} catch (ParseException e1) {
					e1.printStackTrace();
				}
				TreeDisplayWindow.this.dispose();
			}
		});
		
		this.setLayout(new BorderLayout());
		
		TreeViewer tv = new TreeViewer(tree,nodeAnnotations);
		this.add(tv, BorderLayout.CENTER);
		
		if (project != null){
			toolbar.add(this.closeButton);
			toolbar.addSeparator();
			toolbar.add(new JLabel("Name:"));
			toolbar.add(this.nameField);
			toolbar.add(this.addButton);
			
			if (suggestedName == null) suggestedName = "newtree";
			suggestedName = project.convertToValidNewItemName(suggestedName);
			this.nameField.setText(suggestedName);
			
			this.add(toolbar, BorderLayout.NORTH);
			
			try {
				TreeParser.parseString(tree.toString(), tree.getSymbolClass());
			} catch (TokenMgrError ex){
				ex.printStackTrace();
				JOptionPane.showMessageDialog(this, "Can't parse tree back in. This is a bug probably caused by bogus or parser unsupported toString implementation for Symbols the Tree", "Tree Parse Exception", JOptionPane.ERROR_MESSAGE);
				this.nameField.setEnabled(false);
				this.addButton.setEnabled(false);
			} catch (ParseException ex){
				ex.printStackTrace();
				JOptionPane.showMessageDialog(this, "Can't parse tree back in. This is a bug probably caused by bogus or parser unsupported toString implementation for Symbols the Tree", "Tree Parse Exception", JOptionPane.ERROR_MESSAGE);
				this.nameField.setEnabled(false);
				this.addButton.setEnabled(false);
			}
		}
		
		this.setTitle("Tree Display" + ((title != null) ? " - " + title : ""));
		this.setSize(500,400);
		this.setVisible(true);
	}

}