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
import java.awt.Dimension;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.text.NumberFormat;

import javax.swing.*;
import javax.swing.event.*;

import de.uni_muenster.cs.sev.lethal.parser.fta.FTAParser;
import de.uni_muenster.cs.sev.lethal.parser.fta.TokenMgrError;
import de.uni_muenster.cs.sev.lethal.parser.ftagrammar.FTAGrammarParser;
import de.uni_muenster.cs.sev.lethal.symbol.common.RankedSymbol;
import de.uni_muenster.cs.sev.lethal.tree.common.Tree;
import de.uni_muenster.cs.sev.lethal.treeautomata.common.FTAOps;
import de.uni_muenster.cs.sev.lethal.treeautomata.common.FTAProperties;
import de.uni_muenster.cs.sev.lethal.treeautomata.easy.EasyFTA;
import de.uni_muenster.cs.sev.lethal.treeautomata.easy.EasyFTAOps;

/**
 * @author Philipp, Sezar
 * Editor window for Finite Tree Automaton Rules.<br>
 * Rules are entered in text form and the create
 * button is used to create an FTA from the rules.
 */
@SuppressWarnings("serial")
public class FTAEditor  extends AbstractTreeAutomatonEditor {

	/** @see FTAItem */
	protected FTAItem item;
	
	/**
	 * Creates a new FTAEditor.
	 * @param item FTAItem to edit by this editor.
	 */
	public FTAEditor(final FTAItem item){
		super(item);
		this.item = item;

		if (item.getAutomaton() != null){
			this.editorTextField.setText(item.getAutomatonString());
		}
		//Update the text box content if the automaton is updated while this editor is open
		this.projectListener = new ProjectEventListener(){
			@Override
			public void onItemContentSet(Item item) {
				if (item == FTAEditor.this.item){
					FTAEditor.this.editorTextField.setText(FTAEditor.this.item.getAutomatonString());
					setInputMode(FTAEditor.this.item.getInputMode());
					setDirty(false);
				}
			}
		};
		item.getProject().addProjectListener(this.projectListener);

		this.editorTextField.getDocument().addDocumentListener(new DocumentListener(){
			public void changedUpdate(DocumentEvent e){setDirty(true);}
			public void insertUpdate(DocumentEvent e) {setDirty(true);}
			public void removeUpdate(DocumentEvent e) {setDirty(true);}
		});
		
		this.quickApplyButton.addActionListener(new ActionListener(){
			public void actionPerformed(ActionEvent e) {
				final EasyFTA automaton = tryParseCurrentAutomaton();
				if (automaton == null) return; 

				final JPopupMenu menu = new JPopupMenu();
				ApplyEvent<TreeItem> treeApplyAction = new ApplyEvent<TreeItem>(){
					public void apply(TreeItem treeItem){
						try{
							Tree<RankedSymbol> tree = treeItem.getTree();
							new TreeDisplayWindow(
									tree,
									null,
									null,
									automaton.getFinalStates(),
									FTAOps.annotateTreeWithRules(automaton, tree),
									FTAEditor.this.item.getName() + " vs. " + treeItem.getName()
							);
						} catch (Exception ex) {
							JOptionPane.showMessageDialog(FTAEditor.this, "Failed to apply this automaton on '" + treeItem.getName() + "':\n" + ex.getMessage() , "Quick Apply", JOptionPane.ERROR_MESSAGE);
						}
					}
				};
				menu.add(generateApplyMenu(item.getProject(), TreeItem.class, treeApplyAction));

				menu.addSeparator();

				JMenuItem mimimizeApplyMenu = new JMenuItem("Minimize");
				menu.add(mimimizeApplyMenu);
				mimimizeApplyMenu.addActionListener(new ActionListener(){
					@Override
					public void actionPerformed(ActionEvent e) {
						new TreeAutomatonDisplayWindow(
								EasyFTAOps.minimize(FTAProperties.checkDeterministic(automaton) ? automaton : EasyFTAOps.determinize(automaton)),
								FTAEditor.this.item.getProject(),
								FTAEditor.this.item.getName() + "_minimized",
								FTAEditor.this.item,
								"Minimize " + FTAEditor.this.item.getName());
					}
				});
				JMenu reduceApplyMenu = new JMenu("Reduce");
				JMenuItem bottomUpReduceMenu = new JMenuItem("Buttom up");
				bottomUpReduceMenu.addActionListener(new ActionListener(){
					@Override
					public void actionPerformed(ActionEvent e) {
						new TreeAutomatonDisplayWindow(
								EasyFTAOps.reduceBottomUp(automaton),
								FTAEditor.this.item.getProject(),
								FTAEditor.this.item.getName() + "_reduced",
								FTAEditor.this.item,
								"Buttom up reduce " + FTAEditor.this.item.getName());	
					}
				});
				JMenuItem topDownReduceMenu = new JMenuItem("Top down");
				topDownReduceMenu.addActionListener(new ActionListener(){
					@Override
					public void actionPerformed(ActionEvent e) {
						new TreeAutomatonDisplayWindow(
								EasyFTAOps.reduceTopDown(automaton),
								FTAEditor.this.item.getProject(),
								FTAEditor.this.item.getName() + "_reduced",
								FTAEditor.this.item,
								"Top down reduce " + FTAEditor.this.item.getName());	
					}
				});
				JMenuItem fullReduceReduceMenu = new JMenuItem("Both");
				fullReduceReduceMenu.addActionListener(new ActionListener(){
					@Override
					public void actionPerformed(ActionEvent e) {
						new TreeAutomatonDisplayWindow(
								EasyFTAOps.reduceFull(automaton),
								FTAEditor.this.item.getProject(),
								FTAEditor.this.item.getName() + "_reduced",
								FTAEditor.this.item,
								"Full reduce " + FTAEditor.this.item.getName());	
					}
				});
				reduceApplyMenu.add(bottomUpReduceMenu);
				reduceApplyMenu.add(topDownReduceMenu);
				reduceApplyMenu.add(fullReduceReduceMenu);
				menu.add(reduceApplyMenu);
				
				JMenuItem determinizeApplyMenu = new JMenuItem("Determinize");
				menu.add(determinizeApplyMenu);
				determinizeApplyMenu.addActionListener(new ActionListener(){
					@Override
					public void actionPerformed(ActionEvent e) {
						new TreeAutomatonDisplayWindow(
								EasyFTAOps.determinize(automaton),
								FTAEditor.this.item.getProject(),
								FTAEditor.this.item.getName() + "_determinized",
								FTAEditor.this.item,
								"Determinize " + FTAEditor.this.item.getName());
					}
				});
				JMenuItem completeApplyMenu = new JMenuItem("Complete");
				menu.add(completeApplyMenu);
				
				completeApplyMenu.addActionListener(new ActionListener(){
					@Override
					public void actionPerformed(ActionEvent e) {
						new TreeAutomatonDisplayWindow(
								EasyFTAOps.complete(automaton),
								FTAEditor.this.item.getProject(),
								FTAEditor.this.item.getName() + "_completed",
								FTAEditor.this.item,
								"Complete " + FTAEditor.this.item.getName());
					}
				});
				JMenuItem complementApplyMenu = new JMenuItem("Complement");
				menu.add(complementApplyMenu);
				complementApplyMenu.addActionListener(new ActionListener(){
					@Override
					public void actionPerformed(ActionEvent e) {
						new TreeAutomatonDisplayWindow(
								EasyFTAOps.complement(automaton),
								FTAEditor.this.item.getProject(),
								FTAEditor.this.item.getName() + "_complement",
								FTAEditor.this.item,
								"Complement " + FTAEditor.this.item.getName());
					}
				});
				JMenuItem finiteLanguageApplyMenu = new JMenuItem("Has finite language?");
				menu.add(finiteLanguageApplyMenu);
				finiteLanguageApplyMenu.addActionListener(new ActionListener(){
					@Override
					public void actionPerformed(ActionEvent e) {
						String s =(FTAProperties.finiteLanguage(automaton) ? "a FINITE" : "an infinite");
						JOptionPane.showMessageDialog(FTAEditor.this, "This FTA has " + s + " language.", "Has finite language?", JOptionPane.INFORMATION_MESSAGE);
					}
				});
				menu.addSeparator();
				JMenu exampleTreeMenu = new JMenu("Accepted tree example");
				menu.add(exampleTreeMenu);
				final JMenuItem exampleTreeSmallMenu = new JMenuItem("Any");
				final JMenuItem exampleTreeMinSizeMenu = new JMenuItem("Height at least      ");
				final JTextField minHeightBox = new JFormattedTextField(NumberFormat.getIntegerInstance());
				
				minHeightBox.setText("3");
				minHeightBox.setPreferredSize(new Dimension(25,0));
				exampleTreeMinSizeMenu.setLayout(new BorderLayout());
				exampleTreeMinSizeMenu.add(minHeightBox, BorderLayout.EAST);
				exampleTreeMinSizeMenu.add(new JLabel(" Height at least"), BorderLayout.CENTER);
				exampleTreeMenu.add(exampleTreeSmallMenu);
				exampleTreeMenu.add(exampleTreeMinSizeMenu);
				
				ActionListener exmpleTreeAction = new ActionListener(){
					@Override
					public void actionPerformed(ActionEvent e) {
						Tree<RankedSymbol> tree;
						if (e.getSource() == exampleTreeSmallMenu){
							tree = EasyFTAOps.constructTreeFrom(automaton);
							if (tree == null){
								JOptionPane.showMessageDialog(FTAEditor.this, "This FTA has does not accept anything :(", "You messed up", JOptionPane.WARNING_MESSAGE);
								return;
							}
						} else {
							int minHeight = Integer.parseInt(minHeightBox.getText());
							tree = EasyFTAOps.constructTreeWithMinHeightFrom(automaton, minHeight, false);
							if (tree == null){
								JOptionPane.showMessageDialog(FTAEditor.this, "This FTA has does not accept any tree having at least the given height", "You messed up", JOptionPane.WARNING_MESSAGE);
								return;
							}
						}
						
						new TreeDisplayWindow(tree,
											  item.getProject(),
											  item.getName() + "_exampletree",
											  null,
											  null,
											  "Example tree accepted by " + item.getName());
							
					}
				};
				exampleTreeMinSizeMenu.addActionListener(exmpleTreeAction);
				exampleTreeSmallMenu.addActionListener(exmpleTreeAction);
				
				if (FTAEditor.this.inputMode == AbstractTreeAutomatonItem.INPUT_MODE_GRAMMAR){
					menu.addSeparator();
					JMenuItem rulesConvert = new JMenuItem("Convert Grammar to FTA rules");
					menu.add(rulesConvert);
					rulesConvert.addActionListener(new ActionListener(){
						@Override
						public void actionPerformed(ActionEvent e) {
							new TreeAutomatonDisplayWindow(
								automaton,
								FTAEditor.this.item.getProject(),
								FTAEditor.this.item.getName() + "_rules",
								FTAEditor.this.item,
								"Rules of " + FTAEditor.this.item.getName()
							);
						}
					});
				}
				
				initTreePreview(menu);
				
				menu.show(FTAEditor.this.quickApplyButton, 0, FTAEditor.this.quickApplyButton.getHeight());
			}
		});
		
		this.helpButton.addActionListener(new ActionListener(){
			public void actionPerformed(ActionEvent e) {
				JOptionPane.showMessageDialog(FTAEditor.this, "Enter tree automaton rules using format:\nsymbol(state1,state2,...,stateN) -> deststate\nOr\nstate=>deststate\n\nMark final states with a tailing '!' (e.g 'fstate!').\nNote that a state will become a final state even if only some occurrences are marked with '!'.\n\nOne Rule in each line.", "Help", JOptionPane.INFORMATION_MESSAGE);
			}
		});

		assert(this.dirty == false);
	}

	
	@Override
	protected boolean saveToItem(){
		EasyFTA automaton = tryParseCurrentAutomaton();
		if (automaton != null){
			FTAEditor.this.item.setAutomaton(automaton, this.editorTextField.getText(), this.inputMode);
			
			setDirty(false);
			return true;
		} else {
			return false;
		}
	}

	/**
	 * Tries to parse the current text in the editor as an finite tree automaton and returns it.<br>
	 * If the parsing fails an error message is shown and null is returned.
	 * @return the resulting finite tree automaton
	 */
	private EasyFTA tryParseCurrentAutomaton(){
		String rulesString = FTAEditor.this.editorTextField.getText();
		try {
			if (this.inputMode == AbstractTreeAutomatonItem.INPUT_MODE_GRAMMAR){
				return FTAGrammarParser.parseString(rulesString);
			} else {
				return FTAParser.parseString(rulesString);
			}
		} catch (TokenMgrError ex) {
			ex.printStackTrace();
			JOptionPane.showMessageDialog(FTAEditor.this, "Finite Tree Automaton Parser Exception:\n" + ex.getMessage(), this.item.getName(), JOptionPane.ERROR_MESSAGE);
			return null;
		} catch (Exception ex) {
			ex.printStackTrace();
			JOptionPane.showMessageDialog(FTAEditor.this, "Finite Tree Automaton Parser Exception:\n" + ex.getMessage(), this.item.getName(), JOptionPane.ERROR_MESSAGE);
			return null;
		}
	}

	@Override
	public FTAItem getItem(){
		return this.item;
	}

	@Override
	public String getName(){
		return "Finite Tree Automaton Editor";
	}

}
