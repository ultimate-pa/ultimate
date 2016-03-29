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

import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;

import javax.swing.JMenuItem;
import javax.swing.JOptionPane;
import javax.swing.JPopupMenu;
import javax.swing.event.DocumentEvent;
import javax.swing.event.DocumentListener;

import de.uni_muenster.cs.sev.lethal.factories.StateFactory;
import de.uni_muenster.cs.sev.lethal.hedgeautomaton.EasyHAOps;
import de.uni_muenster.cs.sev.lethal.hedgeautomaton.EasyHedgeAutomaton;
import de.uni_muenster.cs.sev.lethal.hedgeautomaton.HAOps;
import de.uni_muenster.cs.sev.lethal.hedgeautomaton.HedgeAutomaton;
import de.uni_muenster.cs.sev.lethal.parser.hedgeautomaton.HedgeAutomatonParser;
import de.uni_muenster.cs.sev.lethal.parser.hedgegrammar.HedgeGrammarParser;
import de.uni_muenster.cs.sev.lethal.states.HedgeState;
import de.uni_muenster.cs.sev.lethal.states.State;
import de.uni_muenster.cs.sev.lethal.symbol.common.RankedSymbol;
import de.uni_muenster.cs.sev.lethal.symbol.common.UnrankedSymbol;
import de.uni_muenster.cs.sev.lethal.symbol.special.HedgeSymbol;
import de.uni_muenster.cs.sev.lethal.symbol.standard.StdNamedRankedSymbol;
import de.uni_muenster.cs.sev.lethal.tree.common.Tree;
import de.uni_muenster.cs.sev.lethal.treeautomata.common.FTA;
import de.uni_muenster.cs.sev.lethal.treeautomata.common.FTAOps;
import de.uni_muenster.cs.sev.lethal.treeautomata.easy.EasyFTACreator;
import de.uni_muenster.cs.sev.lethal.treeautomata.easy.EasyFTAOps;
import de.uni_muenster.cs.sev.lethal.utils.Converter;

/**
 * GUI Editor window for hedge automata.
 * @author Philipp, Sezar
 *
 */
public class HedgeAutomatonEditor extends AbstractTreeAutomatonEditor {

	/**
	 * Item edited by this editor.
	 */
	private HedgeAutomatonItem item;

	/**
	 * Creates a new hedge automaton editor.
	 * @param item item to edit
	 */
	public HedgeAutomatonEditor(final HedgeAutomatonItem item) {
		super(item);
		this.item = item;

		if (item.getAutomatonString() != null){
			this.editorTextField.setText(item.getAutomatonString());
		}

		this.editorTextField.getDocument().addDocumentListener(new DocumentListener(){
			public void changedUpdate(DocumentEvent e){setDirty(true);}
			public void insertUpdate(DocumentEvent e) {setDirty(true);}
			public void removeUpdate(DocumentEvent e) {setDirty(true);}
		});

		this.quickApplyButton.addActionListener(new ActionListener(){
			public void actionPerformed(ActionEvent e) {
				final HedgeAutomaton<UnrankedSymbol,State> automaton = tryParseCurrentAutomaton();
				if (automaton == null) return; 

				JPopupMenu menu = new JPopupMenu();
				ApplyEvent<HedgeItem> hedgeApplyAction = new ApplyEvent<HedgeItem>(){
					public void apply(HedgeItem hedgeItem){
						try{
							Tree<UnrankedSymbol> hedge = hedgeItem.getTree();
							if (HAOps.decide(automaton, hedge)){
								JOptionPane.showMessageDialog(HedgeAutomatonEditor.this, "Tree '" + hedgeItem.getName() + "' accepted!", "Quick Apply", JOptionPane.INFORMATION_MESSAGE);
							} else {
								JOptionPane.showMessageDialog(HedgeAutomatonEditor.this, "Tree '" + hedgeItem.getName() + "' NOT accepted :(", "Quick Apply", JOptionPane.INFORMATION_MESSAGE);
							}
						} catch (Exception ex) {
							ex.printStackTrace();
							JOptionPane.showMessageDialog(HedgeAutomatonEditor.this, "Failed to apply this automaton on '" + hedgeItem.getName() + "':\n" + ex.toString() , "Quick Apply", JOptionPane.ERROR_MESSAGE);
						}
					}
				};
				menu.add(generateApplyMenu(item.getProject(), HedgeItem.class, hedgeApplyAction));
				
				menu.addSeparator();
				JMenuItem complementApplyMenu = new JMenuItem("Complement");
				menu.add(complementApplyMenu);
				complementApplyMenu.addActionListener(new ActionListener(){
					@Override
					public void actionPerformed(ActionEvent e) {
						new TreeAutomatonDisplayWindow(
								EasyHAOps.complement(automaton),
								HedgeAutomatonEditor.this.item.getProject(),
								HedgeAutomatonEditor.this.item.getName() + "_complement",
								HedgeAutomatonEditor.this.item,
								"Complement " + HedgeAutomatonEditor.this.item.getName());
					}
				});
				JMenuItem finiteLanguageApplyMenu = new JMenuItem("Has finite language?");
				menu.add(finiteLanguageApplyMenu);
				finiteLanguageApplyMenu.addActionListener(new ActionListener(){
					@Override
					public void actionPerformed(ActionEvent e) {
						String s =(HAOps.finiteLanguage(automaton) ? "a FINITE" : "an infinite");
						JOptionPane.showMessageDialog(HedgeAutomatonEditor.this, "This hedge automaton has " + s + " language.", "Has finite language?", JOptionPane.INFORMATION_MESSAGE);
					}
				});
				menu.addSeparator();
				JMenuItem exampleTreeMenu = new JMenuItem("Accepted tree example");
				menu.add(exampleTreeMenu);
				exampleTreeMenu.addActionListener(new ActionListener(){
					@Override
					public void actionPerformed(ActionEvent e) {
						Tree<RankedSymbol> tree = EasyFTAOps.constructTreeFrom((FTA)automaton.getTA());
						if (tree == null){
							JOptionPane.showMessageDialog(HedgeAutomatonEditor.this, "This HA has does not accept anything :(", "You messed up", JOptionPane.WARNING_MESSAGE);
						} else {
							new TreeDisplayWindow(tree,
												  item.getProject(),
												  item.getName() + "_exampletree",
												  null,
												  null,
												  "Example tree accepted by " + item.getName());
							
						}
					}
				});
				
				menu.addSeparator();
				
				JMenuItem convertApplyMenu = new JMenuItem("Convert to Finite Tree Automaton");
				menu.add(convertApplyMenu);
				convertApplyMenu.addActionListener(new ActionListener(){
					@Override
					public void actionPerformed(ActionEvent e) {
						new TreeAutomatonDisplayWindow(
								FTAOps.ftaConverter(
										automaton.getTA(),
										new Converter<HedgeState<State>,State>(){
											@Override
											public State convert(HedgeState<State> a) {
												return StateFactory.getStateFactory().makeState(a.toString());
											}
										},
										new Converter<HedgeSymbol<UnrankedSymbol>, RankedSymbol>(){
											@Override
											public RankedSymbol convert(HedgeSymbol<UnrankedSymbol> a) {
												return new StdNamedRankedSymbol<String>(a.toString(), a.getArity());
											}
										},
										new EasyFTACreator()
								),
								HedgeAutomatonEditor.this.item.getProject(),
								HedgeAutomatonEditor.this.item.getName() + "_converted",
								null,
								"Convert HA '" + HedgeAutomatonEditor.this.item.getName() + "' to FTA"); 
					}
				});
				
				initTreePreview(menu);
				
				menu.show(quickApplyButton, 0, quickApplyButton.getHeight());
			}
		});

		setDirty(false);
	}


	@Override
	protected boolean saveToItem(){
		EasyHedgeAutomaton automaton = tryParseCurrentAutomaton();
		if (automaton != null){
			HedgeAutomatonEditor.this.item.setAutomaton(automaton, this.editorTextField.getText(), this.inputMode);

			setDirty(false);
			return true;
		} else {
			return false;
		}
	}

	/**
	 * Tries to parse the current text in the editor as a hedge automaton and returns it.<br>
	 * If the parsing fails an error message is shown and null is returned.
	 * @return the resulting hedge automaton
	 */
	private EasyHedgeAutomaton tryParseCurrentAutomaton(){
		String rulesString = HedgeAutomatonEditor.this.editorTextField.getText();
		try {
			if (this.inputMode == AbstractTreeAutomatonItem.INPUT_MODE_GRAMMAR){
				return HedgeGrammarParser.parseString(rulesString).getHA();
			} else {
				return HedgeAutomatonParser.parseString(rulesString);
			}
		} catch (de.uni_muenster.cs.sev.lethal.parser.hedgeautomaton.TokenMgrError ex) {
			JOptionPane.showMessageDialog(HedgeAutomatonEditor.this, "Hedge Automaton Parser Exception:\n" + ex.getMessage(), this.item.getName(), JOptionPane.ERROR_MESSAGE);
			return null;
		} catch (de.uni_muenster.cs.sev.lethal.parser.hedgeautomaton.ParseException ex) {
			JOptionPane.showMessageDialog(HedgeAutomatonEditor.this, "Hedge Automaton Parser Exception:\n" + ex.getMessage(), this.item.getName(), JOptionPane.ERROR_MESSAGE);
			return null;
		} catch (de.uni_muenster.cs.sev.lethal.parser.hedgegrammar.TokenMgrError ex) {
			JOptionPane.showMessageDialog(HedgeAutomatonEditor.this, "Hedge Grammar Parser Exception:\n" + ex.getMessage(), this.item.getName(), JOptionPane.ERROR_MESSAGE);
			return null;
		} catch (de.uni_muenster.cs.sev.lethal.parser.hedgegrammar.ParseException ex) {
			JOptionPane.showMessageDialog(HedgeAutomatonEditor.this, "Hedge Grammar Parser Exception:\n" + ex.getMessage(), this.item.getName(), JOptionPane.ERROR_MESSAGE);
			return null;
		}
	}

	@Override
	protected AbstractTreeAutomatonItem getItem() {
		return this.item;
	}

	@Override
	public String getName() {
		return "Hedge Automaton Editor";
	}

}
