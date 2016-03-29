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

import de.uni_muenster.cs.sev.lethal.factories.StateFactory;

import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.util.HashMap;

import javax.swing.JMenuItem;
import javax.swing.JOptionPane;
import javax.swing.JPopupMenu;

import de.uni_muenster.cs.sev.lethal.parser.tree.ParseException;
import de.uni_muenster.cs.sev.lethal.parser.tree.TokenMgrError;
import de.uni_muenster.cs.sev.lethal.parser.tree.TreeParser;
import de.uni_muenster.cs.sev.lethal.states.State;
import de.uni_muenster.cs.sev.lethal.symbol.common.RankedSymbol;
import de.uni_muenster.cs.sev.lethal.symbol.common.Symbol;
import de.uni_muenster.cs.sev.lethal.tree.common.Tree;
import de.uni_muenster.cs.sev.lethal.treeautomata.common.FTAOps;
import de.uni_muenster.cs.sev.lethal.treeautomata.easy.EasyFTA;
import de.uni_muenster.cs.sev.lethal.treeautomata.easy.EasyFTACreator;
import de.uni_muenster.cs.sev.lethal.treeautomata.easy.EasyFTAOps;
import de.uni_muenster.cs.sev.lethal.utils.Converter;
import de.uni_muenster.cs.sev.lethal.utils.IdentityConverter;

/**
 * GUI Editor for ranked trees.
 * @author Sezar,Philipp
 */
public class TreeEditor extends AbstractTreeEditor{

	private TreeItem item;

	/**
	 * Create a new editor for a tree item.
	 * @param item item to edit
	 */
	public TreeEditor(final TreeItem item){
		super(item);
		this.item = item;

		this.quickApplyButton.addActionListener(new ActionListener(){
			public void actionPerformed(ActionEvent e) {
				final Tree<RankedSymbol> tree = tryParseCurrentTree(true);
				if (tree == null) return; 

				JPopupMenu menu = new JPopupMenu();

				JMenuItem singletonAutomatonItem = new JMenuItem("Create singleton automaton");
				menu.add(singletonAutomatonItem);
				singletonAutomatonItem.addActionListener(new ActionListener(){
					@Override
					public void actionPerformed(ActionEvent e) {
						EasyFTA fta = EasyFTAOps.computeSingletonFTA(tree);
						final HashMap<State,State> stateMap = new HashMap<State,State>(); 
						fta = FTAOps.ftaConverter(fta, new Converter<State,State>(){
							@Override
							public State convert(State a) {
								State q = stateMap.get(a);
								if (q == null) {q = StateFactory.getStateFactory().makeState(); stateMap.put(a,q);}
								return q;
							}
						}
						, new IdentityConverter<RankedSymbol>(), new EasyFTACreator());
						new TreeAutomatonDisplayWindow(
								fta,
								item.getProject(),
								item.getName()+ "_singleton",
								null,
								"Singleton FTA for tree" + item.getName());
					}
				});
				
				menu.show(TreeEditor.this.quickApplyButton, 0, TreeEditor.this.quickApplyButton.getHeight());
			}
		});
	}

	/**
	 * @see de.uni_muenster.cs.sev.lethal.gui.Editor#getName()
	 */
	@Override
	public String getName() {
		return "Tree Editor";
	}


	/**
	 * @see de.uni_muenster.cs.sev.lethal.gui.AbstractTreeEditor#drawTerm(boolean)
	 */
	@Override
	protected void drawTerm(boolean showError) {
		Tree<RankedSymbol> hedge = tryParseCurrentTree(false);
		if (hedge != null){
			this.treeViewer.setTree(hedge);
			this.treeViewer.repaint();
			setValid(true);
		} else {
			setValid(false);
		}
	}
	
	/**
	 * @see de.uni_muenster.cs.sev.lethal.gui.Editor#saveToItem()
	 */
	@Override
	protected boolean saveToItem(){
		Tree<RankedSymbol> tree = tryParseCurrentTree(true);
		if (tree != null){
			this.item.setTree(tree);
			setDirty(false);
			return true;
		}
		return false;
	}

	/**
	 * Tries to parse the current text in the editor line as a hedge and returns it.<br>
	 * If the parsing fails an error message is shown (unless showError is false) and null is returned.
	 * @param showError if true an error message is shown if the parsing fails, otherwise it fails silently
	 * @return the resulting hedge or null
	 */
	protected Tree<RankedSymbol> tryParseCurrentTree(boolean showError){
		try {
			if (this.insertField.getText() != null && this.insertField.getText().length() != 0){
				return TreeParser.parseString(this.insertField.getText());
			} else {
				return null;
			}
		} catch (ParseException e) {
			if (showError) JOptionPane.showMessageDialog(this,"Tree Parser Exception:\n" + e.toString(), item.getName(), JOptionPane.ERROR_MESSAGE);
			return null;
		} catch (TokenMgrError e){
			if (showError) JOptionPane.showMessageDialog(this,"Tree Parser Exception:\n" + e.toString(), item.getName(), JOptionPane.ERROR_MESSAGE);
			return null;
		}
	}

	/**
	 * @see de.uni_muenster.cs.sev.lethal.gui.Editor#getItem()
	 */
	@Override
	protected TreeItem getItem() {
		return this.item;
	}

	@Override
	protected Class<? extends Symbol> getTreeSymbolClass() {
		return RankedSymbol.class;
	}

}
