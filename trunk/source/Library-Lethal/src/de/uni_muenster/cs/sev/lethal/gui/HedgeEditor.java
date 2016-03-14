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


import java.awt.event.*;
import javax.swing.*;

import de.uni_muenster.cs.sev.lethal.parser.tree.*;

import de.uni_muenster.cs.sev.lethal.utils.Converter;

import de.uni_muenster.cs.sev.lethal.symbol.common.RankedSymbol;
import de.uni_muenster.cs.sev.lethal.symbol.common.Symbol;
import de.uni_muenster.cs.sev.lethal.symbol.common.UnrankedSymbol;
import de.uni_muenster.cs.sev.lethal.symbol.special.HedgeSymbol;
import de.uni_muenster.cs.sev.lethal.symbol.standard.StdNamedRankedSymbol;

import de.uni_muenster.cs.sev.lethal.tree.common.Tree;
import de.uni_muenster.cs.sev.lethal.tree.common.TreeOps;
import de.uni_muenster.cs.sev.lethal.tree.standard.StdTreeCreator;

import de.uni_muenster.cs.sev.lethal.hedgeautomaton.internal.TreeCache;

/**
 * GUI Editor for hedges.
 * @author Philipp
 *
 */
public class HedgeEditor extends AbstractTreeEditor {

	/**
	 * Item edited by this editor.
	 */
	private HedgeItem item;

	/**
	 * Creates a new hedge editor.
	 * @param item item to edit
	 */
	public HedgeEditor(HedgeItem item){
		super(item);
		this.item = item;

		this.quickApplyButton.addActionListener(new ActionListener(){
			public void actionPerformed(ActionEvent e) {
				final Tree<UnrankedSymbol> hedge = tryParseCurrentTree(true);
				if (hedge == null) return; 

				JPopupMenu menu = new JPopupMenu();

				JMenuItem convertApplyMenu = new JMenuItem("Convert to ranked Tree");
				menu.add(convertApplyMenu);
				convertApplyMenu.addActionListener(new ActionListener(){
					@Override
					public void actionPerformed(ActionEvent e) {
						new TreeDisplayWindow(
								TreeOps.convert(
										TreeCache.getTree(hedge),
										new Converter<HedgeSymbol<UnrankedSymbol>, RankedSymbol>(){
											@Override
											public RankedSymbol convert(HedgeSymbol<UnrankedSymbol> a) {
												return new StdNamedRankedSymbol<String>(a.toString(), a.getArity());
											}
										},
										new StdTreeCreator<RankedSymbol>()
								),
								HedgeEditor.this.item.getProject(),
								HedgeEditor.this.item.getName() + "_converted",
								null,
								null,
								"Convert Hedge '" + HedgeEditor.this.item.getName() + "' to Tree");
					}
				});

				menu.show(quickApplyButton, 0, quickApplyButton.getHeight());
			}
		});

	}

	@Override
	public String getName() {
		return "Hedge Editor";
	}


	@Override
	protected void drawTerm(boolean showError) {
		Tree<UnrankedSymbol> hedge = tryParseCurrentTree(false);
		if (hedge != null){
			this.treeViewer.setTree(hedge);
			this.treeViewer.repaint();
			setValid(true);
		} else {
			setValid(false);
		}
	}

	@Override
	protected boolean saveToItem(){
		Tree<UnrankedSymbol> hedge = tryParseCurrentTree(true);
		if (hedge != null){
			this.item.setHedge(hedge);
			setDirty(false);
			return true;
		} else {
			return false;
		}
	}

	/**
	 * Tries to parse the current text in the editor line as a hedge and returns it.<br>
	 * If the parsing fails an error message is shown (unless showError is false) and null is returned.
	 * @param showError if true an error message is shown if the parsing fails, otherwise it fails silently
	 * @return the resulting hedge or null
	 */
	protected Tree<UnrankedSymbol> tryParseCurrentTree(boolean showError){
		try {
			if (this.insertField.getText() != null && this.insertField.getText().length() != 0){
				return TreeParser.parseStringAsHedge(this.insertField.getText());
			} else {
				return null;
			}
		} catch (ParseException e) {
			if (showError) JOptionPane.showMessageDialog(this,"Hedge Parser Exception:\n" + e.toString(), item.getName(), JOptionPane.ERROR_MESSAGE);
			return null;
		} catch (TokenMgrError e){
			if (showError) JOptionPane.showMessageDialog(this,"Hedge Parser Exception:\n" + e.toString(), item.getName(), JOptionPane.ERROR_MESSAGE);
			return null;
		}
	}

	@Override
	protected HedgeItem getItem() {
		return this.item;
	}
	
	@Override
	protected Class<? extends Symbol> getTreeSymbolClass() {
		return UnrankedSymbol.class;
	}
}
