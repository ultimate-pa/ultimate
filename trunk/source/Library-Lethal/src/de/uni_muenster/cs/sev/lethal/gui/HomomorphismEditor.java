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

import de.uni_muenster.cs.sev.lethal.hom.EasyHom;

import java.awt.BorderLayout;
import java.awt.event.*;

import javax.swing.*;
import javax.swing.event.*;

import de.uni_muenster.cs.sev.lethal.parser.fta.TokenMgrError;
import de.uni_muenster.cs.sev.lethal.parser.homomorphism.HomomorphismParser;
import de.uni_muenster.cs.sev.lethal.symbol.common.RankedSymbol;
import de.uni_muenster.cs.sev.lethal.tree.common.Tree;
import de.uni_muenster.cs.sev.lethal.treeautomata.easy.EasyFTA;

/**
 * GUI Editor for Tree Homomorphisms.
 * @author Philipp
 *
 */
public class HomomorphismEditor extends Editor {
	/** Last hope for despaired users */
	private JButton helpButton = new JButton("Help",Resources.loadIcon("help.png"));

	protected JButton quickApplyButton = new JButton("Quick Operations", Resources.loadIcon("fta-quickops.png"));
	
	/** Text field in which the user enters new rules. */
	private JTextArea editorTextField = new JTextArea();

	/** @see HomomorphismItem  */
	private HomomorphismItem item;

	/**
	 * Constructs editor window from given homomorphism.
	 * @param item item to be edited
	 */
	public HomomorphismEditor(final HomomorphismItem item){
		super(item);
		this.item = item;
		this.toolbar.add(this.quickApplyButton);
		this.toolbar.addSeparator();
		this.toolbar.add(this.helpButton);

		this.add(new JScrollPane(editorTextField), BorderLayout.CENTER);

		if (item.getHomomorphism() != null){
			this.editorTextField.setText(item.getHomomorphismString());
		}

		this.editorTextField.getDocument().addDocumentListener(new DocumentListener(){
			public void changedUpdate(DocumentEvent e){setDirty(true);}
			public void insertUpdate(DocumentEvent e) {setDirty(true);}
			public void removeUpdate(DocumentEvent e) {setDirty(true);}

		});

		this.quickApplyButton.addActionListener(new ActionListener(){
			public void actionPerformed(ActionEvent e) {
				final EasyHom hom = tryParseCurrentHomomorphism();
				if (hom == null) return;
				
				JPopupMenu menu = new JPopupMenu();
				
				ApplyEvent<TreeItem> treeApplyAction = new ApplyEvent<TreeItem>(){
					@Override
					public void apply(TreeItem treeItem){
						try{
							Tree<RankedSymbol> tree = treeItem.getTree();
							Tree<RankedSymbol> resultTree = hom.apply(tree);
							if (resultTree == null) {JOptionPane.showMessageDialog(HomomorphismEditor.this, "Tree not accepted, no output to display :'(", "Apply Tree Homomorphism", JOptionPane.INFORMATION_MESSAGE); return;}
							new TreeDisplayWindow(
									resultTree,
									item.getProject(),
									treeItem.getName() + "_" + item.getName(),
									null,
									null, 
									"Transformation result: " + HomomorphismEditor.this.item.getName() + " on " + treeItem.getName()
							);
						} catch (Exception ex) {
							JOptionPane.showMessageDialog(HomomorphismEditor.this, "Failed to apply this homomorphism on '" + treeItem.getName() + "':\n" + ex.getMessage() , "Quick Apply", JOptionPane.ERROR_MESSAGE);
						}
					}
				};
				menu.add(generateApplyMenu(item.getProject(), TreeItem.class, treeApplyAction));
				ApplyEvent<FTAItem> ftaApplyAction = new ApplyEvent<FTAItem>(){
					@Override
					public void apply(FTAItem ftaItem){
						try{
							EasyFTA fta = ftaItem.getAutomaton();
							EasyFTA resultFTA = hom.applyOnAutomaton(fta);
							new TreeAutomatonDisplayWindow(
									resultFTA,
									item.getProject(),
									ftaItem.getName() + "_" + item.getName(),
									null,
									"Transformation result: " + HomomorphismEditor.this.item.getName() + " on " + ftaItem.getName()
							);
						} catch (Exception ex) {
							ex.printStackTrace();
							JOptionPane.showMessageDialog(HomomorphismEditor.this, "Failed to apply this homomorphism on '" + ftaItem.getName() + "':\n" + ex.getMessage() , "Quick Apply", JOptionPane.ERROR_MESSAGE);
						}
					}
				};
				menu.add(generateApplyMenu(item.getProject(), FTAItem.class, ftaApplyAction));
				
				initTreePreview(menu);
				menu.show(quickApplyButton, 0, quickApplyButton.getHeight());
			}
		});
		
		
		
		this.helpButton.addActionListener(new ActionListener(){
			public void actionPerformed(ActionEvent e) {
				JOptionPane.showMessageDialog(HomomorphismEditor.this, "Enter tree homomorphism rules using format:\nfunction(var1,var2,...,varN) -> tree(subtree(...,var1,...),...,subtree(...,varN)) \n\nOne Rule in each line.", "Help", JOptionPane.INFORMATION_MESSAGE);
			}
		});
	}

	@Override
	protected boolean saveToItem(){
		EasyHom homomorphism = tryParseCurrentHomomorphism();
		if (homomorphism == null) return false;
		
		item.setHomomorphism(homomorphism, this.editorTextField.getText());

		setDirty(false);
		return true;
	}

	private EasyHom tryParseCurrentHomomorphism(){
		String rulesString = this.editorTextField.getText();
		try {
			return HomomorphismParser.parseString(rulesString);
		} catch (TokenMgrError ex) {
			ex.printStackTrace();
			JOptionPane.showMessageDialog(this, "Homomorphism Parser Exception:\n" + ex.getMessage());
			return null;
		} catch (Exception ex) {
			ex.printStackTrace();
			JOptionPane.showMessageDialog(this, "Homomorphism Parser Exception:\n" + ex.getMessage());
			return null;
		}
	}
	
	@Override
	public HomomorphismItem getItem(){
		return this.item;
	}
	
	@Override
	public String getName() {
		return "Homomorphism Editor";
	}

}
