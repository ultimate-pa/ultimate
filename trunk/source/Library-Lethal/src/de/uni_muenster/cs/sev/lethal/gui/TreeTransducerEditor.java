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
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.util.Set;

import javax.swing.*;
import javax.swing.event.*;

import de.uni_muenster.cs.sev.lethal.parser.fta.TokenMgrError;
import de.uni_muenster.cs.sev.lethal.parser.treetransducer.TreeTransducerParser;
import de.uni_muenster.cs.sev.lethal.symbol.common.RankedSymbol;
import de.uni_muenster.cs.sev.lethal.tree.common.Tree;
import de.uni_muenster.cs.sev.lethal.treetransducer.EasyTT;


/**
 * GUI editor for tree transducers.
 * @author Philipp
 *
 */
public class TreeTransducerEditor extends Editor {
	/** Last hope for despaired users. */
	private JButton helpButton = new JButton("Help",Resources.loadIcon("help.png"));

	/** Text field in which the user enters new rules. */
	private JTextArea editorTextField = new JTextArea();

	protected JButton quickApplyButton = new JButton("Quick Operations", Resources.loadIcon("fta-quickops.png"));
	
	/** @see TreeTransducerItem  */
	private TreeTransducerItem item;

	/**
	 * Constructs editor window from a given tree transducer item.
	 * @param item item to be edited
	 */
	public TreeTransducerEditor(final TreeTransducerItem item){
		super(item);
		this.item = item;

		this.toolbar.add(quickApplyButton);
		this.toolbar.add(new JToolBar.Separator());
		this.toolbar.add(helpButton);

		this.add(new JScrollPane(editorTextField), BorderLayout.CENTER);

		if (item.getTreeTransducerString() != null){
			this.editorTextField.setText(item.getTreeTransducerString());
		}

		this.editorTextField.getDocument().addDocumentListener(new DocumentListener(){
			public void changedUpdate(DocumentEvent e){setDirty(true);}
			public void insertUpdate(DocumentEvent e) {setDirty(true);}
			public void removeUpdate(DocumentEvent e) {setDirty(true);}
		});
		
		
		this.quickApplyButton.addActionListener(new ActionListener(){
			public void actionPerformed(ActionEvent e) {
				final EasyTT trans = tryParseCurrentTransducer();
				if (trans == null) return;
				
				JPopupMenu menu = new JPopupMenu();
				
				ApplyEvent<TreeItem> applyAction = new ApplyEvent<TreeItem>(){
					@Override
					public void apply(TreeItem treeItem){
						try{
							Tree<RankedSymbol> tree = treeItem.getTree();
							Set<Tree<RankedSymbol>> resultTrees = trans.doARun(tree);
							if (resultTrees.isEmpty()) {JOptionPane.showMessageDialog(TreeTransducerEditor.this, "Tree not accepted, no output to display :'(", "Apply Tree Transducer", JOptionPane.INFORMATION_MESSAGE); return;}
							if (JOptionPane.showConfirmDialog(TreeTransducerEditor.this, "Tree accepted and " + resultTrees.size() + " tree" + (resultTrees.size() != 1 ? "s" : "") + " generated, do you want to display " + (resultTrees.size() != 1 ? "them" : "it") + "?", "Apply Tree Transducer", JOptionPane.YES_NO_OPTION) == JOptionPane.NO_OPTION) return;
							for (Tree<RankedSymbol> resultTree : resultTrees){
								new TreeDisplayWindow(
										resultTree,
										item.getProject(),
										treeItem.getName() + "_" + item.getName(),
										null,
										null, 
										"Transformation result: " + TreeTransducerEditor.this.item.getName() + " on " + treeItem.getName()
							);
							}
						} catch (Exception ex) {
							JOptionPane.showMessageDialog(TreeTransducerEditor.this, "Failed to apply this automaton on '" + treeItem.getName() + "':\n" + ex.getMessage() , "Quick Apply", JOptionPane.ERROR_MESSAGE);
						}
					}
				};
				menu.add(generateApplyMenu(item.getProject(), TreeItem.class, applyAction));
				menu.addSeparator();

				JMenuItem extractFTAMenu = new JMenuItem("Extract FTA");
				menu.add(extractFTAMenu);
				extractFTAMenu.addActionListener(new ActionListener(){
					@Override
					public void actionPerformed(ActionEvent e) {
						new TreeAutomatonDisplayWindow(
								trans.getFTAPart(),
								TreeTransducerEditor.this.item.getProject(),
								TreeTransducerEditor.this.item.getName() + "_fta",
								null,
								"Extract FTA from " + TreeTransducerEditor.this.item.getName());
					}
				});
				initTreePreview(menu);
				menu.show(quickApplyButton, 0, quickApplyButton.getHeight());
			}
		});
		
		this.helpButton.addActionListener(new ActionListener(){
			public void actionPerformed(ActionEvent e) {
				JOptionPane.showMessageDialog(TreeTransducerEditor.this, "Enter tree transducer rules using format:\nfunction(state1[:var1],state2[:var2],...,stateN[:varN]) -> deststate, tree(subtree(...,var1,...),...,subtree(...,varN))\nOr\nstate:var => deststate, tree(...,subtree(...,var,...)) \n\nOne Rule in each line.", "Help", JOptionPane.INFORMATION_MESSAGE);
			}
		});
	}

	@Override
	protected boolean saveToItem(){
		String transducerDescribtion = TreeTransducerEditor.this.editorTextField.getText();
		EasyTT transducer = tryParseCurrentTransducer();
		if (transducer == null) return false;
		
		item.setTreeTransducer(transducer, transducerDescribtion);

		setDirty(false);
		return true;
	}

	/**
	 * Tries to parse the current text in the editor as an tree transducer and returns it. <br>
	 * If the parsing fails an error message is shown and null is returned.
	 * @return the resulting tree transducer
	 */
	private EasyTT tryParseCurrentTransducer(){
		String rulesString = this.editorTextField.getText();
		try {
			return TreeTransducerParser.parseString(rulesString);
		} catch (TokenMgrError ex) {
			ex.printStackTrace();
			JOptionPane.showMessageDialog(TreeTransducerEditor.this, "Tree Transducer Parser Exception:\n" + ex.getMessage());
			return null;
		} catch (Exception ex) {
			ex.printStackTrace();
			JOptionPane.showMessageDialog(TreeTransducerEditor.this, "Tree Transducer Parser Exception:\n" + ex.getMessage());
			return null;
		}
	}
	
	@Override
	public TreeTransducerItem getItem(){
		return this.item;
	}

	@Override
	public String getName() {
		return "Tree Transducer Editor";
	}


}
