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
import java.awt.Color;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;

import javax.swing.*;
import javax.swing.event.*;

import de.uni_muenster.cs.sev.lethal.symbol.common.Symbol;
import de.uni_muenster.cs.sev.lethal.tree.common.Tree;

import de.uni_muenster.cs.sev.lethal.factories.NamedSymbolTreeFactory;
import de.uni_muenster.cs.sev.lethal.factories.TreeFactory;

/**
 * Abstract superclass for ranked tree and hedge editor.
 * @author Philipp, Sezar
 *
 */
public abstract class AbstractTreeEditor extends Editor {
	protected JTextField insertField;
	protected JButton quickApplyButton = new JButton("Quick Operations", Resources.loadIcon("fta-quickops.png"));
	protected JLabel invalidLabel = new JLabel("Invalid");
	protected JButton randomButton = new JButton("Random", Resources.loadIcon("random.png"));
	protected TreeViewer treeViewer;

	protected Project project;

	protected boolean valid = false;

	/**
	 * Constructor for AbstractTreeEditor, initializes common elements of tree editors.
	 * @param item tree item to edit.
	 */
	protected AbstractTreeEditor(AbstractTreeItem item){
		super(item);
		this.project = item.getProject();

		this.insertField = new JTextField();
		this.toolbar.add(this.insertField);

		this.toolbar.add(this.invalidLabel);
		this.invalidLabel.setForeground(Color.RED);

		this.toolbar.add(this.randomButton);
		
		this.toolbar.add(quickApplyButton);
		
		this.treeViewer = new TreeViewer(item.getTree());
		this.add(this.treeViewer, BorderLayout.CENTER);
		
		// load tree if it has been saved
		if (item.getTree()!=null) {
			this.insertField.setText(item.getTree().toString());
			this.setValid(true);
		}
		
		insertField.getDocument().addDocumentListener(new DocumentListener() {
			@Override
			public void changedUpdate(DocumentEvent e) {_drawTerm(false); setDirty(true);}
			@Override
			public void insertUpdate(DocumentEvent e) {_drawTerm(false); setDirty(true);}
			@Override
			public void removeUpdate(DocumentEvent e) {_drawTerm(false); setDirty(true);}
		});
		
		drawTerm(false);
		
		this.randomButton.addActionListener(new ActionListener(){
			@Override
			public void actionPerformed(ActionEvent e) {
				NamedSymbolTreeFactory<? extends Symbol> tf = TreeFactory.getTreeFactory(getTreeSymbolClass());
				Tree<? extends Symbol> tree = tf.generateRandomTree(5, 5, 15);
				insertField.setText(tree.toString());
			}
		});
	}
	
	/**
	 * Sets the valid state of the editor. 
	 * @param valid true if the currently entered string is a valid tree, false if not.
	 */
	protected void setValid(boolean valid){
		this.valid = valid;
		this.invalidLabel.setVisible(!valid);
		this.applyButton.setEnabled(dirty && this.valid);
	}

	private void _drawTerm(boolean showError){
		if ("__breakout__".equals(insertField.getText())) {
			this.tb = new TreeBreak(TreeFactory.getTreeFactory(getTreeSymbolClass()));
			this.add(this.tb,  BorderLayout.CENTER);
			this.treeViewer.setVisible(false);
			this.validate();
			return;
		} else {
			if (tb != null) this.tb.setVisible(false);
			tb = null;
			this.treeViewer.setVisible(true);
			this.add(this.treeViewer);
			this.validate();
		}
		drawTerm(showError);
	}
	
	private TreeViewer tb;
	
	protected abstract void drawTerm(boolean showError);
	
	protected abstract Class<? extends Symbol> getTreeSymbolClass();
}
