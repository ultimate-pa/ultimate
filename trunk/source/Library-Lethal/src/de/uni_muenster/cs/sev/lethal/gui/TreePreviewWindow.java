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

import java.awt.Dimension;
import java.awt.Graphics;

import javax.swing.JScrollPane;
import javax.swing.JWindow;
import javax.swing.ScrollPaneConstants;

import de.uni_muenster.cs.sev.lethal.symbol.common.Symbol;
import de.uni_muenster.cs.sev.lethal.tree.common.Tree;

/**
 * Frame-less preview window for trees.<br>
 * Shows a given tree in a max of 200x200 pixels auto scaling the zoom factor to fit the size.
 * @author Philipp
 *
 */
public class TreePreviewWindow extends JWindow{
	
	private static final int MAX_WIDTH  = 200;
	private static final int MAX_HEIGHT = 200;
	
	private TreeViewer tv;
	private Tree<? extends Symbol> tree;
	private int repaintCount;
	
	/**
	 * Create a new TreePreviewWindow.
	 */
	public TreePreviewWindow(){
		tv = new TreeViewer(null);
		tv.setToolbarVisible(false);
		tv.setScrollEnabled(false);
		this.setSize(MAX_WIDTH, MAX_HEIGHT);
		JScrollPane sp = new JScrollPane(tv);
		sp.setHorizontalScrollBarPolicy(ScrollPaneConstants.HORIZONTAL_SCROLLBAR_NEVER);
		sp.setVerticalScrollBarPolicy(ScrollPaneConstants.VERTICAL_SCROLLBAR_NEVER);
		this.add(sp);
	}
	
	/**
	 * Set the tree to display. <br>
	 * Setting to null will hide the window.
	 * @param tree tree to display
	 */
	public void setTree(Tree<? extends Symbol> tree){
		if (this.tree == tree) return;
		this.tree = tree;
		
		if (tree != null){
			tv.setSize(MAX_WIDTH, MAX_HEIGHT);
			tv.setPreferredSize(new Dimension(MAX_WIDTH, MAX_HEIGHT));
			tv.setTree(tree);
			repaintCount = 0;
			this.setVisible(true);
			this.repaint();
		} else {
			this.setVisible(false);
		}
	}
	
	@Override
	public void paint(Graphics g) {
		super.paint(g);
		if (repaintCount == 0){
			tv.autoZoom(0.2F, 1F);
			this.repaint();
			repaintCount = 1;
		} else if (repaintCount == 1){
			int w = (int) tv.getPreferredSize().getWidth() +4; //FIXME: figure out the Borders somehow
			int h = (int) tv.getPreferredSize().getHeight() +4;
			if (w > MAX_WIDTH) w = MAX_WIDTH;
			if (h > MAX_HEIGHT) h = MAX_HEIGHT;
			this.setSize(w,h);
			tv.setSize(w,h);
			repaintCount = 2;
		}
	}
}
