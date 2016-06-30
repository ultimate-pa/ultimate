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
import java.awt.Point;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.awt.event.InputEvent;
import java.awt.event.KeyEvent;

import javax.swing.AbstractAction;
import javax.swing.InputMap;
import javax.swing.JButton;
import javax.swing.JComponent;
import javax.swing.JMenu;
import javax.swing.JMenuItem;
import javax.swing.JPanel;
import javax.swing.JPopupMenu;
import javax.swing.JToolBar;
import javax.swing.KeyStroke;
import javax.swing.MenuElement;
import javax.swing.SwingUtilities;
import javax.swing.event.ChangeEvent;
import javax.swing.event.ChangeListener;
import javax.swing.event.PopupMenuEvent;
import javax.swing.event.PopupMenuListener;

import de.uni_muenster.cs.sev.lethal.symbol.common.Symbol;
import de.uni_muenster.cs.sev.lethal.tree.common.Tree;

/**
 * Base class for GUI Editor widgets.
 * @author Philipp
 */
@SuppressWarnings("serial")
public abstract class Editor extends JPanel {

	protected JToolBar toolbar = new JToolBar();

	protected JButton applyButton = new JButton("Apply", Resources.loadIcon("apply.png"));

	protected TreePreviewWindow treePreviewWindow;
	
	/** True if the editor has unsaved changes. */
	protected boolean dirty = false;
	
	protected Editor(Item item){
		this.setLayout(new BorderLayout());
		this.add(toolbar, BorderLayout.NORTH);

		this.toolbar.add(this.applyButton);
		this.applyButton.setEnabled(false);
		this.toolbar.addSeparator();

		applyButton.addActionListener(new ActionListener(){
			public void actionPerformed(ActionEvent e) {
				saveToItem();
			}
		});

		this.applyButton.setMnemonic(KeyEvent.VK_A);
		InputMap inputMap = this.applyButton.getInputMap(JComponent.WHEN_IN_FOCUSED_WINDOW);
		inputMap.put(KeyStroke.getKeyStroke(KeyEvent.VK_A, InputEvent.CTRL_DOWN_MASK), "APPLY");
		inputMap.put(KeyStroke.getKeyStroke(KeyEvent.VK_S, InputEvent.CTRL_DOWN_MASK), "APPLY");
		this.applyButton.getActionMap().put("APPLY", new AbstractAction(){
			public void actionPerformed(ActionEvent e) {
				saveToItem();
			}
		});
		
		item.getProject().fireItemEditorChanged(item, this);
	}

	/**
	 * Returns the item edited by this editor.
	 * @return the item edited by this editor
	 */
	protected abstract Item getItem();
	
	/**
	 * User visible name for this Editor.
	 */
	@Override
	public abstract String getName();

	/**
	 * Set unsaved changes state of the editor. 
	 * @param dirty true if there are unsaved changes, false if there are not.
	 */
	protected void setDirty(boolean dirty){
		if (this.dirty != dirty){
			this.dirty = dirty;
			this.applyButton.setEnabled(dirty);
			this.getItem().getProject().fireItemEdited(this.getItem());
		}
	}
	
	/**
	 * Returns true if the editor has unsaved changes.
	 * @return true if the editor has unsaved changes
	 */
	public boolean isDirty(){
		return dirty;
	}

	/**
	 * Saves the state of the editor to its item.
	 * @return true if the save was successful, false if not.
	 */
	protected abstract boolean saveToItem();
	
	/**
	 * Called by the main window if the editor is closed.
	 * can be implemented by subclasses, by default it does nothing. 
	 */
	public void close() {
		setDirty(false);
		getItem().getProject().fireItemEditorChanged(getItem(), null);
	}

	
	protected <S extends Item> JMenu generateApplyMenu(Project project, Class<S> itemClass, final ApplyEvent<S> clickHandler){
		final JMenu applyMenu = new JMenu("Apply on "+ Item.getItemClassName(itemClass));
		
		for (final Item item : project.getItems(itemClass)){
			final JMenuItem menuItem = new JMenuItem(item.getName());
			
			if (AbstractTreeItem.class.isAssignableFrom(itemClass)){ //preview is only supported for for tree Items
				final Tree<? extends Symbol> tree = ((AbstractTreeItem)item).getTree();
				
				menuItem.getModel().addChangeListener(new ChangeListener(){
					@Override
					public void stateChanged(ChangeEvent e) {
						if (treePreviewWindow != null) {
							treePreviewWindow.setTree(tree);
							
							Point p = new Point(menuItem.getWidth(),0);
							SwingUtilities.convertPointToScreen(p, menuItem);
							treePreviewWindow.setLocation(p);
						}
					}
				});
			}
			
			applyMenu.add(menuItem);
			menuItem.addActionListener(new ActionListener(){
				@SuppressWarnings("unchecked")
				@Override
				public void actionPerformed(ActionEvent e){
					if (treePreviewWindow != null) treePreviewWindow.setTree(null);
					clickHandler.apply((S)item);
				}
			});
		}
		return applyMenu;
	}
	
	protected void initTreePreview(JPopupMenu menu){
		menu.addPopupMenuListener(new PopupMenuListener(){
			@Override public void popupMenuCanceled(PopupMenuEvent e) {}
			@Override public void popupMenuWillBecomeInvisible(PopupMenuEvent e) {
				treePreviewWindow.setTree(null);
				treePreviewWindow.dispose();
				treePreviewWindow = null;
			}
			@Override public void popupMenuWillBecomeVisible(PopupMenuEvent e) {
				treePreviewWindow = new TreePreviewWindow();
			}
		});
		//Hide the treePreviewWindow if anything in the main menu gets selected
		for (MenuElement element : menu.getSubElements()){
			if (element instanceof JMenuItem){
				((JMenuItem)element).getModel().addChangeListener(new ChangeListener(){
					@Override
					public void stateChanged(ChangeEvent e) {
						if (treePreviewWindow != null) treePreviewWindow.setTree(null);
					}
				});
			}
		}
	}
	
	protected interface ApplyEvent<S extends Item>{
		public void apply(S item);
	}
	
}
