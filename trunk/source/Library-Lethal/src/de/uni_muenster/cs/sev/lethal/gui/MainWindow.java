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

import de.uni_muenster.cs.sev.lethal.gui.Project.InvalidItemNameException;

import java.awt.*;
import java.awt.event.*;

import javax.swing.*;
import javax.swing.event.*;
import javax.swing.filechooser.*;
import javax.swing.plaf.basic.BasicArrowButton;
import javax.swing.tree.*;

import java.io.File;

import java.util.*;
import java.util.List;

import java.lang.reflect.InvocationTargetException;

import de.uni_muenster.cs.sev.lethal.parser.xml.XMLTreeParser;
import de.uni_muenster.cs.sev.lethal.symbol.common.*;
import de.uni_muenster.cs.sev.lethal.tree.common.Tree;

/**
 * Application main window.
 * @author Philipp, Sezar
 */
@SuppressWarnings("serial")
public class MainWindow extends JFrame {
	
	/** MainWindow toolbar, contains all user action buttons. */
	private JToolBar toolbar = new JToolBar();

	private JButton newProjectButton    = new JButton("New",         Resources.loadIcon("project-new.png")    );
	private JButton openProjectButton   = new JButton("Open",        Resources.loadIcon("project-open.png")   );
	private JButton openRecentMenuButton= new BasicArrowButton(SwingConstants.SOUTH);
	private JButton saveProjectButton   = new JButton("Save all",    Resources.loadIcon("project-save.png")   );
	private JButton saveProjectAsButton = new JButton("Save as...",  Resources.loadIcon("project-save-as.png"));
	private JButton importButton        = new JButton("Import",      Resources.loadIcon("import.png")         );
	private JButton addItemButton       = new JButton("Add item",    Resources.loadIcon("item-add.png")       );
	private JButton removeItemButton    = new JButton("Remove selected", Resources.loadIcon("item-remove.png"));
	
	private ScriptConsole scriptConsole = new ScriptConsole(this);

	private JSplitPane splitter = new JSplitPane(JSplitPane.HORIZONTAL_SPLIT);

	/** List of all user created items for the current project. */
	private JTree treeview = new JTree();

	/** Container for the actual item editors. */
	private Container editorContainer = new Container();

	/** Label showing the name of the current item editor. */
	private JLabel editorNameLabel = new JLabel();
	
	/** Button to close the currently visible editor. */
	private JButton editorCloseButton = new JButton(Resources.loadIcon("editor-close.png"));
	
	/** Map of currently open editors for items. */
	private HashMap<Item,Editor> openEditors = new HashMap<Item,Editor>();
	
	/** Editor object for the item selected by the user. */
	private Editor visibleEditor;

	/** Currently loaded project. */
	private Project currentProject;
	
	/** Filename of the currently loaded project, null if unsaved. */
	private File projectFile;
	
	/**
	 * Creates the main window.
	 */
	public MainWindow(){
		this.setLayout(new BorderLayout());
		
		this.setDefaultCloseOperation(DO_NOTHING_ON_CLOSE); //need to intercept window close for "do you want to save?" question. So don't close the window automatically
		
		this.setIconImages(Arrays.<Image>asList(Resources.loadImage("mainwindow-small.png"), Resources.loadImage("mainwindow-medium.png"), Resources.loadImage("mainwindow-large.png")));
		
		//Window layout setup
		this.add(this.toolbar, BorderLayout.NORTH);
		this.toolbar.add(this.newProjectButton);
		this.toolbar.add(this.openProjectButton);
		this.toolbar.add(this.saveProjectButton);
		this.toolbar.add(this.saveProjectAsButton);
		this.toolbar.add(new JToolBar.Separator());
		this.toolbar.add(this.importButton);
		this.toolbar.add(new JToolBar.Separator());
		this.toolbar.add(this.addItemButton);
		this.toolbar.add(this.removeItemButton);

		this.removeItemButton.setEnabled(false);

		//Place the recent dropDown button inside the open button
		//Restrict the the max size to what we need, otherwise the button will stretch as much as possible. 
		this.openProjectButton.setMaximumSize(new Dimension(this.openProjectButton.getPreferredSize().width + openRecentMenuButton.getPreferredSize().width, this.openProjectButton.getPreferredSize().height));
		this.openProjectButton.setLayout(new BorderLayout()); //need a layout to place somthing in a control
		this.openProjectButton.setHorizontalAlignment(SwingConstants.LEFT); //Align Button text to the left, not center or it will slide "under" the dropdown button
		this.openProjectButton.setMargin(new Insets(-2,0,-2,-2)); //no margin, dropdown button gets to tiny otherwise. 
		this.openProjectButton.add(this.openRecentMenuButton, BorderLayout.EAST); //dropdown buttons goes to the right.
		//this.openRecentMenuButton.setBorderPainted(false); //would probably look better, but doesn't work :(
		this.openRecentMenuButton.setBorder(null);
		
		this.add(this.splitter, BorderLayout.CENTER);

		this.editorContainer.setLayout(new BorderLayout(3,0));

		this.splitter.setLeftComponent(new JScrollPane(this.treeview));
		this.splitter.setRightComponent(this.editorContainer);

		this.editorContainer.add(this.editorNameLabel, BorderLayout.NORTH);
		this.editorNameLabel.setLayout(new BorderLayout());
		this.editorNameLabel.add(this.editorCloseButton, BorderLayout.EAST);
		this.editorCloseButton.setMaximumSize(new Dimension(16,16));
		this.editorCloseButton.setPreferredSize(new Dimension(16,16));
		this.editorCloseButton.setToolTipText("Close the current editor, discarding all not applied changes.");
		this.editorCloseButton.setBorderPainted(false);
		
		ItemNodeRenderer renderer = new ItemNodeRenderer();
		this.treeview.setCellRenderer(renderer);
		this.treeview.setEditable(true);
		this.treeview.setCellEditor(new ItemNodeEditor(this.treeview, renderer));
		this.treeview.addMouseListener(new MouseAdapter(){
			@SuppressWarnings("unchecked")
			@Override
			public void mousePressed(MouseEvent e) {
				if (e.getButton() == MouseEvent.BUTTON1 && e.getClickCount() == 2){ //double left click
					TreePath path = MainWindow.this.treeview.getPathForLocation(e.getX(), e.getY());
					Object node;
					if (path != null){
						node = path.getLastPathComponent();
					} else {
						node = null;
					}
					if (node instanceof Item){
						if (MainWindow.this.visibleEditor == null || node != MainWindow.this.visibleEditor.getItem()){
							MainWindow.this.editItem((Item)node); //, false);
						}
					}
				}
				
				if (e.getButton() == MouseEvent.BUTTON3){ //right click 
					final TreePath path = treeview.getPathForLocation(e.getX(), e.getY());
					if (path == null) return;
					final Class<? extends Item> itemClass;
					final Item item;
					String itemName;
					if (path.getLastPathComponent() instanceof Item){
						item = ((Item)path.getLastPathComponent());
						itemClass = item.getClass();
						itemName = item.getName();
					} else if (path.getLastPathComponent() instanceof Class<?>){
						itemClass = (Class<? extends Item>)path.getLastPathComponent();
						item = null;
						itemName = null;
					} else {
						return;
					}
					MainWindow.this.treeview.setSelectionPath(path); //HACK: isCellEditable(EventObject event) gets null passed for event if startEditingAtPath is used and thus has no clue which cell we are talking about. We use the cell selection to pass that info.
					
					String className = Item.getItemClassName(itemClass);
					JPopupMenu menu = new JPopupMenu();
					if (item != null){
						JMenuItem renameItem = new JMenuItem("Rename '" + itemName + "'", Resources.loadIcon("item-rename-tiny.png"));
						menu.add(renameItem);
						renameItem.addActionListener(new ActionListener(){
							@Override
							public void actionPerformed(ActionEvent e) { 
								MainWindow.this.treeview.startEditingAtPath(path);
							}
						});
						JMenuItem removeItem = new JMenuItem("Delete '" + itemName + "'", Resources.loadIcon("item-remove-tiny.png"));
						removeItem.addActionListener(new ActionListener(){
							@Override
							public void actionPerformed(ActionEvent e) {
								MainWindow.this.removeItem(item);
							}
						});
						menu.add(removeItem);
						menu.addSeparator();
					}
					
					JMenuItem addItem = new JMenuItem("Add " + className, Resources.loadIcon("item-add-tiny.png"));
					menu.add(addItem);
					addItem.addActionListener(new ActionListener(){
						@Override
						public void actionPerformed(ActionEvent e) {
							MainWindow.this.createNewItem(itemClass);
						}
					});
					menu.show(treeview, e.getX(), e.getY());
				}
			}
		});
		this.treeview.addTreeSelectionListener(new TreeSelectionListener(){
			@Override
			public void valueChanged(TreeSelectionEvent e) {
				if (MainWindow.this.treeview.getSelectionPath() != null){
					Object node = MainWindow.this.treeview.getSelectionPath().getLastPathComponent();
					MainWindow.this.removeItemButton.setEnabled(node instanceof Item);
				} else {
					MainWindow.this.removeItemButton.setEnabled(false);
				}
			}
		});
		
		
		this.newProjectButton.addActionListener(new ActionListener(){
			public void actionPerformed(ActionEvent e) {newProject(null);}
		});
		this.openProjectButton.addActionListener(new ActionListener(){
			public void actionPerformed(ActionEvent e) {loadProject(null);}
		});
		this.saveProjectButton.addActionListener(new ActionListener(){
			public void actionPerformed(ActionEvent e) {saveProject(MainWindow.this.projectFile, false);}
		});
		this.saveProjectButton.setMnemonic(KeyEvent.VK_S);
		InputMap inputMap = this.saveProjectButton.getInputMap(JComponent.WHEN_IN_FOCUSED_WINDOW);
		inputMap.put(KeyStroke.getKeyStroke(KeyEvent.VK_S, InputEvent.CTRL_DOWN_MASK), "SAVE");
		this.saveProjectButton.getActionMap().put("SAVE", new AbstractAction(){
			public void actionPerformed(ActionEvent e) {
				saveProject(MainWindow.this.projectFile, false);
			}
		});

		this.saveProjectAsButton.addActionListener(new ActionListener(){
			public void actionPerformed(ActionEvent e) {saveProject(MainWindow.this.projectFile, true);}
		});

		this.openRecentMenuButton.addActionListener(new ActionListener(){
			@Override
			public void actionPerformed(ActionEvent e) {
				JPopupMenu recentMenu = new JPopupMenu();
				ActionListener openAction = new ActionListener(){
					@Override
					public void actionPerformed(ActionEvent e) {
						loadProject(new File(((JMenuItem)e.getSource()).getText()));
						
					}
					
				};
				boolean anyItems = false;
				for (String file : Settings.getRecentFiles()){
					if (file != null){
						JMenuItem item = new JMenuItem(file);
						item.addActionListener(openAction);
						recentMenu.add(item);
						anyItems = true;
					}
				}
				if (anyItems){
					recentMenu.addSeparator();
					JMenuItem clearItem = new JMenuItem("Clear List");
					clearItem.addActionListener(new ActionListener(){
						@Override
						public void actionPerformed(ActionEvent e) {
							Settings.clearRecentFiles();
						}
					});
					recentMenu.add(clearItem);
				} else {
					JMenuItem dummyItem = new JMenuItem("No Recent Files");
					dummyItem.setEnabled(false);
					recentMenu.add(dummyItem);
				}
				
				recentMenu.show(MainWindow.this.openRecentMenuButton, 0, MainWindow.this.openRecentMenuButton.getHeight());
			}
		});
		
		this.editorCloseButton.addActionListener(new ActionListener(){
			@Override
			public void actionPerformed(ActionEvent e) {
				closeCurrentEditor();
			}
		});
		
		
		//Generate a popup menu for the "Import" button
		final JPopupMenu importMenu = new JPopupMenu();
		JMenuItem menuItem = new JMenuItem("Tree from XML");
		menuItem.addActionListener(new ActionListener(){
			@Override
			public void actionPerformed(ActionEvent e) {
				importTreeFromXML(RankedSymbol.class);
			}
		});
		importMenu.add(menuItem);
		menuItem = new JMenuItem("Hedge from XML");
		menuItem.addActionListener(new ActionListener(){
			@Override
			public void actionPerformed(ActionEvent e) {
				importTreeFromXML(UnrankedSymbol.class);
			}
		});
		importMenu.add(menuItem);


		this.importButton.addActionListener(new ActionListener(){
			@Override
			public void actionPerformed(ActionEvent e) {
				importMenu.show(MainWindow.this.importButton, 0, MainWindow.this.importButton.getHeight());
			}
		});

		//Generate a popup menu for the "Add Item" button from the Item classes.
		final JPopupMenu addItemMenu = new JPopupMenu();
		for (final Class<? extends Item> itemClass : Project.getItemClasses()){
			String name = Item.getItemClassName(itemClass);
			JMenuItem item = new JMenuItem(name);
			item.addActionListener(new ActionListener(){
				public void actionPerformed(ActionEvent e) {
					createNewItem(itemClass);
				}
			});
			addItemMenu.add(item);
		}
		//Open the add item popup menu
		this.addItemButton.addActionListener(new ActionListener(){
			public void actionPerformed(ActionEvent e) {
				addItemMenu.show(MainWindow.this.addItemButton, 0, MainWindow.this.addItemButton.getHeight());
			}
		});

		//Remove the selected item from the tree
		this.removeItemButton.addActionListener(new ActionListener(){
			public void actionPerformed(ActionEvent e) {
				if (MainWindow.this.treeview.getSelectionPath() != null) {
					Object selNode = MainWindow.this.treeview.getSelectionPath().getLastPathComponent();
					if (selNode instanceof Item) removeItem((Item)selNode);
				}
			}
		});

		this.addWindowListener(new WindowAdapter(){	
			@Override
			public void windowClosing(WindowEvent e) {
				Settings.setMainWindowMaximized(MainWindow.this.getExtendedState() == MAXIMIZED_BOTH);
				Settings.setMainWindowRect(MainWindow.this.getBounds());
				Settings.setMainWindowSplitterLocation(MainWindow.this.splitter.getDividerLocation());
				if (askSave()) System.exit(0);
			}
		});
		
		
		this.editorContainer.add(this.scriptConsole, BorderLayout.SOUTH);
		
		Rectangle rect = Settings.getMainWindowRect();
		this.setLocation(rect.getLocation());
		this.setSize(rect.getSize());
		if (Settings.getMainWindowMaximized()) this.setExtendedState(MAXIMIZED_BOTH);
		this.splitter.setDividerLocation(Settings.getMainWindowSplitterLocation());
		
		newProject("New Project");
		this.editorNameLabel.setText("Nothing selected (Add new items or double click existing ones to edit)");
	}

	/**
	 * Creates a new project.
	 * @param name new project name. Passing null opens a prompt dialog for the user.
	 * @return true if the new project has been created, false if not (e.g. user cancelled)
	 */
	private boolean newProject(String name){
		if (!askSave()) return false;

		if (name == null){
			name = JOptionPane.showInputDialog(this, "Enter new project name:", "New Project");
			if (name == null || name.length() == 0) return false;
		}
		
		closeAllEditors();
		this.currentProject = new Project(name);
		this.treeview.setModel(new ItemTreeModel(this.currentProject));
		//Expend all item class nodes
		for (Class<? extends Item> itemClass : Project.getItemClasses()){
			this.treeview.expandPath(new TreePath(new Object[]{this.currentProject, itemClass}));
		}
		this.projectFile = null;

		this.currentProject.addProjectListener(new Project.ProjectEventListener(){
			@Override
			public void onProjectChanged() {updateTitle();}
			@Override
			public void onItemEdited(Item item) {updateTitle();}
			@Override
			public void onItemRenamed(Item item) {updateTitle();}
		});
		updateTitle();

		return true;
	}

	/**
	 * Tries to save the current project.
	 * @param file file to save the project to. If file is null, a file save dialog will be shown to the user.
	 * @param alwaysAskFilename if true the file open dialog will be shown even if file is not null
	 * @return true if the save was successful, false if not
	 */
	private boolean saveProject(File file, boolean alwaysAskFilename){
		if (file == null || alwaysAskFilename){
			JFileChooser dialog = new JFileChooser(file);
			dialog.setFileFilter(new FileNameExtensionFilter("Tree workbench files" ,"twb"));
			if (dialog.showSaveDialog(this) != JFileChooser.APPROVE_OPTION) return false;
			file = dialog.getSelectedFile();
			if (file.exists()){
				int ret = JOptionPane.showConfirmDialog(this, "The file '" +file.getAbsolutePath() + "' already exists, do you want to overwrite it?" , "Overwrite file", JOptionPane.YES_NO_OPTION, JOptionPane.WARNING_MESSAGE);
				if (ret != JOptionPane.YES_OPTION) return false;
			} else {
				if (!file.getName().contains(".")){
					file = new File(file.getAbsolutePath() + ".twb");
				}
			}
		}
		try {
			List<Editor> failed = new ArrayList<Editor>();
			StringBuffer failBuffer = new StringBuffer();
			for (Editor e : this.openEditors.values()){
				if (! e.saveToItem()){
					failed.add(e);
					failBuffer.append("  - ");
					failBuffer.append(e.getItem().getName());
					failBuffer.append("\n");
				}
			}
			if (failed.size() > 0){
				JOptionPane.showMessageDialog(this, "Failed to save the following items:\n" + failBuffer.toString() + "\n Project save aborted.", "Save failure", JOptionPane.ERROR_MESSAGE);
				return false;
			}
			this.currentProject.saveToFile(file);
			this.projectFile = file;
			Settings.addRecentFile(file.getPath());
			return true;
		} catch (Exception ex) {
			JOptionPane.showMessageDialog(this, "Failed to save the project: " + ex.toString(), "Save failure", JOptionPane.ERROR_MESSAGE);
			return false;
		}
	}

	/**
	 * Loads a project from a file.<br>
	 * The currently open project will be closed.
	 * @param file project file to load, if null an open file dialog will be shown
	 * @return true if the project was successfully loaded, false if not
	 */
	private boolean loadProject(File file){
		if (file == null){
			JFileChooser dialog = new JFileChooser(this.projectFile);
			dialog.setFileFilter(new FileNameExtensionFilter("Tree workbench files" ,"twb"));
			if (dialog.showOpenDialog(this) != JFileChooser.APPROVE_OPTION) return false;
			file = dialog.getSelectedFile();
		}
		Project project;

		if (!askSave()) return false;

		try{
			project = Project.loadFromFile(file);
		} catch (Throwable ex) {
			Throwable t = ex;
			t.printStackTrace();
			while (t instanceof InvocationTargetException && t.getCause() != null) t = t.getCause();
			
			JOptionPane.showMessageDialog(this, "Failed to load project from file '" + file.getName() + "': " + t.toString(), "Project load error", JOptionPane.ERROR_MESSAGE);
			return false;
		}
		
		closeAllEditors();
		
		this.projectFile = file;
		this.currentProject = project;
		this.treeview.setSelectionPath(null);
		this.treeview.setModel(new ItemTreeModel(project));
		//Expend all item class nodes
		for (Class<? extends Item> itemClass : Project.getItemClasses()){
			this.treeview.expandPath(new TreePath(new Object[]{project, itemClass}));		
		}

		this.currentProject.addProjectListener(new Project.ProjectEventListener(){
			@Override
			public void onProjectChanged() {updateTitle();}
			@Override
			public void onItemEdited(Item item) {updateTitle();}
			@Override
			public void onItemRenamed(Item item) {updateTitle();}
		});
		updateTitle();

		Settings.addRecentFile(file.getPath());
		
		return true;
	}

	/**
	 * Creates a new item of the given class, prompts the user for the item name. 
	 * @param itemClass class of the item
	 */
	private void createNewItem(Class<? extends Item> itemClass){
		boolean validName = false;
		String name = null;
		while (!validName){
			name = JOptionPane.showInputDialog(this, "Enter " + Item.getItemClassName(itemClass) + " name:");
			if (name == null || name.length() == 0) return;
			try {
				this.currentProject.checkValidNewItemName(name);
				validName = true;
			} catch (InvalidItemNameException ex){
				JOptionPane.showMessageDialog(this, ex.toString(), "Invalid Name", JOptionPane.ERROR_MESSAGE);
				validName = false;
			}
		}

		Item newItem;
		try{
			newItem = itemClass.getConstructor(String.class, Project.class).newInstance(name, this.currentProject);
		} catch (Exception ex) {
			Throwable t = ex;
			t.printStackTrace();
			while (t instanceof InvocationTargetException && t.getCause() != null) t = t.getCause();

			JOptionPane.showMessageDialog(this, "Failed to create a new item: " + t.toString(), "Exception", JOptionPane.ERROR_MESSAGE);
			return;
		}
		this.currentProject.addItem(newItem);

		editItem(newItem); //, true);
	}

	/**
	 * Imports a tree from an XML file. <br> The XML file is selected by the user in a file open dialog.
	 * A new Item will be added to the project if the import is successful.
	 * @param <S> class of the symbol to be used by the XML tree parser
	 * @param symbolClass class of the symbol to be used by the XML tree parser. Supported values are RankedSymbol.class (will result in a TreeItem) and UnrankedSymbol (will result in a HedgeItem). 
	 * @return true if the import succeeds, false if not
	 */
	private <S extends Symbol> boolean importTreeFromXML(Class<S> symbolClass){
		JFileChooser dialog = new JFileChooser();
		dialog.setFileFilter(new FileNameExtensionFilter("XML files" ,"xml"));
		if (dialog.showOpenDialog(this) != JFileChooser.APPROVE_OPTION) return false;
		File file = dialog.getSelectedFile();

		Tree<S> tree;

		try {
			tree = XMLTreeParser.parseFromXML(file, false, symbolClass);
		} catch (Exception e) {
			e.printStackTrace();
			JOptionPane.showMessageDialog(this, "Failed to import file '" + file.getAbsolutePath() + "': " + e.getMessage(), "XML import exception", JOptionPane.ERROR_MESSAGE);
			return false;
		}
		String name = this.currentProject.convertToValidNewItemName(file.getName());

		AbstractTreeItem item = AbstractTreeItem.fromTree(name, this.currentProject, tree);
		this.currentProject.addItem(item);

		return true;
	}

	/**
	 * Removes the given item from the project.
	 * @param item item to remove
	 * @return true if the item was removed, false if the user aborted
	 */
	private boolean removeItem(Item item){
		int ret = JOptionPane.showConfirmDialog(this, "Do you want to remove the " + Item.getItemClassName(item.getClass()) + " '" + item.getName() + "'?" , "Confirm delete", JOptionPane.YES_NO_OPTION);
		if (ret != JOptionPane.YES_OPTION) return false;
		if (this.visibleEditor != null && item == this.visibleEditor.getItem()) closeCurrentEditor();
		this.openEditors.remove(item);
		this.currentProject.removeItem(item);
		return true;
	}
	/**
	 * Exits the current editor and loads a new editor for the given item.
	 * The current editor can refuse to close, in this case the editor remains unchanged.
	 * @param item item to edit
	 * @return true if the item editor as successfully switched, false if the current editor refused to close
	 */
	// * @param force do not call canClose() on the item, just close it forcefully loosing unsaved changes. Use with caution.	
	private boolean editItem(Item item){ //, boolean force){
		if (this.visibleEditor != null) {
			this.editorContainer.remove(this.visibleEditor);
		}
		
		assert(item != null);
		
		System.out.println("Edit: " + item.getName());
		Editor editor = this.openEditors.get(item);
		if (editor == null){
			editor = item.getEditor();
			this.openEditors.put(item, editor);
		}
		this.visibleEditor = editor;
		
		this.editorNameLabel.setText(this.visibleEditor.getName() + " - " + item.getName());
		this.editorContainer.add(this.visibleEditor, BorderLayout.CENTER);
		this.editorCloseButton.setVisible(true);
		this.treeview.setSelectionPath(new TreePath(new Object[]{this.currentProject, item.getClass(), item}));
		//TODO: Figure out why the window is not properly redrawn without this hack.
		this.editorContainer.repaint();
		
		updateTitle();
		return true;
	}
	
	private void closeCurrentEditor() {
		if (this.visibleEditor != null){
			this.openEditors.remove(this.visibleEditor.getItem());
			this.visibleEditor.close();
			this.editorContainer.remove(this.visibleEditor);
		}
		this.visibleEditor = null;
		this.editorNameLabel.setText("Nothing selected");
		this.editorCloseButton.setVisible(false);
		//TODO: Figure out why the window is not properly redrawn without this hack.
		this.editorContainer.repaint();
		updateTitle();
	}
	
	private void closeAllEditors() {
		if (this.visibleEditor != null) this.editorContainer.remove(this.visibleEditor);
		for (Editor editor : this.openEditors.values()){
			editor.close();
		}
		this.openEditors.clear();
		this.visibleEditor = null;
		this.editorNameLabel.setText("Nothing selected");
		this.editorCloseButton.setVisible(false);
		//TODO: Figure out why the window is not properly redrawn without this hack.
		this.editorContainer.repaint();
		updateTitle();
	}

	/**
	 * Asks the user to save the current project if it has unsaved changes.<br>
	 * If no project is loaded or there are no unsaved changes, this function simply returns true.
	 * Otherwise it prompts the user if he would like to save the changes.
	 * Cancel yields to returning false, indicating that the project should no be closed.
	 * No yields to true, indicating that the project can closed.
	 * Yes causes the project to be saved and returns if the save process was successful.
	 * @return see description
	 */
	private boolean askSave(){
		if (this.currentProject == null) return true; //can happen on very first "newProject()" call.
		if (this.currentProject.isDirty() == false) return true;
		List<Editor> dirtyEditors = new ArrayList<Editor>();
		StringBuilder msg = new StringBuilder("There are unsaved changes in:\n");
		msg.append("-");
		msg.append(this.currentProject.getName());
		msg.append("\t (Project not saved to disk)");
		msg.append("\n");
		for (Editor e : this.openEditors.values()){
			if (e.isDirty()){
				msg.append("  - ");
				msg.append(e.getItem().getName());
				msg.append("\t (Changes not applied to project)\n");
				dirtyEditors.add(e);
			}
		}
		
		msg.append("Do you want to save now?");
		int ret = JOptionPane.showConfirmDialog(this, msg.toString(), "Save?", JOptionPane.YES_NO_CANCEL_OPTION);
		if (ret == JOptionPane.CANCEL_OPTION){
			return false;
		} if (ret == JOptionPane.NO_OPTION){
			return true;
		} else {
			return saveProject(this.projectFile, false);
		}
	}

	/**
	 * Updates the window title, to show the current project and item.
	 */
	private void updateTitle(){
		StringBuilder s = new StringBuilder("Tree Automaton Workbench");
		if (this.currentProject != null) {
			s.append(" - ");
			s.append(this.currentProject.getName());
			if (this.currentProject.isDirty()) s.append(" *");
		}
		if (this.visibleEditor != null){
			s.append(" - ");
			s.append(this.visibleEditor.getItem().getName());
			if (this.visibleEditor.isDirty()) s.append(" *");
		}
		this.setTitle(s.toString());
	}
	
	/**
	 * Returns the currently loaded project.
	 * @return the currently loaded project
	 */
	public Project getCurrentProject(){
		return this.currentProject;
	}
	
	/**
	 * Main program - currently just for testing.
	 * @param args arguments passed to vm - not used here
	 */
	public static void main(String[] args){
		Locale.setDefault(Locale.US); //All messages are in English, disable the java internal i18n
		JFrame mainWindow = new MainWindow();
		mainWindow.setVisible(true);
	}

	/**
	 * Tree model for the item editor tree on the left side of the main window.
	 * @author Philipp
	 */
	private class ItemTreeModel implements TreeModel{

		private Project project;
		private List<TreeModelListener> listeners = new ArrayList<TreeModelListener>();

		ItemTreeModel(Project project){
			this.project = project;
			this.project.addProjectListener(new Project.ProjectEventListener(){
				@Override
				public void onProjectChanged()  {fireProjectChanged();}
				@Override
				public void onItemEdited(Item item)  {fireItemChanged(item);}
				@Override
				public void onItemRenamed(Item item)  {
					fireClassGroupChanged(item.getClass()); //redraw all items of this class, because the sorting order may have changed.
					treeview.setSelectionPath(new TreePath(new Object[]{currentProject, item.getClass(),item})); //update selection, this item may have moved.
				}
				@Override
				public void onItemAdded(Item item)   {fireItemAdded(item);}
				@Override
				public void onItemRemoved(Item item) {fireItemRemoved(item);}
				@Override
				public void onItemEditorChanged(Item item, Editor editor) {fireItemChanged(item);}
			});
		}

		@Override
		public Object getRoot() {
			return this.project;
		}

		@Override
		@SuppressWarnings("unchecked")
		public Object getChild(Object parent, int index) {
			if (parent instanceof Project){
				return Project.getItemClasses().get(index) ;
			} else if (parent instanceof Class){
				return this.project.getItems((Class<? extends Item>)parent).get(index);
			} else {
				return null;
			}
		}
		@Override
		@SuppressWarnings("unchecked")
		public int getChildCount(Object parent) {
			if (parent instanceof Project){
				return Project.getItemClasses().size();
			} else if (parent instanceof Class){
				return this.project.getItems((Class<? extends Item>)parent).size();
			} else {
				return 0;
			}
		}
		@Override
		@SuppressWarnings("unchecked")
		public int getIndexOfChild(Object parent, Object child) {
			if (parent instanceof Project){
				return Project.getItemClasses().indexOf(child) ;
			} else if (parent instanceof Class){
				return this.project.getItems((Class<? extends Item>)parent).indexOf(child);
			} else {
				return -1;
			}
		}

		@Override
		@SuppressWarnings("unchecked")
		public boolean isLeaf(Object node) {
			if (node instanceof Project){
				return false;
			} else if (node instanceof Class){
				return this.project.getItems((Class<? extends Item>)node).isEmpty();
			} else {
				return true;
			}
		}

		/**
		 * To be called after an item has been added to the project. Updates the tree to show it.
		 * @param item the item added.
		 */
		private void fireItemAdded(Item item){
			TreeModelEvent e = makeItemEvent(item);
			for (TreeModelListener l : this.listeners){
				l.treeNodesInserted(e);
			}
		}
		/**
		 * To be called BEFORE an item is removed from the project. Updates the tree, removing it.
		 * @param item the item about to be removed.
		 */
		private void fireItemRemoved(Item item){
			TreeModelEvent e = makeItemEvent(item);
			for (TreeModelListener l : this.listeners){
				l.treeNodesRemoved(e);
			}
		}
		/**
		 * To be called after an item has been changed (e.g. dirty state flipped). 
		 * Updates the tree, redrawing it.
		 * @param item the item changed.
		 */
		private void fireItemChanged(Item item){
			TreeModelEvent e = makeItemEvent(item);
			for (TreeModelListener l : this.listeners){
				l.treeNodesChanged(e);
			}
		}
		
		private void fireClassGroupChanged(Class<? extends Item> itemClass){
			Object[] path = new Object[]{MainWindow.this.currentProject, itemClass};
			Object[] items = project.getItems(itemClass).toArray();
			int[] indices = new int[items.length];
			for (int i = 0; i < items.length; i++){indices[i] = i;}

			TreeModelEvent e = new TreeModelEvent(MainWindow.this, path, indices, items);
			for (TreeModelListener l : this.listeners){
				l.treeNodesChanged(e);
			}
		}

		private TreeModelEvent makeItemEvent(Item item){
			Object[] path = new Object[]{MainWindow.this.currentProject, item.getClass()};
			int[] newIndices = new int[]{this.getIndexOfChild(item.getClass(), item)};
			Object[] newNodes = new Object[]{item};
			return new TreeModelEvent(MainWindow.this, path, newIndices, newNodes);
		}

		private void fireProjectChanged(){
			Object[] path = new Object[]{MainWindow.this.currentProject};
			int[] newIndices = new int[]{};
			Object[] newNodes = new Object[]{MainWindow.this.currentProject};
			TreeModelEvent event = new TreeModelEvent(MainWindow.this, path, newIndices, newNodes);
			for (TreeModelListener l : this.listeners){
				l.treeNodesChanged(event);
			}
		}

		@Override
		public void addTreeModelListener(TreeModelListener l) {
			listeners.add(l);
		}
		@Override
		public void removeTreeModelListener(TreeModelListener l) {
			listeners.remove(l);

		}
		@Override
		public void valueForPathChanged(TreePath path, Object newValue) {
			Object node = path.getLastPathComponent();
			if (node instanceof Project){
				if (((Project)node).getName().equals(newValue)) return; //name unchanged
				((Project)node).setName((String)newValue);
				fireProjectChanged();
			} else if (node instanceof Item){
				String newName = (String)newValue;
				if (((Item)node).getName().equals(newName)) return; //name unchanged
				try {
					MainWindow.this.currentProject.checkValidNewItemName(newName);
				} catch (InvalidItemNameException ex){
					JOptionPane.showMessageDialog(MainWindow.this, ex.toString(), "Invalid Name", JOptionPane.ERROR_MESSAGE);
					return;
				}
				((Item)node).setName(newName);
				fireItemChanged((Item)node);
			}

		}

	}

	class ItemNodeRenderer extends DefaultTreeCellRenderer{

		private ImageIcon projectIcon = Resources.loadIcon("node-project.png");
		private ImageIcon classIcon = Resources.loadIcon("node-class.png");
		private HashMap<Class<? extends Item>,ImageIcon> itemClassIcons = new HashMap<Class<? extends Item>,ImageIcon>();

		public ItemNodeRenderer(){
			for (Class<? extends Item> itemClass : Project.getItemClasses()){
				itemClassIcons.put(itemClass, Resources.loadIcon("node-" + itemClass.getSimpleName().toLowerCase() + ".png"));
			}
		}
		
		@Override
		@SuppressWarnings("unchecked")
		public Component getTreeCellRendererComponent(JTree tree, Object node,boolean sel,boolean expanded,boolean leaf,int row,boolean hasFocus) {
			super.getTreeCellRendererComponent(tree, node, sel,expanded, leaf, row, hasFocus);
			if (node instanceof Project){
				Project project = (Project)node;
				this.setText(project.getName() + (project.isDirty() ? " *" : ""));
			} else if (node instanceof Class){
				this.setText(Item.getItemClassName((Class<? extends Item>)node));
			} else if (node instanceof Item){
				Editor editor = MainWindow.this.openEditors.get(node);
				if (editor != null){
					this.setText(((Item)node).getName() + (editor.isDirty() ? " *" : ""));
				} else {
					this.setText(((Item)node).getName());
				}
			}
			this.setIcon(getNodeIcon(node));
			return this;
		}

		public ImageIcon getNodeIcon(Object node){
			if (node instanceof Project){
				return this.projectIcon;
			} else if (node instanceof Class<?>){
				return this.classIcon;
			} else if (node instanceof Item){
				return this.itemClassIcons.get(node.getClass());
			} else {
				return null;
			}
		}
	}

	class ItemNodeEditor extends DefaultTreeCellEditor{

		public ItemNodeEditor(JTree tree, DefaultTreeCellRenderer renderer) {
			super(tree, renderer);
		}

		@Override
		public Component getTreeCellEditorComponent(JTree tree, Object node, boolean isSelected, boolean expanded, boolean leaf, int row) {
			Component comp = super.getTreeCellEditorComponent(tree, node, isSelected, expanded, leaf, row);
			// HACK: DefaultTreeCellEditor uses calls to getLeafIcon(), getOpenIcon() and getClosedIcon()
			//       of the renderer to get the icon, but doesn't supply a node, so we can't implement them to return node specific icons.
			//       This hack overwrites the icon directly in the DefaultTreeCellEditor instance.
			//       after getTreeCellEditorComponent fetched the wrong icon.
			this.editingIcon = ((ItemNodeRenderer)renderer).getNodeIcon(node);  
			return comp;
		}

		@Override
		public boolean isCellEditable(EventObject event) {
			TreePath path = null;
			if (event == null) path = tree.getSelectionPath(); //manual edit trigger causes null to be passed here.
			
			//FIXME: Mouse editing immediately starts instead of waiting a few hundred milliseconds, making it impossible to do double clicks. Disable mouse editing for now.
			//if (event instanceof MouseEvent)  path = tree.getPathForLocation(((MouseEvent)event).getX(), ((MouseEvent)event).getY());
			
			if (path != null){
				Object node = path.getLastPathComponent();
				if (node instanceof Class<?>){
					//System.out.println("NOT Editable: " + node.toString());
					return false;
				} else {
					//System.out.println("Editable: " + node.toString());
					return true;
				}
			}
			return false;
		}


	}

}
