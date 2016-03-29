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

import java.io.File;
import java.io.IOException;
import java.lang.reflect.InvocationTargetException;
import java.util.*;
import java.util.regex.*;

import javax.xml.parsers.*;
import javax.xml.transform.*;
import javax.xml.transform.dom.DOMSource;
import javax.xml.transform.stream.StreamResult;
import org.w3c.dom.*;
import org.xml.sax.SAXException;

/**
 * GUI Project class, contains all items currently loaded.
 * @author Philipp
 *
 */
public class Project {

	/*
	 * Class Members / Methods
	 */
	
	/**
	 * All item classes the GUI knows about.
	 */
	private static final List<Class<? extends Item>> itemClasses = new ArrayList<Class<? extends Item>>();
	static{
		itemClasses.add(TreeItem.class);
		itemClasses.add(FTAItem.class);
		itemClasses.add(HomomorphismItem.class);
		itemClasses.add(TreeTransducerItem.class);
		itemClasses.add(HedgeItem.class);
		itemClasses.add(HedgeAutomatonItem.class);
		itemClasses.add(ScriptItem.class);
	}
	/**
	 * Returns the list of all item classes the GUI knows about.
	 * @return the list of all item classes the GUI knows about
	 */
	public static List<Class<? extends Item>> getItemClasses() {
		return itemClasses;
	}
	/**
	 * Find an item class by the internal simple name (NOT the user visible class name).
	 * @param simpleName simple name of the class to search for
	 * @return the class object if found, or null if not
	 */
	public static Class<? extends Item> findItemClassBySimpleName(String simpleName){
		for (Class<? extends Item> itemClass : itemClasses){
			if (itemClass.getSimpleName().equals(simpleName)) return itemClass;
		}
		return null;
	}
	
	/**
	 * Loads a project from the given file.
	 * @param file file to load from
	 * @return the loaded project
	 * @throws SAXException XML lib exception
	 * @throws IOException IO access problem (file not found, not readable, etc.)
	 * @throws ParserConfigurationException XML lib exception
	 * @throws IllegalArgumentException reflection exception, item class does not properly implement fromXML
	 * @throws SecurityException  reflection exception, item class does not properly implement fromXML
	 * @throws IllegalAccessException  reflection exception, item class does not properly implement fromXML
	 * @throws InvocationTargetException  reflection exception, item class does not properly implement fromXML
	 * @throws NoSuchMethodException reflection exception, item class does not properly implement fromXML
	 */
	public static Project loadFromFile(File file) throws SAXException, IOException, ParserConfigurationException, IllegalArgumentException, SecurityException, IllegalAccessException, InvocationTargetException, NoSuchMethodException{
		Document xmldoc = DocumentBuilderFactory.newInstance().newDocumentBuilder().parse(file);
		Element root = (Element)xmldoc.getFirstChild();
		
		Project project = new Project(root.getAttribute("name"));
		
		for (int i = 0; i < root.getChildNodes().getLength(); i++){
			Element itemClassElement = (Element)root.getChildNodes().item(i);
			String itemClassSimpleName = itemClassElement.getNodeName();
			Class<? extends Item> itemClass = Project.findItemClassBySimpleName(itemClassSimpleName);
			for (int j = 0; j < itemClassElement.getChildNodes().getLength(); j++){
				Node itemElement = itemClassElement.getChildNodes().item(j);
				Item item = (Item)itemClass.getMethod("fromXML", Element.class, Project.class).invoke(itemClass, itemElement, project);
				project.getItems(itemClass).add(item);
			}
			sortItemList(project.items.get(itemClass));
		}
		return project;
	}
	
	/*
	 *Instance Members / Methods 
	 */
	
	/**
	 * Lists of Items in this project, keyed by class.
	 */
	private HashMap<Class<? extends Item>, List<Item>> items = new HashMap<Class<? extends Item>, List<Item>>();	
	
	/**
	 * All registered project event listeners.
	 */
	private List<ProjectEventListener> eventListeners = new ArrayList<ProjectEventListener>();
	
	/**
	 * Name of this project.
	 */
	private String name;
	
	private boolean dirty = false;
	
	/**
	 * Creates a new project.
	 * @param name project name
	 */
	public Project(String name){
		this.name = name;
		
		//Init item lists.
		for (Class<? extends Item> itemClass : itemClasses){
			this.items.put(itemClass, new ArrayList<Item>());
		}
	}
	
	
	/**
	 * List of all items of a given class in the project.
	 * @param itemClass class of the items
	 * @return all items of a given class in the project
	 */
	public List<Item> getItems(Class<? extends Item> itemClass) {
		return items.get(itemClass);
	}
	
	/**
	 * Adds an item to the project.
	 * @param item item to add
	 */
	public void addItem(Item item){
		List<Item> classItems = items.get(item.getClass());
		classItems.add(item);
		sortItemList(classItems);
		
		for (ProjectEventListener listener : eventListeners) {listener.onItemAdded(item);}
		setDirty(true);
	}
	/**
	 * Removes an item from the project.
	 * @param item item to remove
	 */
	public void removeItem(Item item){
		for (int i = this.eventListeners.size() -1; i >= 0; i--){ //onItemRemoved may remove the listener, can't use enumerating loop here.
			this.eventListeners.get(i).onItemRemoved(item);
		}
		items.get(item.getClass()).remove(item);
		setDirty(true);
	}
	
	/**
	 * Searches for an item with the given name and returns it if found.
	 * @param name the name to search for.
	 * @return the item with the given name or null if there is no item with this name.
	 */
	public Item getItemByName(String name){
		for (Class<? extends Item> itemClass : itemClasses){
			for (Item item : this.items.get(itemClass)){
				if (item.getName().equals(name)) return item;
			}
		}
		return null;
	}
	
	/**
	 * Sets a new project name.
	 * @param name new project name
	 */
	public void setName(String name) {
		this.name = name;
		setDirty(true);
		for (ProjectEventListener listener : eventListeners) {listener.onProjectChanged();}
	}
	/**
	 * Returns the project name.
	 * @return the project name
	 */
	public String getName() {
		return this.name;
	}
	
	/**
	 * Sets the dirty status of the project. Dirty means the project has unsaved changes.
	 * @param dirty true if the project has unsaved changes
	 */
	public void setDirty(boolean dirty){
		if (this.dirty != dirty){
			this.dirty = dirty;
			for (ProjectEventListener listener : eventListeners) {listener.onProjectChanged();}
		}
	}
	
	/**
	 * Returns the project dirty status. <br> Dirty means the project has unsaved changes.
	 * @return true if the project has unsaved changes, false if not
	 */
	public boolean isDirty(){
		return this.dirty;
	}
	
	/**
	 * Adds a listener to project events (such as items added to the project or project name changed). 
	 * @param l listener to add
	 */
	public void addProjectListener(ProjectEventListener l){
		this.eventListeners.add(l);
	}
	
	/**
	 * Removes a project events listener. 
	 * @param l the listener to remove
	 */
	public void removeProjectListener(ProjectEventListener l){
		this.eventListeners.remove(l);
	}
	
	
	/**
	 * Saves the project to the given file. 
	 * @param file file to save to.
	 * @throws ParserConfigurationException XML lib exception
	 * @throws TransformerConfigurationException XML lib exception
	 * @throws TransformerException XML lib exception
	 * @throws TransformerFactoryConfigurationError XML lib exception
	 */
	public void saveToFile(File file) throws ParserConfigurationException, TransformerException, TransformerFactoryConfigurationError{
		Document xmldoc = DocumentBuilderFactory.newInstance().newDocumentBuilder().newDocument();
		Element root = xmldoc.createElement("TreeWorkbenchProject");
		root.setAttribute("name", this.name);
		xmldoc.appendChild(root);
		for (Class<? extends Item> itemClass : Project.getItemClasses()){
			Element itemClassElement = xmldoc.createElement(itemClass.getSimpleName());
			root.appendChild(itemClassElement);
			for (Item item : this.items.get(itemClass)){
				Element itemElement = xmldoc.createElement("Element");
				itemClassElement.appendChild(itemElement);
				itemElement.setAttribute("name", item.getName());
				item.toXML(itemElement);
			}
		}
		//Write the XML doc to the file. This is ridiculously complex.
		Source xmlsource = new DOMSource(xmldoc);
		Result result = new StreamResult(file);
		TransformerFactory.newInstance().newTransformer().transform(xmlsource, result);
		setDirty(false);
	}
	
	@Override
	public String toString(){
		return this.name;
	}
	
	/**
	 * Check if the given name is valid or not.<br>
	 * A name is valid if it matches the regexp [a-z_A-Z][a-z_A-Z0-9]*. 
	 * @param name name to validate
	 * @throws InvalidItemNameException thrown if the name is not valid
	 */
	public void checkValidNewItemName(String name) throws InvalidItemNameException{
		if (!Pattern.matches(("^[a-z_A-Z][a-z_A-Z0-9]*$"), name)){
			throw new InvalidItemNameException("'" + name + "' is not a valid name.\nNames may only contain letters, digits or underscores and cannot start with digits");
		}
		if (getItemByName(name) != null){
			throw new InvalidItemNameException("There is already an item named '" + name + "'. Item names must be unique.");
		}
	}
	
	/**
	 * Converts a given name to a valid project item name. <br>
	 * All invalid chars contained are replaced with _.
	 * If the resulting name is already used in the project a counter number will be 
	 * appended to make it unique.
	 * @param refName input name
	 * @return valid, unique item name
	 */
	public String convertToValidNewItemName(String refName){
		StringBuffer sb = new StringBuffer(refName); 
		Pattern p = Pattern.compile("^[^a-z_A-Z]$" );
		if (p.matcher(refName).matches()){
			sb.setCharAt(0, '_');
		}
		
		p = Pattern.compile("[^a-z_A-Z0-9]");
		Matcher m = p.matcher(sb);
		while (m.find()){
			sb.setCharAt(m.start(),'_');
		}
		
		p = Pattern.compile(".*_(\\d+)$");
		while (getItemByName(sb.toString()) != null){
			m = p.matcher(sb.toString());
			if (m.matches()){
				int i = Integer.valueOf(m.group(1));
				sb.replace(m.start(1), m.end(1), String.valueOf(i+1));
			} else {
				sb.append("_1");
			}
		}
		return sb.toString();
	}
	
	private static void sortItemList(List<Item> items){
		Collections.sort(items, new Comparator<Item>(){
			@Override
			public int compare(Item o1, Item o2) {
				return o1.getName().compareTo(o2.getName());
			}
		});
	}

	/**
	 * Fires an renamed event for an item. <br>
	 * An renamed event is raised when the user has changed the name of an existing item
	 * @param item item changed
	 */
	protected void fireItemRenamed(Item item){
		setDirty(true);
		sortItemList(this.items.get(item.getClass()));
		for (ProjectEventListener listener : eventListeners) {listener.onItemRenamed(item);}
	}
	
	/**
	 * Fires an edit event for an item. <br>
	 * An edit event is raised when the user edits an item in an editor window.
	 * @param item item changed
	 */
	protected void fireItemEdited(Item item){
		setDirty(true);
		for (ProjectEventListener listener : eventListeners) {listener.onItemEdited(item);}
	}
	
	/**
	 * Fires an item editor change event.<br>
	 * Such an event is raised when an item is opened for editing and when the editor is closed.  
	 * @param item item which editor changed
	 * @param editor new editor or null if the editor was closed
	 */
	public void fireItemEditorChanged(Item item, Editor editor){
		for (ProjectEventListener listener : eventListeners) {listener.onItemEditorChanged(item,editor);}
	}
	
	/**
	 * Fires a content set event for an item. <br>
	 * A content set event is raised when the contents of an item is updated, usually by the user clicking the "apply" button in an editor.
	 * @param item item changed
	 */
	protected void fireItemContentSet(Item item){
		for (ProjectEventListener listener : eventListeners) {listener.onItemContentSet(item);}
	}
	
	static abstract class ProjectEventListener {
		public void onProjectChanged(){}
		public void onItemAdded(Item item) {}
		public void onItemRemoved(Item item) {}
		public void onItemEdited(Item item) {}
		public void onItemRenamed(Item item) {}
		public void onItemContentSet(Item item){}
		public void onItemEditorChanged(Item item, Editor editor) {}
	}
	
	class InvalidItemNameException extends Exception{
		public InvalidItemNameException(String message){
			super(message);
		}
	}
}
