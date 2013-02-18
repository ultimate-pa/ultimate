/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.gui.misc;

import java.util.ArrayList;


/**
 * @author dietsch
 *
 */
public class GroupEntry extends TreeViewEntry {

	private ArrayList<TreeViewEntry> gEntries;
	
	public GroupEntry(String entryName,GroupEntry parent){
		super(entryName,parent);
		this.gEntries = new ArrayList<TreeViewEntry>();
	}
	
	public Object[] getEntries(){
		return this.gEntries.toArray();
	}

	
	public boolean removeEntry(TreeViewEntry entry){
		return gEntries.remove(entry);
	}
	
	public boolean addEntry(TreeViewEntry entry){
		return gEntries.add(entry);
	}
	
}
