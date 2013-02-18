/**
 * 
 */
package local.stalin.gui.misc;

/**
 * @author  dietsch
 */
public abstract class TreeViewEntry {
	private String name;
	private TreeViewEntry parent;
	
	public TreeViewEntry(String entryName, TreeViewEntry parent){
		this.name = entryName;
		this.parent = parent;
	}
	
	/**
	 * @return  the parent
	 * @uml.property  name="parent"
	 */
	public Object getParent(){
		return parent;
	}
	
	/**
	 * @return  the name
	 * @uml.property  name="name"
	 */
	public String getName(){
		return this.name;
	}
}
