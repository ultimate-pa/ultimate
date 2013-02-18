/**
 * 
 */
package local.stalin.gui.misc;


/**
 * @author dietsch
 *
 */
public class Entry extends TreeViewEntry {
	
	private String eValue;
	
	
	public Entry(String entryName, String value, GroupEntry parent){
		super(entryName,parent);
		this.eValue=value;

	}
	
	public String getValue(){
		return this.eValue;
	}

}
