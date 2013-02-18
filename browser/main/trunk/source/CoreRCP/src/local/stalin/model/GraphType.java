/**
 * 
 */
package local.stalin.model;

import java.io.File;
import java.io.Serializable;
import java.text.DateFormat;
import java.text.SimpleDateFormat;
import java.util.Date;
import java.util.List;

import local.stalin.core.api.StalinServices;
import local.stalin.core.coreplugin.Activator;
import local.stalin.plugins.Constants;

import org.apache.log4j.Logger;
import org.eclipse.core.runtime.Assert;


/**
 * Intended for separating different types of graphs and trees 
 * like Call Graphs, Data Flow Graphs, AST 
 * Should also specify their special attributes
 * 
 * Change in Stalin 2.0:
 * 
 * A GraphType should be identified by its String representation.
 * Unlike object identity this should be preserved during serialization.
 * Therefore the equals method now checks for equal String representation instead
 * of object identity. In order to be consistent this change is carried to 
 * hashCode. 
 * 
 * The changes will allow the GraphType to remain a suitable key in the model managers
 * in-memory map and its string representation to be the key in the repository.
 * 
 * @author dietsch
 */
public class GraphType implements Serializable{
	

	/**
	 * long serialVersionUID
	 */
	private static final long serialVersionUID = -2922069733243189149L;

	private static Logger s_Logger = StalinServices.getInstance().getLogger(Activator.s_PLUGIN_ID);
	
	private int m_Size;
	
	private String m_Creator;
	private Date m_Created;
	private Date m_LastModified;
	private String m_LastModifier;
	private Type m_Type;
	private int m_Iteration;
	private boolean m_Touched;
	private List<String> m_FileNames;
	private DateFormat m_LastModifiedStringFormat;
	
	private boolean m_IsCyclic;
	private boolean m_IsDirected;
	private boolean m_IsTree;
	private boolean m_IsOrdered;
	private boolean m_IsMultiGraph;
	private boolean m_IsFinite;
	
	
	
	/**
	 * @author  dietsch
	 */
	public enum Type{AST,CG,CFG,DFG,CST,TS,PG,OTHER}
	
	public GraphType(String creatorPluginID, Type type, List<String> fileNames) {
		Assert.isNotNull(fileNames);
		Assert.isNotNull(type);
		this.m_Creator = creatorPluginID;
		this.m_Type = type;
		this.m_FileNames = fileNames;
		
		init();
	}
	
	public GraphType(String creatorPluginID, String type, List<String> fileNames) throws Exception{
		Assert.isNotNull(fileNames);
		Assert.isNotNull(type);
		this.m_Creator = creatorPluginID;
		this.m_FileNames = fileNames;
		this.m_Type = Type.OTHER;
		init();
	}

	/**
	 * Should be set AFTER a write operation was performed on this data structure was completed  
	 *
	 * @param modifierPluginID The ID of the plugin which performed the write operation
	 */
	public void modified(String modifierPluginID){
		this.setDirty(true);
		this.m_LastModifier = modifierPluginID;
		this.m_LastModified = new Date();
		this.m_Iteration++;
	}
	
	/* (non-Javadoc)
	 * @see java.lang.Object#equals(java.lang.Object)
	 */
	@Override
	public boolean equals(Object obj) {
		return this.toString().equals(obj.toString());
	}
	
	/* (non-Javadoc)
	 * @see java.lang.Object#hashCode()
	 */
	@Override
	public int hashCode() {
		return this.toString().hashCode();
	}
	
	/* (non-Javadoc)
	 * @see java.lang.Object#toString()
	 */
	public String toString(){
		StringBuffer sb = new StringBuffer();
		for (String fileName : this.m_FileNames) {
			sb.append(new File(fileName).getName());
		}
		sb.append(" " + this.m_Creator);
		sb.append(" " + this.m_Type);
		sb.append(" " + this.m_LastModifiedStringFormat.format(this.m_LastModified));
		return sb.toString();
	}
	
	public boolean isDirty(){
		return this.m_Touched;
	}
	
	public void setDirty(boolean flag){
		this.m_Touched = flag;
	}
	
	public String getCreator(){
		return m_Creator;
	}
	
	public Date getCreated(){
		return m_Created;
	}
	
	public String getLastModifier(){
		return m_LastModifier;
	}
	
	public Date getLastModified(){
		return m_LastModified;
	}
	
	public boolean isFromSource(){
		return (this.m_Iteration==0);
	}
	
	public Type getType(){
		return m_Type;
	}
	public boolean isCyclic(){
		return m_IsCyclic;
	}
	public boolean isDirected(){
		return m_IsDirected;
	}
	public boolean isGraph(){
		return m_IsTree;
	}
	public boolean isOrdered(){
		return m_IsOrdered;
	}
	public boolean isFinite(){
		return m_IsFinite;
	}
	public boolean isMulitGraph(){
		return m_IsMultiGraph;
	}
	public String getAbsolutePath(int i){
		return this.m_FileNames.get(i);
	}
	
	public String getFileName(int i) {
		String s = this.m_FileNames.get(i);
		if (s.contains(Constants.getFileSep())) {
			String fileSep = Constants.getFileSep();
			String[] names = s.split(fileSep);
			s = "";
			for (String k : names) {
				s += k.substring(k.lastIndexOf(File.separator) + 1) + fileSep;
			}
			s = s.substring(0, s.length() - 2);
		} else {
			s = s.trim();
			s = s.substring(s.lastIndexOf(File.separator) + 1);
		}
		return s;
	}
	
	public int getNumberOfFiles(){
		return this.m_FileNames.size();
	}
	

	private void init() {
		this.m_Touched = false;
		this.m_Iteration = 0;
		this.m_LastModifier = this.m_Creator;
		this.m_Created = new Date();
		this.m_LastModified = new Date();
		this.m_Size = 0;
		this.m_LastModifiedStringFormat = new SimpleDateFormat("dd.MM hh:mm:ss");
		setAttributes();
	}
	
	private void setAttributes() {
		switch (m_Type) {
		case AST:
			m_IsCyclic = false;
			m_IsDirected = true;
			m_IsTree = true;
			m_IsOrdered = true;
			m_IsMultiGraph = false;
			m_IsFinite = true;
			break;
		case CST:
			m_IsCyclic = false;
			m_IsDirected = true;
			m_IsTree = true;
			m_IsOrdered = true;
			m_IsMultiGraph = false;
			m_IsFinite = true;
			break;
		case DFG:
			m_IsCyclic = false;
			m_IsDirected = true;
			m_IsTree = true;
			m_IsOrdered = false;
			m_IsMultiGraph = false;
			m_IsFinite = true;
			break;
		case CFG:
			m_IsCyclic = true;
			m_IsDirected = true;
			m_IsTree = false;
			m_IsOrdered = false;
			m_IsMultiGraph = false;
			m_IsFinite = true;
			break;	
		case OTHER:
			m_IsCyclic = true;
			m_IsDirected = true;
			m_IsTree = false;
			m_IsOrdered = false;
			m_IsMultiGraph = true;
			m_IsFinite = false;
			break;
		default:
			s_Logger.error("Received wrong Type, throwing IllegalArgumentException...");
			throw new UnsupportedOperationException("Graphtype "+m_Type+" not implemented yet");
		}
	}

	public int getSize() {
		return this.m_Size;
	}

	public void setSize(int size) {
		this.m_Size = size;
	}
	
	public List<String> getFileNames()
	{
		return this.m_FileNames;
	}
	
}
