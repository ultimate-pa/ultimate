package de.uni_freiburg.informatik.ultimate.model;

import java.util.HashMap;

import de.uni_freiburg.informatik.ultimate.model.annotation.IAnnotations;
import de.uni_freiburg.informatik.ultimate.model.location.BoogieLocation;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;


/**
 * 
 * A concrete implementation of the IPayload interface. The payload contains all informations carried by a node. 
 * 
 * @author dietsch
 *
 */
public class Payload implements IPayload {
	
	/**
	 * 
	 */
	private static final long serialVersionUID = 9150283961581614549L;
//	protected int m_Depth;
//	protected int m_ChildCount;
	protected ILocation m_Location;
	protected String m_Name;
	protected UltimateUID m_ID;
	protected HashMap<String, IAnnotations> m_Annotations;
	protected boolean m_IsValue;
	
	
	
	public Payload() {
//		this.m_ChildCount = 0;
//		this.m_Depth = -1;
		this.m_IsValue = false;
	}
	
	public Payload(ILocation loc, String name){
		this();
		this.m_Location = loc;
		this.m_Name = name;
	}
	
	public Payload(ILocation loc, String name, boolean isValue){
		this();
		this.m_Location = loc;
		this.m_Name = name;
		this.m_IsValue = isValue;
	}
	
	public HashMap<String, IAnnotations> getAnnotations() {
		if(m_Annotations == null){
			this.m_Annotations = new HashMap<String, IAnnotations>();
		}
		return this.m_Annotations;
	}

	public UltimateUID getID() {
		if(m_ID == null){
			this.m_ID = new UltimateUID();
		}
		return this.m_ID;
	}

	public ILocation getLocation() {
		if(this.m_Location == null){
			this.m_Location = new BoogieLocation("",0,0,0,0,false);
		}
		return this.m_Location;
	}

	public String getName() {
		if (m_Name == null){
			return "";
		}
		return this.m_Name;
	}
	
	public void setAnnotations(
			HashMap<String, IAnnotations> annotations) {
		this.m_Annotations = annotations;

	}

	public void setLocation(ILocation loc) {
		this.m_Location = loc;		
	}

	public void setName(String name) {
		this.m_Name = name;
	}

//	public int getDepth() {
//		return this.m_Depth;
//	}
//
//	public void setDepth(int depth) {
//		this.m_Depth = depth;
//		
//	}
//
//	public int getChildCount() {
//		return this.m_ChildCount;
//	}
//
//	public void setChildCount(int count) {
//		this.m_ChildCount = count;
//		
//	}
	
	public String toString(){
		return this.getName();
	}
	
	public boolean hasAnnotation() {
		if(this.m_Annotations == null){
			return false;
		}
		return !this.m_Annotations.isEmpty();
	}
	
	public boolean hasLocation() {
		return (this.m_Location !=null);
	}

	public boolean hasID() {
		return (this.m_ID != null);
	}

	public boolean hasName() {
		return (this.m_Name !=null);
	}

	public boolean isValue() {
		return this.m_IsValue;
	}


}
