package de.uni_freiburg.informatik.ultimate.model;

import java.io.Serializable;
import java.util.UUID;

/**
 * This is an updated UltimateUID. It uses UUID instead of UID.
 * UUID provides its own compare methods so you only have to compare
 * Strings if you saved a UltimateUID as a String somewhere. Please note
 * that creating a random UUID takes three times the time of creating
 * a UID. That still should not matter because creating 100000 UUIDs
 * takes some 200ms.
 * <br><br>
 * @author dietsch
 * @since 486
 * <br><br>
 * $LastChangedBy$ <br>
 * $LastChangedDate$ <br>
 * $LastChangedRevision$
 *
 */
public class UltimateUID implements Serializable {

	private static final long serialVersionUID = -5789249181482554415L;
	//private UID m_UID;
	private UUID m_UID;
	private transient String m_UUIDString;
	
	/**
	 * Creates a new UltimateUID
	 */
	public UltimateUID() {
		//this.m_UID = new UID();
		this.m_UID = UUID.randomUUID();
	}
	
	/**
	 * Tests if another UltimateUID equals this one
	 * @param uid the other UltimateUID
	 * @return true if they are the same
	 */
	public boolean equals(UltimateUID uid){
		//return this.m_UID.toString().equals(uid.m_UID.toString());
		return this.m_UID.equals(uid.m_UID);
	}
	
	/**
	 * Tests if another UltimateUID represented by the parameter
	 * equals this UltimateUID.
	 * @param uid The other UltimateUID as String
	 * @return true if they are the same
	 */
	public boolean equals(String uid){
		if(m_UUIDString == null || m_UUIDString.length() == 0)
		{
			m_UUIDString = this.m_UID.toString();
		}
		return m_UUIDString.equals(uid);
	}
	
	/**
	 * Tests if another Object is the same
	 * @param o the other possible UltimateUID
	 * @return true if they are the same
	 */
	public boolean equals(Object o)
	{
		if(o instanceof UltimateUID)
		{
			UltimateUID uid = (UltimateUID)o;
			return equals(uid);
		}
		return false;
	}
	
	public int hashCode(){
		return m_UID.hashCode();
	}
	
	public String toString(){
		return m_UID.toString();
	}
}
