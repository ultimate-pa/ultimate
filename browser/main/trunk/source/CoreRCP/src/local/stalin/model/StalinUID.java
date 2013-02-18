package local.stalin.model;

import java.io.Serializable;
import java.util.UUID;

/**
 * This is an updated StalinUID. It uses UUID instead of UID.
 * UUID provides its own compare methods so you only have to compare
 * Strings if you saved a StalinUID as a String somewhere. Please note
 * that creating a random UUID takes three times the time of creating
 * a UID. That still should not matter because creating 100000 UUIDs
 * takes some 200ms.
 * <br><br>
 * @author dietsch
 * @since 486
 * <br><br>
 * $LastChangedBy: dietsch $ <br>
 * $LastChangedDate: 2008-11-14 15:14:26 +0100 (Fr, 14. Nov 2008) $ <br>
 * $LastChangedRevision: 793 $
 *
 */
public class StalinUID implements Serializable {

	private static final long serialVersionUID = -5789249181482554415L;
	//private UID m_UID;
	private UUID m_UID;
	private transient String m_UUIDString;
	
	/**
	 * Creates a new StalinUID
	 */
	public StalinUID() {
		//this.m_UID = new UID();
		this.m_UID = UUID.randomUUID();
	}
	
	/**
	 * Tests if another StalinUID equals this one
	 * @param uid the other StalinUID
	 * @return true if they are the same
	 */
	public boolean equals(StalinUID uid){
		//return this.m_UID.toString().equals(uid.m_UID.toString());
		return this.m_UID.equals(uid.m_UID);
	}
	
	/**
	 * Tests if another StalinUID represented by the parameter
	 * equals this StalinUID.
	 * @param uid The other StalinUID as String
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
	 * @param o the other possible StalinUID
	 * @return true if they are the same
	 */
	public boolean equals(Object o)
	{
		if(o instanceof StalinUID)
		{
			StalinUID uid = (StalinUID)o;
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
