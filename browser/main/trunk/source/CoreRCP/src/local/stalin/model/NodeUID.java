package local.stalin.model;

import java.io.Serializable;
import java.rmi.server.UID;

public class NodeUID implements Serializable {

	private static final long serialVersionUID = 5467914622799796365L;
	private UID m_UID;

	public NodeUID() {
		this.m_UID = new UID();
	}

	public int hashCode() {
		return m_UID.hashCode();
	}

	public boolean equals(Object obj) {
		if(obj==null){
			return false;
		}
		return this.m_UID.toString().equals(obj.toString());
	}

	public String toString() {
		return m_UID.toString();
	}

}
