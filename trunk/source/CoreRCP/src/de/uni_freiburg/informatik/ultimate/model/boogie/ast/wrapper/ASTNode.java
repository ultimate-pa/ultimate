package de.uni_freiburg.informatik.ultimate.model.boogie.ast.wrapper;

import java.io.Serializable;
import java.util.LinkedList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.model.BoogieLocation;
import de.uni_freiburg.informatik.ultimate.model.ILocation;
import de.uni_freiburg.informatik.ultimate.model.Payload;

public abstract class ASTNode implements Serializable{
	/**
	 * long serialVersionUID
	 */
	private static final long serialVersionUID = -8972919761308612994L;
	private Payload payload;
	
	public ASTNode(ILocation location) {
		if (payload == null) {
			payload = new Payload(location, "don't know what to write here");
		}
		else {
			payload.setLocation(location);
		}
		if (location instanceof BoogieLocation) {
			((BoogieLocation) location).setASTNode(this); 
		}
	}
	
	public List<Object> getChildren() {
		return new LinkedList<Object>();
	}
	
	public Payload getPayload() {
		if (payload == null) {
			payload = new Payload(null, this.getClass().getName().toUpperCase());
//			payload.setChildCount(getChildren().size());
		}
		return payload;
	}
	
	public ILocation getLocation() {
		return getPayload().getLocation();
	}
}
