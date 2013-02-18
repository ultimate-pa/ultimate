package local.stalin.model.boogie.ast.wrapper;

import java.io.Serializable;
import java.util.LinkedList;
import java.util.List;

import local.stalin.model.Payload;

public abstract class ASTNode implements Serializable{
	/**
	 * long serialVersionUID
	 */
	private static final long serialVersionUID = -8972919761308612994L;
	private Payload payload;
	
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
}
