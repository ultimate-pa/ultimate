package de.uni_freiburg.informatik.ultimate.model.boogie.ast;

import de.uni_freiburg.informatik.ultimate.model.location.BoogieLocation;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;
import de.uni_freiburg.informatik.ultimate.model.structure.BaseSimpleAST;

public class BoogieASTNode extends BaseSimpleAST<BoogieASTNode> {

	private static final long serialVersionUID = 5856434889026482850L;
	
	public BoogieASTNode(ILocation location) {
		super();
		
		getPayload().setLocation(location);
		
		if (location instanceof BoogieLocation) {
			((BoogieLocation) location).setBoogieASTNode(this); 
		}
	}
	
	public ILocation getLocation() {
		return getPayload().getLocation();
	}

}
