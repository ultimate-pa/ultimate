package de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg;

import de.uni_freiburg.informatik.ultimate.model.AbstractAnnotations;

public abstract class RCFGEdgeAnnotation extends AbstractAnnotations{

	private static final long serialVersionUID = 1L;
	
	protected RCFGEdge mBackingEdge;

	protected RCFGEdgeAnnotation(RCFGEdge backingEdge){
		mBackingEdge = backingEdge;
	}
	
	public RCFGEdge getBackingEdge() {
		return mBackingEdge;
	}
	
	@Override
	public boolean equals(Object obj) {
		if(obj instanceof RCFGEdgeAnnotation){
			return mBackingEdge.equals(((RCFGEdgeAnnotation)obj).mBackingEdge);
		} else if (obj instanceof RCFGEdge){
			return mBackingEdge.equals(obj);
		}
		return super.equals(obj);
	}
	
	@Override
	public int hashCode() {
		return mBackingEdge.hashCode();
	}
	
	@Override
	public String toString() {
		return mBackingEdge.toString();
	}

}
