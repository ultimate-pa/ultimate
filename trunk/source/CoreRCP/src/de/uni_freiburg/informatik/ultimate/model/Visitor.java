package de.uni_freiburg.informatik.ultimate.model;

/**
 *
 * @author bisser
 * @version 0.1.3  
 * $LastChangedDate$
 * $LastChangedBy$
 * $LastChangedRevision$ 
 */
public abstract class Visitor
{

	public abstract void init();
	
	public abstract boolean process(IPayload payload);
	
	public abstract Object[] process(IPayload payload, Object[] params);
	
	public abstract void reset();
	
}
