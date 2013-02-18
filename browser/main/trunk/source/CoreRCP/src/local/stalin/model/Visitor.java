package local.stalin.model;

/**
 *
 * @author bisser
 * @version 0.1.3  
 * $LastChangedDate: 2008-03-07 16:42:04 +0100 (Fr, 07. Mär 2008) $
 * $LastChangedBy: dietsch $
 * $LastChangedRevision: 500 $ 
 */
public abstract class Visitor
{

	public abstract void init();
	
	public abstract boolean process(IPayload payload);
	
	public abstract Object[] process(IPayload payload, Object[] params);
	
	public abstract void reset();
	
}
