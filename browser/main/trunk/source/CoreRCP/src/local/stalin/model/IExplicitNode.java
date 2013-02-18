package local.stalin.model;

import java.util.List;

/**
 * This is the main interface for all nodes in graphs or trees
 * 
 * 
 * 	@author dietsch / bisser
 * 	@deprecated deprecated in stalin 2.0. Now edges can have labels themselves
 *	
 */
@Deprecated
public interface IExplicitNode extends IElement  {

    List<IEdge> getIncoming();

    List<IEdge> getOutgoing();

    boolean addOutgoing(IEdge edge);
    
    boolean addIncoming(IEdge edge);
    
    boolean removeOutgoing (IEdge edge);
    
    boolean removeIncoming (IEdge edge);
    
    void clearIncoming();
    
    void clearOutgoing();

    void setDepth(int depth);
    
}
