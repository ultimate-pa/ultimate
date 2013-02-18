package local.stalin.ep.interfaces;

import local.stalin.model.IElement;


/**
 * interface for Transformer plugins
 * transforms One graph into another
 * 
 * 
 * open Question:
 * may transformation be destructive?
 *
 * 
 * @author Christian Ortolf
 *
 */
public interface IGenerator extends IModifyingTool {

	IElement getModel();	
}
