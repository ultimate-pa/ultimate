package de.uni_freiburg.informatik.ultimate.ep.interfaces;

import de.uni_freiburg.informatik.ultimate.model.IElement;


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
