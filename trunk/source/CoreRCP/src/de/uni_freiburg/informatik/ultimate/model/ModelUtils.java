package de.uni_freiburg.informatik.ultimate.model;

import de.uni_freiburg.informatik.ultimate.model.boogie.ast.wrapper.ASTNode;

/**
 * Helper methods for Ultimate models.
 */
public final class ModelUtils {
	/**
	 * Takes annotations from one IElement (if any) and adds them to another
	 * IElement.
	 * 
	 * NOTE: duplicate method for ASTNode
	 * 
	 * @param oldE old IElement to take annotations from
	 * @param newE new IElement to add annotations to
	 */
	public static void mergeAnnotations(IElement oldE, IElement newE) {
	    IPayload oldPayload = oldE.getPayload();
	    if (oldPayload.hasAnnotation()) {
	        newE.getPayload().getAnnotations().putAll(oldPayload.getAnnotations());
		}
	}
	
	/**
     * Takes annotations from one ASTNode (if any) and adds them to another
     * ASTNode.
     * 
     * NOTE: duplicate method for IElement
     * 
     * @param oldA old ASTNode to take annotations from
     * @param newA new ASTNode to add annotations to
     */
    public static void mergeAnnotations(ASTNode oldA, ASTNode newA) {
        IPayload oldPayload = oldA.getPayload();
        if (oldPayload.hasAnnotation()) {
            newA.getPayload().getAnnotations().putAll(oldPayload.getAnnotations());
        }
    }
}
