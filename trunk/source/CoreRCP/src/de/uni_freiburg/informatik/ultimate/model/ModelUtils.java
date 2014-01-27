package de.uni_freiburg.informatik.ultimate.model;

import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BoogieASTNode;

/**
 * Helper methods for Ultimate models.
 */
public final class ModelUtils {
	/**
	 * Takes annotations from one IElement (if any) and adds them to another
	 * IElement.
	 * 
	 * NOTE: duplicate method for BoogieASTNode
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
     * Takes annotations from one BoogieASTNode (if any) and adds them to another
     * BoogieASTNode.
     * 
     * NOTE: duplicate method for IElement
     * 
     * @param oldA old BoogieASTNode to take annotations from
     * @param newA new BoogieASTNode to add annotations to
     */
    public static void mergeAnnotations(BoogieASTNode oldA, BoogieASTNode newA) {
        IPayload oldPayload = oldA.getPayload();
        if (oldPayload.hasAnnotation()) {
            newA.getPayload().getAnnotations().putAll(oldPayload.getAnnotations());
        }
    }
}
