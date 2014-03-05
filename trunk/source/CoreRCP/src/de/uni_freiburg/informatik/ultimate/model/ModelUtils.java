package de.uni_freiburg.informatik.ultimate.model;

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
	 * @param oldE
	 *            old IElement to take annotations from
	 * @param newE
	 *            new IElement to add annotations to
	 */
	public static void mergeAnnotations(IElement oldE, IElement newE) {
		if (oldE == null || newE == null) {
			return;
		}
		if (!oldE.hasPayload()) {
			return;
		}
		IPayload oldPayload = oldE.getPayload();
		if (oldPayload.hasAnnotation()) {
			newE.getPayload().getAnnotations().putAll(oldPayload.getAnnotations());
		}
	}
}
