package de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.annot;

import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.annotation.AbstractAnnotations;

/**
 * When the RCFG is used as a Büchi program, use this Annotation to mark all
 * elements that had to be added during the product construction (helps with
 * backtranslation and result generation).
 * 
 * @author dietsch@informatik.uni-freiburg.de
 * @deprecated Was an experiment, will be removed 
 */
public class BuchiProgramNeverClaimElementsAnnotation extends AbstractAnnotations {

	private static final long serialVersionUID = 1L;
	private static final String sKey = BuchiProgramNeverClaimElementsAnnotation.class.getSimpleName();
	private static final String[] sFieldNames = new String[] { "BelongsToNeverClaim" };
	private static final Object[] sFieldValues = new Object[] { true };

	@Override
	protected String[] getFieldNames() {
		return sFieldNames;
	}

	@Override
	protected Object getFieldValue(String field) {
		return sFieldValues;
	}

	public void annotate(IElement elem) {
		elem.getPayload().getAnnotations().put(sKey, this);
	}

	public static BuchiProgramNeverClaimElementsAnnotation getAnnotation(IElement elem) {
		if (!elem.hasPayload()) {
			return null;
		}
		if (!elem.getPayload().hasAnnotation()) {
			return null;
		}
		return (BuchiProgramNeverClaimElementsAnnotation) elem.getPayload().getAnnotations().get(sKey);
	}

}
