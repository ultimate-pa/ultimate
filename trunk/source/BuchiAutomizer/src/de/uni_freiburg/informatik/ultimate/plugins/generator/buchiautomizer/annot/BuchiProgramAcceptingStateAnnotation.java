package de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.annot;

import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.annotation.AbstractAnnotations;

/**
 * When the RCFG is used as a Büchi program, use this Annotation to mark
 * accepting Locations.
 * 
 * 
 * @author Langenfeld
 * 
 */

public class BuchiProgramAcceptingStateAnnotation extends AbstractAnnotations {

	private static final long serialVersionUID = 1L;
	private static final String sKey = BuchiProgramAcceptingStateAnnotation.class.getSimpleName();

	@Override
	protected String[] getFieldNames() {
		return new String[] { "IsAcceptingState" };
	}

	@Override
	protected Object getFieldValue(String field) {
		return new Object[] { true };
	}
	
	public void annotate(IElement elem) {
		elem.getPayload().getAnnotations().put(sKey, this);
	}

	public static BuchiProgramAcceptingStateAnnotation getAnnotation(IElement elem) {
		if (!elem.hasPayload()) {
			return null;
		}
		if (!elem.getPayload().hasAnnotation()) {
			return null;
		}
		return (BuchiProgramAcceptingStateAnnotation) elem.getPayload().getAnnotations().get(sKey);
	}

}
