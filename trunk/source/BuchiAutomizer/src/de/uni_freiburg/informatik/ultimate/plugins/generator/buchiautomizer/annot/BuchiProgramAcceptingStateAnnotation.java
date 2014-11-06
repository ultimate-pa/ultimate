package de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.annot;

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

	@Override
	protected String[] getFieldNames() {
		return new String[] { "accepting" };
	}

	@Override
	protected Object getFieldValue(String field) {
		return new Object[] { true };
	}

}
