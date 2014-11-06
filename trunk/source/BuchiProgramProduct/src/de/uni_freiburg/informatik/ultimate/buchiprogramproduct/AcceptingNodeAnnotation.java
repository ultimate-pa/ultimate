package de.uni_freiburg.informatik.ultimate.buchiprogramproduct;

import de.uni_freiburg.informatik.ultimate.model.annotation.AbstractAnnotations;

/**
 * When the RCFG is used as a Büchi program, use this Annotation to mark
 * accepting Locations.
 * 
 * 
 * @author Langenfeld
 * 
 */

public class AcceptingNodeAnnotation extends AbstractAnnotations {

	private static final long serialVersionUID = 1L;

	@Override
	protected String[] getFieldNames() {
		// TODO Auto-generated method stub
		return new String[] { "accepting" };
	}

	@Override
	protected Object getFieldValue(String field) {
		// TODO Auto-generated method stub
		return new Object[] { true };
	}

}
