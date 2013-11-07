package de.uni_freiburg.informatik.ultimate.BuchiProgramProduct;

import de.uni_freiburg.informatik.ultimate.model.AbstractAnnotations;
import de.uni_freiburg.informatik.ultimate.model.annotations.Overapprox;

/**
 * When the RCFG is used as a Büchi program, use this Annotation
 * to mark accepting Locations.
 * 
 * 
 * @author Langenfeld
 *
 */

public class AcceptingNodeAnnotation extends AbstractAnnotations {
	
	@Override
	protected String[] getFieldNames() {
		// TODO Auto-generated method stub
		return new String[]{"accepting"};
	}

	@Override
	protected Object getFieldValue(String field) {
		// TODO Auto-generated method stub
		return new Object[]{true};
	}

}
