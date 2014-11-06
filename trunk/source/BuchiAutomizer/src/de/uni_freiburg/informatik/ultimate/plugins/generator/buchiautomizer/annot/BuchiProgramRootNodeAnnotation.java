package de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.annot;

import de.uni_freiburg.informatik.ultimate.model.annotation.AbstractAnnotations;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.BuchiAutomizer;

/**
 * When the RCFG is used as a Büchi program, use this Annotation to mark
 * the root node so {@link BuchiAutomizer} knows that it should run in LTL mode. 
 * 
 * @author dietsch@informatik.uni-freiburg.de
 */

public class BuchiProgramRootNodeAnnotation extends AbstractAnnotations {

	private static final long serialVersionUID = 1L;

	@Override
	protected String[] getFieldNames() {
		return new String[] { "UseLTLMode" };
	}

	@Override
	protected Object getFieldValue(String field) {
		return new Object[] { true };
	}

}
