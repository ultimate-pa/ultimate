package de.uni_freiburg.informatik.ultimate.model.annotations;

import java.util.Arrays;

import de.uni_freiburg.informatik.ultimate.model.AbstractAnnotations;
import de.uni_freiburg.informatik.ultimate.result.Check;

/**
 * Annotation for transition (e.g., CodeBlock) that indicates that it was not
 * build by a semantics preserving translation but by an overapproximation.
 * This allows model checkers to report <i>unknown</i> instead of <i>unsafe</i>
 * for traces that contain elements with this annotation.
 */
public class Overapprox extends AbstractAnnotations {
	
	public static final String BITVEC = "bitvector operation";
	public static final String FUNC_POINTER = "call of function pointer";
	
	private final String[] m_Reasons;
	
	public Overapprox(String... resons) {
		m_Reasons = resons;
	}

	public static final String getIdentifier() {
		return Check.class.getName();
	}
	
	private static final long serialVersionUID = -575969312624287029L;

	/**
	 * The published attributes.  Update this and getFieldValue()
	 * if you add new attributes.
	 */
	private final static String[] s_AttribFields = {
		"Reason for overapproximation"
	};
	
	@Override
	protected String[] getFieldNames() {
		return s_AttribFields;
	}

	@Override
	protected Object getFieldValue(String field) {
		if (field == "Reason for overapproximation")
			return Arrays.toString(m_Reasons);
		else
			throw new UnsupportedOperationException("Unknown field "+field);
	}

}
