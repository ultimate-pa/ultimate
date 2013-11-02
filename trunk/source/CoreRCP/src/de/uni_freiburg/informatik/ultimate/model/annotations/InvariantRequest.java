package de.uni_freiburg.informatik.ultimate.model.annotations;

import java.util.Arrays;

import de.uni_freiburg.informatik.ultimate.model.AbstractAnnotations;
import de.uni_freiburg.informatik.ultimate.result.Check;

/**
 * Annotation that indicates that model checkers should infer an invariant
 * for the annotated node.
 */
public class InvariantRequest extends AbstractAnnotations {
	
	public static final String getIdentifier() {
		return InvariantRequest.class.getName();
	}
	
	public static final String LOOPENTRY = "loop entry";
	
	private final String[] m_Reasons;
	
	public InvariantRequest(String... resons) {
		m_Reasons = resons;
	}

	private static final long serialVersionUID = -575969312624287029L;

	/**
	 * The published attributes.  Update this and getFieldValue()
	 * if you add new attributes.
	 */
	private final static String[] s_AttribFields = {
		"Reason"
	};
	
	@Override
	protected String[] getFieldNames() {
		return s_AttribFields;
	}

	@Override
	protected Object getFieldValue(String field) {
		if (field == "Reason")
			return Arrays.toString(m_Reasons);
		else
			throw new UnsupportedOperationException("Unknown field "+field);
	}

}
