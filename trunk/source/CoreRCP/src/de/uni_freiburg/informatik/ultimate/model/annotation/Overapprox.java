package de.uni_freiburg.informatik.ultimate.model.annotation;

import java.util.Collections;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.model.location.ILocation;

/**
 * Annotation for transition (e.g., CodeBlock) that indicates that it was not
 * build by a semantics preserving translation but by an overapproximation.
 * This allows model checkers to report <i>unknown</i> instead of <i>unsafe</i>
 * for traces that contain elements with this annotation.
 */
public class Overapprox extends AbstractAnnotations {
	
	public static final String s_REASON_FOR_OVERAPPROXIMATION = "Reason for overapproximation";
	public static final String s_LOCATION_MAPPING = "Location mapping";
	
	public static final String BITVEC = "bitvector operation";
	public static final String FUNC_POINTER = "call of function pointer";
	
	
	public static final String getIdentifier() {
		return Overapprox.class.getName();
	}
	
	private final Map<String, ILocation> m_Reason2Loc;
	
	public Overapprox(Map<String, ILocation> reason2Loc) {
		m_Reason2Loc = reason2Loc;
	}
	
	public Overapprox(String reason, ILocation loc) {
        m_Reason2Loc = Collections.singletonMap(reason, loc);
    }

	private static final long serialVersionUID = -575969312624287029L;

	/**
	 * The published attributes.  Update this and getFieldValue()
	 * if you add new attributes.
	 */
	private final static String[] s_AttribFields = {
		s_REASON_FOR_OVERAPPROXIMATION, s_LOCATION_MAPPING
	};
	
	@Override
	protected String[] getFieldNames() {
		return s_AttribFields;
	}

	@Override
	protected Object getFieldValue(String field) {
		if (field.equals(s_REASON_FOR_OVERAPPROXIMATION))
			return m_Reason2Loc.keySet();
		else if (field.equals(s_LOCATION_MAPPING))
			return m_Reason2Loc;
		else
			throw new UnsupportedOperationException("Unknown field "+field);
	}

}
