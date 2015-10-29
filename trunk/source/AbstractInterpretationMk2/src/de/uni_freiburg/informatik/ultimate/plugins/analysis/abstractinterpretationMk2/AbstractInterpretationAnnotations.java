package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.annotation.AbstractAnnotations;

/**
 * @author Christopher Dillo
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
@SuppressWarnings("rawtypes")
public class AbstractInterpretationAnnotations extends AbstractAnnotations {

	private static final long serialVersionUID = 1L;

	private static final String ANNOTATION_NAME = "Abstract Interpretation";
	private static final String FIELD_NAME_STATES = "Abstract states";

	private final List<StackState> mStates;

	public AbstractInterpretationAnnotations(List<StackState> states) {
		mStates = states;
	}

	@Override
	protected String[] getFieldNames() {
		return new String[] { FIELD_NAME_STATES };
	}

	@Override
	protected Object getFieldValue(final String field) {
		switch (field) {
		case FIELD_NAME_STATES:
			return mStates;
		default:
			throw new UnsupportedOperationException("Field " + field + " unknown");
		}
	}

	/**
	 * Annotate a given IElement with this annotation object
	 * 
	 * @param element
	 *            The IElement object this annotation shall be added to
	 */
	public void annotate(IElement element) {
		element.getPayload().getAnnotations().put(ANNOTATION_NAME, this);
	}

	/**
	 * Checks the given IElement for an AbstractInterpretationAnnotation and
	 * returns it
	 * 
	 * @param element
	 *            The element whose Annotation is to be retrieved
	 * @return An AbstractInterpretationAnnotation on the IElement or null if
	 *         none is present
	 */
	public static AbstractInterpretationAnnotations getAnnotation(IElement element) {
		if (!element.hasPayload()) {
			return null;
		}
		if (!element.getPayload().hasAnnotation()) {
			return null;
		}
		return (AbstractInterpretationAnnotations) element.getPayload().getAnnotations().get(ANNOTATION_NAME);
	}

	@Override
	public String toString() {
		return "Abstract Interpretation";
	}

}
