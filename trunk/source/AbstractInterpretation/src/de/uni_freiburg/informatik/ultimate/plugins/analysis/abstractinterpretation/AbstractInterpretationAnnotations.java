/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.annotation.AbstractAnnotations;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.AbstractState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractValue;

/**
 * @author Christopher Dillo
 *
 */
public class AbstractInterpretationAnnotations extends AbstractAnnotations {

	private static final long serialVersionUID = 1L;

	public static final String s_annotationName = "AbstractInterpretation";
	
	private List<AbstractState> m_states = null;
	
	public List<AbstractState> getStates() { return m_states; }
	public void setStates(List<AbstractState> states) { m_states = states; }
	
	public AbstractInterpretationAnnotations(List<AbstractState> states) {
		setStates(states);
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.model.annotation.AbstractAnnotations#getFieldNames()
	 */
	@Override
	protected String[] getFieldNames() {
		return new String[] { "Abstract States",  "Abstract Values" };
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.model.annotation.AbstractAnnotations#getFieldValue(java.lang.String)
	 */
	@Override
	protected Object getFieldValue(String field) {
		switch (field) {
		case "Abstract States":
			return m_states;
		case "Abstract Values":
			List<List<Map<String, IAbstractValue>>> values = new ArrayList<List<Map<String, IAbstractValue>>>(m_states.size());
			for (int i = 0; i < m_states.size(); i++)
				values.add(m_states.get(i).getValues());
			return values;
		default:
			return null;
		}
	}

	/**
	 * Annotate a given IElement with this annotation object
	 * @param element The IElement object this annotation shall be added to
	 */
	public void annotate(IElement element) {
		element.getPayload().getAnnotations().put(s_annotationName, this);
	}

	/**
	 * Checks the given IElement for an AbstractInterpretationAnnotation and returns it
	 * @param element The element whose Annotation is to be retrieved
	 * @return An AbstractInterpretationAnnotation on the IElement or null if none is present
	 */
	public static AbstractInterpretationAnnotations getAnnotation(IElement element) {
		if (!element.hasPayload()) {
			return null;
		}
		if (!element.getPayload().hasAnnotation()) {
			return null;
		}
		return (AbstractInterpretationAnnotations) element.getPayload().getAnnotations().get(s_annotationName);
	}
	
	@Override
	public String toString() {
		return "AbstractInterpretation : " + m_states.toString();
	}

}
