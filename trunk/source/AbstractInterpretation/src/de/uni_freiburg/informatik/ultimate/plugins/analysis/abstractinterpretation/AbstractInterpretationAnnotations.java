/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation;

import java.util.HashMap;
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
	
	private Map<String, AbstractState> m_states = null;
	
	public Map<String, AbstractState> getStates() { return m_states; }
	public void setStates(Map<String, AbstractState> states) { m_states = states; }
	
	public AbstractInterpretationAnnotations(List<AbstractState> states) {
		if ((states == null) || (states.size() <= 0)) return;
		
		Map<String, AbstractState> statesMap = new HashMap<String, AbstractState>();
		
		for (int i = 0; i < states.size(); i++)
			statesMap.put(String.format("Abstract state %d", i), states.get(i));
		
		setStates(statesMap);
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
			if (m_states == null) return null;
			Map<String, Map<String, Map<String, IAbstractValue<?>>>> values =
				new HashMap<String, Map<String, Map<String, IAbstractValue<?>>>>(m_states.size());
			for (String stateKey : m_states.keySet()) {
				AbstractState state = m_states.get(stateKey);
				if (state != null) {
					List<Map<String, IAbstractValue<?>>> layer = state.getValues();
					Map<String, Map<String, IAbstractValue<?>>> layerMap =
							new HashMap<String, Map<String, IAbstractValue<?>>>(layer.size());
					for (int j = 0; j < layer.size(); j++)
						layerMap.put(String.format("Scope level %d", j), layer.get(j));
					values.put(stateKey, layerMap);
				}
			}
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
