/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.annotation.AbstractAnnotations;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.CallStatement;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.AbstractState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.AbstractState.ArrayData;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.AbstractState.CallStackElement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGNode;

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
		return new String[] { "Abstract states",  "Abstract values", "Traces"};
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.model.annotation.AbstractAnnotations#getFieldValue(java.lang.String)
	 */
	@Override
	protected Object getFieldValue(String field) {
		switch (field) {
		case "Abstract states" :
			return m_states;
		case "Abstract values" :
			if (m_states == null) return null;
			// state -> scope -> (value, array -> (value, has unclear indices))
			Map<String, Map<String, Object>> states =
				new HashMap<String, Map<String, Object>>(m_states.size());
			for (String stateKey : m_states.keySet()) {
				AbstractState state = m_states.get(stateKey);
				if (state != null) {
					// scope -> (value, array -> (value, has unclear indices))
					List<CallStackElement> callstack = state.getCallStack();
					Map<String, Object> callstackData = new HashMap<String, Object>(2);
					for (CallStackElement cse : callstack) {
						// array -> (value, has unclear indices)
						Map<String, Map<String, Object>> arrayInfo = new HashMap<String, Map<String, Object>>(2);
						Map<String, ArrayData> arrays = cse.getArrays();
						for (String ident : arrays.keySet()) {
							ArrayData a = arrays.get(ident);
							Map<String, Object> aInfo = new HashMap<String, Object>();
							aInfo.put("Merged value", a.getValue());
							aInfo.put("Has unclear indices", a.getIndicesUnclear());
							arrayInfo.put(ident, aInfo);
						}
						// store (value, array -> (value, has unclear indices))
						Map<String, Object> stateData = new HashMap<String, Object>();
						stateData.put("Values", cse.getValues());
						stateData.put("Arrays", arrayInfo);
						CallStatement csmt = cse.getCallStatement();
						String functionName = (csmt == null) ? "GLOBAL" : csmt.getMethodName();
						callstackData.put(String.format("%s", functionName), stateData);
					}
					states.put(stateKey, callstackData);
				}
			}
			return states;
		case "Traces" :
			if (m_states == null) return null;
			Map<String, List<String>> traces =
				new HashMap<String, List<String>>(m_states.size());
			for (String stateKey : m_states.keySet()) {
				AbstractState state = m_states.get(stateKey);
				if (state != null) {
					List<RCFGNode> passed = state.getPassedNodes();
					List<String> passedList =
							new ArrayList<String>(passed.size());
					for (RCFGNode node : passed)
						passedList.add(node.toString());
					traces.put(stateKey, passedList);
				}
			}
			return traces;
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
