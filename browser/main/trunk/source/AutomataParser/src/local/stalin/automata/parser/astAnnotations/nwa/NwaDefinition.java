package local.stalin.automata.parser.astAnnotations.nwa;
import java.util.ArrayList;

import local.stalin.model.AbstractAnnotations;


public class NwaDefinition extends AbstractAnnotations {

	private static final long serialVersionUID = -2644386589944130013L;
	private final String name;
	private final ArrayList<String> callAlphabet;
	private final ArrayList<String> internalAlphabet;
	private final ArrayList<String> returnAlphabet;
	private final ArrayList<String> states;
	private final ArrayList<String> initialStates;
	private final ArrayList<String> finalStates;
	
	/**
	 * The published attributes.  Update this and getFieldValue()
	 * if you add new attributes.
	 */
	private final static String[] s_AttribFields = {
		"name", "callAlphabet", "internalAlphabet", "returnAlphabet", "states",
		"initialStates", "finalStates"
	};
	


	public NwaDefinition(String name, ArrayList<String> callAlphabet,
			ArrayList<String> internalAlphabet,
			ArrayList<String> returnAlphabet, ArrayList<String> states,
			ArrayList<String> initialStates, ArrayList<String> finalStates) {
		this.name = name;
		this.callAlphabet = callAlphabet;
		this.internalAlphabet = internalAlphabet;
		this.returnAlphabet = returnAlphabet;
		this.states = states;
		this.initialStates = initialStates;
		this.finalStates = finalStates;
	}

	@Override
	protected String[] getFieldNames() {
		return s_AttribFields;
	}

	@Override
	protected Object getFieldValue(String field) {
		if (field == "name")
			return name;
		else if (field == "internalAlphabet")
			return internalAlphabet;
		else if (field == "callAlphabet")
			return callAlphabet;
		else if (field == "returnAlphabet")
			return returnAlphabet;
		else if (field == "states")
			return states;
		else if (field == "initialStates")
			return initialStates;
		else if (field == "finalStates")
			return finalStates;
		else
			throw new UnsupportedOperationException("Unknown field "+field);
	}

	/**
	 * @return the name
	 */
	public String getName() {
		return name;
	}

	/**
	 * @return the callAlphabet
	 */
	public ArrayList<String> getCallAlphabet() {
		return callAlphabet;
	}

	/**
	 * @return the internalAlphabet
	 */
	public ArrayList<String> getInternalAlphabet() {
		return internalAlphabet;
	}

	/**
	 * @return the returnAlphabet
	 */
	public ArrayList<String> getReturnAlphabet() {
		return returnAlphabet;
	}

	/**
	 * @return the states
	 */
	public ArrayList<String> getStates() {
		return states;
	}

	/**
	 * @return the initialStates
	 */
	public ArrayList<String> getInitialStates() {
		return initialStates;
	}

	/**
	 * @return the finalStates
	 */
	public ArrayList<String> getFinalStates() {
		return finalStates;
	}
	
	

}
