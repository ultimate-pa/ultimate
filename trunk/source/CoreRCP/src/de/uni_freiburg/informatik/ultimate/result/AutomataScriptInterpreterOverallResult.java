package de.uni_freiburg.informatik.ultimate.result;


/**
 * While interpreting an automata script file such an overall result is
 * constructed.
 * @author Matthias Heizmann
 *
 */
public class AutomataScriptInterpreterOverallResult extends AbstractResult
		implements IResultWithSeverity {
	
	public enum OverallResult {
		ALL_ASSERTIONS_HOLD, 
		NO_ASSERTION, 
		SOME_ASSERTION_FAILED, 
		EXCEPTION_OR_ERROR, 
		TIMEOUT,
		OUT_OF_MEMORY
//		SYNTAX_ERROR
	}
	
	private final OverallResult m_OverallResult;
	
	public AutomataScriptInterpreterOverallResult(String plugin, OverallResult overallResult) {
		super(plugin);
		m_OverallResult = overallResult;
	}

	@Override
	public String getShortDescription() {
		switch (m_OverallResult) {
		case ALL_ASSERTIONS_HOLD:
			return "Finished interpretation of automata script.";
		case EXCEPTION_OR_ERROR:
			return "Interpretation of automata script failed.";
		case NO_ASSERTION:
			return "Finished interpretation of automata script.";
		case SOME_ASSERTION_FAILED:
			return "Some assert statements have been evaluated to false.";
//		case SYNTAX_ERROR:
		case TIMEOUT:
			return "Timeout during interpretation of automata script.";
		case OUT_OF_MEMORY:
			return "Run out of memory during interpretation of automata script.";
		default:
			throw new AssertionError("unknown case");
		}
	}

	@Override
	public String getLongDescription() {
		switch (m_OverallResult) {
		case ALL_ASSERTIONS_HOLD:
			return "All assert statements have been evaluated to true.";
		case NO_ASSERTION:
			return " You have not used any assert statement in your automata"
					+ " script. Assert statements can be used to check Boolean results.";
		default:
			return getShortDescription();
		}
	}

	@Override
	public Severity getSeverity() {
		switch (m_OverallResult) {
		case ALL_ASSERTIONS_HOLD:
			return Severity.INFO;
		case EXCEPTION_OR_ERROR:
			return Severity.ERROR;
		case NO_ASSERTION:
			return Severity.INFO;
		case SOME_ASSERTION_FAILED:
			return Severity.ERROR;
//		case SYNTAX_ERROR:
		case TIMEOUT:
			return Severity.WARNING;
		case OUT_OF_MEMORY:
			return Severity.WARNING;
		default:
			throw new AssertionError("unknown case");
		}
	}

	public OverallResult getOverallResult() {
		return m_OverallResult;
	}
	
	

}
