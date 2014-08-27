package de.uni_freiburg.informatik.ultimate.result;

/**
 * Objects of this class are used to report the overall result of a termination
 * analysis. Do not use this for synthesis of termination arguments.
 * (I do not know if Severity.ERROR is a good choice for NONTERMINATION and
 * UNKNOWN.)
 * @author heizmann@informatik.uni-freiburg.de
 *
 */
public class TerminationAnalysisResult extends AbstractResult implements
		IResultWithSeverity {
	
	private final TERMINATION m_Termination;
	private final String m_LongDescription;
	
	public TerminationAnalysisResult(String plugin, TERMINATION termination,
			String longDescription) {
		super(plugin);
		m_Termination = termination;
		m_LongDescription = longDescription;
	}
	

	public TERMINATION getTermination() {
		return m_Termination;
	}

	public enum TERMINATION {
		TERMINATING,
		NONTERMINATING,
		UNKNOWN
	}

	@Override
	public String getShortDescription() {
		final String shortDescription;
		switch (m_Termination) {
		case NONTERMINATING:
			shortDescription = "Nontermination possible";
			break;
		case TERMINATING:
			shortDescription = "Termination proven";
			break;
		case UNKNOWN:
			shortDescription = "Unable to decide termination";
			break;
		default:
			throw new AssertionError();
		}
		return shortDescription;
	}

	@Override
	public String getLongDescription() {
		return m_LongDescription;
	}

	@Override
	public Severity getSeverity() {
		Severity severity;
		switch (m_Termination) {
		case NONTERMINATING:
			severity = Severity.ERROR;
			break;
		case TERMINATING:
			severity = Severity.INFO;
			break;
		case UNKNOWN:
			severity = Severity.ERROR;
			break;
		default:
			throw new AssertionError();
		}
		return severity;
	}

}
