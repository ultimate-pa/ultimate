package de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.model.boogie.ast.CallStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.output.BoogiePrettyPrinter;

/**
 * Edge in a recursive control flow graph that represents the call of a
 * procedure, including execution of the procedure, returning to the caller and
 * update of the left hand side of a call statement.
 * 
 * @author heizmann@informatik.uni-freiburg.de
 * 
 */
public class Summary extends CodeBlock {

	/**
	 * 
	 */
	private static final long serialVersionUID = 6048827510357561291L;

	private final CallStatement m_CallStatement;
	private final String m_PrettyPrintedStatements;
	private final boolean m_CalledProcedureHasImplementation;

	/**
	 * The published attributes. Update this and getFieldValue() if you add new
	 * attributes.
	 */
	private final static String[] s_AttribFields = { "CallStatement", "PrettyPrintedStatements", "TransitionFormula",
			"OccurenceInCounterexamples" };

	@Override
	protected String[] getFieldNames() {
		return s_AttribFields;
	}

	@Override
	protected Object getFieldValue(String field) {
		if (field == "CallStatement") {
			return m_CallStatement;
		} else if (field == "PrettyPrintedStatements") {
			return m_PrettyPrintedStatements;
		} else {
			return super.getFieldValue(field);
		}
	}

	public Summary(ProgramPoint source, ProgramPoint target, CallStatement st,
			boolean calledProcedureHasImplementation, Logger logger) {
		super(source, target, logger);
		m_CallStatement = st;
		m_CalledProcedureHasImplementation = calledProcedureHasImplementation;
		m_PrettyPrintedStatements = BoogiePrettyPrinter.print(st);
		updatePayloadName();
	}

	@Override
	public CodeBlock getCopy(ProgramPoint source, ProgramPoint target) {
		CodeBlock copy;
		copy = new Summary(source, target, m_CallStatement, m_CalledProcedureHasImplementation, mLogger);
		copy.setTransitionFormula(getTransitionFormula());
		return copy;
	}

	@Override
	public void updatePayloadName() {
		super.getPayload().setName("summary");
	}

	public boolean calledProcedureHasImplementation() {
		return m_CalledProcedureHasImplementation;
	}

	public CallStatement getCallStatement() {
		return m_CallStatement;
	}

	public String getPrettyPrintedStatements() {
		return m_PrettyPrintedStatements;
	}

	@Override
	public String toString() {
		return "SUMMARY";
	}

}
