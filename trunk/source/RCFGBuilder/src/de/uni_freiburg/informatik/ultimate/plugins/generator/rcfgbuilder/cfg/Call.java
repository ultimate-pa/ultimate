package de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.model.boogie.ast.CallStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.output.BoogieStatementPrettyPrinter;

/**
 * Edge in a recursive control flow graph that represents a procedure call.
 * Opposed to a Summary this represents only the execution from the position
 * directly before the call statement to the initial position of the called
 * procedure. A Call object provides two auxiliary TransitionFormulas
 * m_OldVarsAssignment and m_GlobalVarsAssignment which are used for computing
 * nested interpolants. Let g_1,...,g_n be the global variables modified by the
 * called procedure, then m_OldVarsAssignment represents the update old(g_1),
 * ... old(g_n):=g_1,...,g_n and m_GlobalVarsAssignment represents the update
 * g_1,...,g_n:=old(g_1), ... old(g_n)
 * 
 * @author heizmann@informatik.uni-freiburg.de
 */
public class Call extends CodeBlock {

	private static final long serialVersionUID = 5047439633229508126L;

	protected CallStatement m_CallStatement;
	protected String m_PrettyPrintedStatements;

	/**
	 * The published attributes. Update this and getFieldValue() if you add new
	 * attributes.
	 */
	private final static String[] s_AttribFields = { "CallStatement", "PrettyPrintedStatements", "TransitionFormula",
			"OccurenceInCounterexamples" };

	public Call(ProgramPoint source, ProgramPoint target, CallStatement st, Logger logger) {
		super(source, target, logger);
		m_CallStatement = st;
		m_PrettyPrintedStatements = BoogieStatementPrettyPrinter.print(st);
		updatePayloadName();
	}

	@Override
	public CodeBlock getCopy(ProgramPoint source, ProgramPoint target) {
		CodeBlock copy;
		copy = new Call(source, target, m_CallStatement, mLogger);
		copy.setTransitionFormula(getTransitionFormula());
		return copy;
	}

	@Override
	public void updatePayloadName() {
		super.getPayload().setName(BoogieStatementPrettyPrinter.print(m_CallStatement));
	}

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

	public CallStatement getCallStatement() {
		return m_CallStatement;
	}

	public String getPrettyPrintedStatements() {
		return m_PrettyPrintedStatements;
	}

	@Override
	public String toString() {
		return BoogieStatementPrettyPrinter.print(m_CallStatement);
	}

}
