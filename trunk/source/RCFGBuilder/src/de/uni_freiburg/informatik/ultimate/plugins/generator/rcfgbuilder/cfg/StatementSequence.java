package de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg;


import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.model.boogie.ast.AssignmentStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.HavocStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.model.boogie.output.BoogieStatementPrettyPrinter;

/**
 * Edge in a recursive control flow graph that represents a sequence of 
 * statements which are executed one after the other if this edge is executed.
 * The name of this objects Payload is
 * <ul>
 * <li>a prettyprinted representation of the Statements, if the origin of this
 *  edge is the implementation,</li>
 * <li>"Assert" if origin of this edge is an AssertStatement,</li>
 * <li>"Requires" if origin of this edge is the requires specification,</li>
 * <li>"Ensures" if origin of this edge is the ensures specification.</li>
 * </ul>
 * @author heizmann@informatik.uni-freiburg.de
 */
public class StatementSequence extends CodeBlock {

	private static final long serialVersionUID = -1780068525981157749L;
	
	public static enum Origin { ENSURES, REQUIRES, IMPLEMENTATION, ASSERT };
	

	List<Statement> m_Statements;
	String m_PrettyPrintedStatements;
	/**
	 * m_Origin stores the origin of this InternalEdge, which could be either be
	 * the ensures specification, the requires specification or the
	 * implementation of a program.
	 */
	Origin m_Origin;
	
	/**
	 * The published attributes.  Update this and getFieldValue()
	 * if you add new attributes.
	 */
	private final static String[] s_AttribFields = {
		"Statements", "PrettyPrintedStatements", "TransitionFormula",
		"OccurenceInCounterexamples"
	};
	
	public StatementSequence(ProgramPoint source, ProgramPoint target, 
			Statement st) {
		super(source, target);
		m_Origin = Origin.IMPLEMENTATION;
		this.addStatement(st);
		updatePayloadName();
	}
	
	public StatementSequence(ProgramPoint source, ProgramPoint target,
			Statement st, Origin origin) {
		super(source, target);
		m_Origin = origin;
		this.addStatement(st);
		updatePayloadName();
	}
	
	public StatementSequence(ProgramPoint source, ProgramPoint target,
			List<Statement> stmts, Origin origin) {
		super(source, target);
		m_Statements = stmts;
		m_Origin = origin;
		m_PrettyPrintedStatements = "";
		for (Statement st : stmts) {
			m_PrettyPrintedStatements += BoogieStatementPrettyPrinter.print(st);
		}
		updatePayloadName();
	}
	
	
	@Override
	public CodeBlock getCopy(ProgramPoint source, ProgramPoint target) {
		CodeBlock copy;
		copy = new StatementSequence(source, target, m_Statements, m_Origin);
		copy.setTransitionFormula(getTransitionFormula());
		return copy;
	}
	

	@Override
	protected String[] getFieldNames() {
		return s_AttribFields;
	}

	@Override
	protected Object getFieldValue(String field) {
		if (field == "Statements") {
			return m_Statements;
		}
		else if (field == "PrettyPrintedStatements") {
			return m_PrettyPrintedStatements;
		}
		else if (field == "TransitionFormula") {
			return m_TransitionFormula;
		}
		else if (field == "OccurenceInCounterexamples") {
			return m_OccurenceInCounterexamples;
		}
		else {
			throw new UnsupportedOperationException("Unknown field "+field);
		}
	}
	
	public void addStatement(Statement st) {
		if ( st instanceof AssumeStatement
				|| st instanceof AssignmentStatement
				|| st instanceof HavocStatement ) {
		}
		else {
			throw new IllegalArgumentException("Only Assignment, Assume and" +
					" HavocStatement allowed in InternalEdge.");
		}
		if (m_Statements == null) {
			m_Statements = new ArrayList<Statement>();
			m_PrettyPrintedStatements = "";
		}
		m_Statements.add(st);
		m_PrettyPrintedStatements += BoogieStatementPrettyPrinter.print(st);
	}
	
	public List<Statement> getStatements() {
		return m_Statements;
	}

	public String getPrettyPrintedStatements() {
		return m_PrettyPrintedStatements;
	}
	
	public Origin getOrigin() {
		return m_Origin;
	}

	

}
