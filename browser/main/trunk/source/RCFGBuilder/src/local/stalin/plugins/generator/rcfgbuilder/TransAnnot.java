package local.stalin.plugins.generator.rcfgbuilder;


import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import local.stalin.model.AbstractAnnotations;
import local.stalin.model.boogie.ast.Statement;

public class TransAnnot extends AbstractAnnotations {

	/**
	 * Defines the behaviour of an TransitionEdge in a control flow graph.
	 * The effect of the TransitionEdge is defined by the List of Statements 
	 * m_Statements.
	 * m_PrettyPrintedStatements is a List of these Statements represented as
	 * pretty printed Strings.
	 * m_Origin stores the origin of this InternalEdge, which could be either be
	 * the ensures specification, the requires specification or the
	 * implementation of a program.
	 * m_TransitionFormula stores a TransitionFormula that describes the effect
	 * of this InternalEdge. This TransitionFormula should be derived from
	 * m_Statements.
	 * 
	 * @author heizmann@informatik.uni-freiburg.de
	 */
	private static final long serialVersionUID = -1780068525981157749L;
	
	public static enum Origin { ENSURES, REQUIRES, IMPLEMENTATION, ASSERT };

	List<Statement> m_Statements;
	List<String> m_PrettyPrintedStatements;
	TransFormula m_TransitionFormula;
	Origin m_Origin;
	int m_OccurenceInCounterexamples = 0;
	
	/**
	 * The published attributes.  Update this and getFieldValue()
	 * if you add new attributes.
	 */
	private final static String[] s_AttribFields = {
		"Statements", "PrettyPrintedStatements", "TransitionFormula",
		"OccurenceInCounterexamples"
	};
	
	public TransAnnot() {
		m_Origin = Origin.IMPLEMENTATION;
	}
	
	public TransAnnot(Origin origin) {
		m_Origin = origin;
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
		if (RCFGBuilderObserver.MULTIPLE_STATEMENTS_PER_TRANSITION) {
			if (m_Statements == null) {
				m_Statements = new ArrayList<Statement>();
				m_PrettyPrintedStatements = new ArrayList<String>();
			}
			m_Statements.add(st);
			m_PrettyPrintedStatements.add(BoogieStatementPrettyPrinter.print(st));
		}
		else {
			m_Statements = Collections.singletonList(st);
			m_PrettyPrintedStatements = Collections.singletonList(
										BoogieStatementPrettyPrinter.print(st));
		}
	}
	
	public List<Statement> getStatements() {
		return m_Statements;
	}

	public TransFormula getTransitionFormula() {
		return m_TransitionFormula;
	}

	public void setTransitionFormula(TransFormula transFormula) {
		m_TransitionFormula = transFormula;
	}

	public List<String> getPrettyPrintedStatements() {
		return m_PrettyPrintedStatements;
	}
	
	
	public Origin getOrigin() {
		return m_Origin;
	}

	public int getOccurenceInCounterexamples() {
		return m_OccurenceInCounterexamples;
	}

	public void reportOccurenceInCounterexample() {
		m_OccurenceInCounterexamples++;
	}
	
	@Override
	public String toString() {
		return m_PrettyPrintedStatements.toString();
	}
	
	

}
