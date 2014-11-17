package de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST;


import de.uni_freiburg.informatik.ultimate.model.location.ILocation;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AtsASTNode;

public class AutomataTestFileAST extends AtsASTNode {

	
	private static final long serialVersionUID = 8118811454684637616L;
	
	private AutomataDefinitionsAST m_automataDefinitions;
	

	private AtsASTNode m_statementList;

	public AutomataTestFileAST (ILocation loc, AtsASTNode stmtList, AutomataDefinitionsAST autDefs) {
		super(loc);
		m_automataDefinitions = autDefs;
		m_statementList = stmtList;
	}

	public AutomataDefinitionsAST getAutomataDefinitions() {
		return m_automataDefinitions;
	}

	public void setAutomataDefinitions(AutomataDefinitionsAST m_automataDefinitions) {
		this.m_automataDefinitions = m_automataDefinitions;
	}
	
	public AtsASTNode getStatementList() {
		return m_statementList;
	}

	
	
	
	

}
