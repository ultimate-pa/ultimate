package de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST;


import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AtsASTNode;

public class AutomataTestFile extends AtsASTNode {

	
	private static final long serialVersionUID = 8118811454684637616L;
	
	private AutomataDefinitions m_automataDefinitions;
	

	private AtsASTNode m_statementList;

	public AutomataTestFile (AtsASTNode stmtList, AutomataDefinitions autDefs) {
		m_automataDefinitions = autDefs;
		m_statementList = stmtList;
	}

	public AutomataDefinitions getAutomataDefinitions() {
		return m_automataDefinitions;
	}

	public void setAutomataDefinitions(AutomataDefinitions m_automataDefinitions) {
		this.m_automataDefinitions = m_automataDefinitions;
	}
	
	public AtsASTNode getStatementList() {
		return m_statementList;
	}

	
	
	
	

}
