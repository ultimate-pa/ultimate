package de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg;

import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;


/**
 * Edge in a recursive control flow graph that represents the return from a
 * called procedure. This represents the execution starting from the position
 * directly before the return statement (resp. the last position of a procedure
 * if there is no return statement) to the position after the corresponding
 * call statement. 
 * The update of the variables of the calling procedure is defined in the
 * TransFormula.
 * @author heizmann@informatik.uni-freiburg.de
 *
 */
public class Return extends CodeBlock {

	private static final long serialVersionUID = 3561826943033450950L;
	
	private final ProgramPoint m_CallerNode;
	private final Call m_CorrespondingCallAnnot;
	
	public Return(ProgramPoint source, ProgramPoint target,
			Call callAnnot, ProgramPoint callerNode) {
		super(source, target);
		m_CorrespondingCallAnnot = callAnnot;
		m_CallerNode = callerNode;
		updatePayloadName();
	}
	

	@Override
	public CodeBlock getCopy(ProgramPoint source, ProgramPoint target) {
		CodeBlock copy;
		copy = new Return(source, target, m_CorrespondingCallAnnot, m_CallerNode);
		copy.setTransitionFormula(getTransitionFormula());
		return copy;
	}
	
	@Override
	public void updatePayloadName() {
		super.getPayload().setName("return");
	}
	//TODO: rename
	public Call getCorrespondingCallAnnot() {
		return m_CorrespondingCallAnnot;
	}
	
	public ProgramPoint getCallerNode() {
		return m_CallerNode;
	}
	
	/**
	 * The published attributes.  Update this and getFieldValue()
	 * if you add new attributes.
	 */
	private final static String[] s_AttribFields = {
		"CallStatement", "PrettyPrintedStatements", "TransitionFormula",
		"OccurenceInCounterexamples"
	};
	

	@Override
	protected String[] getFieldNames() {
		return s_AttribFields;
	}
	
	
	@Override
	protected Object getFieldValue(String field) {
		if (field == "CallStatement") {
			return m_CorrespondingCallAnnot.getCallStatement();
		}
		else if (field == "PrettyPrintedStatements") {
			return m_CorrespondingCallAnnot.getPrettyPrintedStatements();
		}
		else {
			return super.getFieldValue(field);
		}
	}
	
	
	public String getPrettyPrintedStatements() {
		return "Return - Corresponding call: " + m_CorrespondingCallAnnot.getPrettyPrintedStatements();
	}

	public Statement getCallStatement() {
		return m_CorrespondingCallAnnot.getCallStatement();
	}

}
