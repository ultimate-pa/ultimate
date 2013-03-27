package de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST;


import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AtsASTNode;

/**
 * @author musab@informatik.uni-freiburg.de
 */
public class ConstantExpression extends AtsASTNode {
	/**
	 * 
	 */
	private static final long serialVersionUID = 9065975410268575852L;
	private Object value;
	
	public ConstantExpression(Integer val) {
		m_returnType = Integer.class;
		value = val;
	}
	
	public ConstantExpression(String val) {
		m_returnType = String.class;
		this.value = val;
	}
	
	public ConstantExpression(boolean val) {
		m_returnType = Boolean.class;
		value = val;
	}
	public Object getValue() {
		return value;
	}

	@Override
	public String toString() {
		return "ConstantExpression [Value : " + value + "]";
	}

	@Override
	public String getAsString() {
		return value.toString();
	}
	
	

}
