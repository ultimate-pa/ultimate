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
		setType(Integer.class);
		value = val;
	}
	
	public ConstantExpression(String val) {
		setType(String.class);
		this.value = val;
	}
	
	public ConstantExpression(boolean val) {
		setType(Boolean.class);
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
		if (value instanceof String) {
			return "\"" + value.toString() + "\"";
		}
		return value.toString();
	}
	
	

}
