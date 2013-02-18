package local.stalin.logic;

public class QuantifiedFormula extends Formula {
	private static final long serialVersionUID = -1501423623752265526L;
	public static final int EXISTS = 0;
	public static final int FORALL = 1;
	private static final String[] quantifierName = { "exists", "forall" };
	
	private int quantifier;
	private TermVariable[] variables;
	private Formula subformula;
	private SMTLibBase[][] triggers;
	
	QuantifiedFormula(int quant, TermVariable[] vars, Formula f, SMTLibBase[][] triggers) {
		this.quantifier = quant;
		this.variables = vars;
		if (vars.length == 0)
			throw new IllegalArgumentException("Quantifier without variables");
		this.subformula = f;
		this.triggers = triggers;
	}
	
	public boolean typeCheck() {
		return subformula.typeCheck();
	}
	
	/**
	 * @return the quantifier
	 */
	public int getQuantifier() {
		return quantifier;
	}

	/**
	 * @return the variables
	 */
	public TermVariable[] getVariables() {
		return variables;
	}

	/**
	 * @return the subformula
	 */
	public Formula getSubformula() {
		return subformula;
	}

	/**
	 * @return the triggers
	 */
	public SMTLibBase[][] getTriggers() {
		return triggers;
	}

	public String toString() {
		StringBuilder sb = new StringBuilder();
		sb.append('(').append(quantifierName[quantifier]);
		for (TermVariable v: variables) {
			sb.append(" (?").append(v.getName()).append(' ').append(v.getSort()).append(')');
		}
		sb.append(' ');
		sb.append(subformula);
		if (triggers != null) {
			for (SMTLibBase[] trig : triggers) {
				sb.append(" :pat { ");
				for (SMTLibBase term : trig) {
					sb.append(term).append(' ');
				}
				sb.append('}');
			}
		}
		sb.append(getStringOfAnnotations());
		sb.append(')');
		return sb.toString();
	}
}
