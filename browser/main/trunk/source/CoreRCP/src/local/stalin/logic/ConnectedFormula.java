package local.stalin.logic;

public class ConnectedFormula extends Formula {
	private static final long serialVersionUID = 2850688636831678558L;
	// TODO: Sync with nativez3 code
	public static final int OR = 0;
	public static final int AND = 1;
	public static final int IMPLIES = 2;
	public static final int IFF = 3;
	public static final int XOR = 4;
	public static final int OEQ = 5;// Binary equality modulo naming
	private static final String[] connectorName = {
		"or", "and", "implies", "iff", "xor", "oeq"
	};
	
	private Formula lhs, rhs;
	private int connector;
	
	ConnectedFormula(int op, Formula f, Formula g) {
		connector = op;
		lhs = f;
		rhs = g;
	}
	
	/**
	 * @return the lhs
	 */
	public Formula getLhs() {
		return lhs;
	}

	/**
	 * @return the rhs
	 */
	public Formula getRhs() {
		return rhs;
	}

	/**
	 * @return the connector
	 */
	public int getConnector() {
		return connector;
	}

	/**
	 * @return string representation of connector
	 */
	public String getConnectorName() {
		return connectorName[connector];
	}

	public boolean typeCheck() {
		return lhs.typeCheck() && rhs.typeCheck();
	}
	
	public String toString() {
		StringBuilder sb = new StringBuilder();
		sb.append("(").append(connectorName[connector]);
		ConnectedFormula f = this;
		while (connector != IMPLIES && f.rhs instanceof ConnectedFormula
				&& f.rhs.getStringOfAnnotations() == ""
				&& ((ConnectedFormula)f.rhs).connector == connector) {
			sb.append(" ").append(f.lhs);
			f = (ConnectedFormula) f.rhs;
		}
		sb.append(" ").append(f.lhs);
		sb.append(" ").append(f.rhs);
		sb.append(getStringOfAnnotations());
		sb.append(")");
		return sb.toString();
	}
}
