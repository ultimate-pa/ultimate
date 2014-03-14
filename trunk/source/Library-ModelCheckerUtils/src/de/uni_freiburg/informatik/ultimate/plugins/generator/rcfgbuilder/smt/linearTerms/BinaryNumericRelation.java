package de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.smt.linearTerms;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * Represents a relation of the form ψ ▷ φ, where the terms ψ and φ have 
 * numeric sort and ▷ is one of the following relation symbols
 * {=, <=, >=, <, >, !=, distinct }.
 * This class is only a helper that can be used to detect if a relation has this
 * form.
 *
 * @author Matthias Heizmann
 */
public class BinaryNumericRelation {
	public enum RelationSymbol {
	    EQ("="),
	    DISTINCT("distinct"),
	    LEQ("<="),
	    GEQ(">="),
	    LESS("<"),
	    GREATER(">");
	    
	    private final String m_StringRepresentation;
	    
	    RelationSymbol(String stringRepresentation) {
	    	this.m_StringRepresentation = stringRepresentation;
	    }

	    @Override
	    public String toString() {
	        return m_StringRepresentation;
	    }
	}
	
	private final RelationSymbol m_RelationSymbol;
	private final Term m_Lhs;
	private final Term m_Rhs;
	
	public String getRelationSymbol() {
		return m_RelationSymbol.toString();
	}

	public Term getLhs() {
		return m_Lhs;
	}

	public Term getRhs() {
		return m_Rhs;
	}

	private static RelationSymbol getNegation(RelationSymbol symb) {
		final RelationSymbol result;
		switch (symb) {
		case EQ:
			result = RelationSymbol.DISTINCT;
			break;
		case DISTINCT:
			result = RelationSymbol.EQ;
			break;
		case LEQ:
			result = RelationSymbol.GREATER;
			break;
		case GEQ:
			result = RelationSymbol.LESS;
			break;
		case LESS:
			result = RelationSymbol.GEQ;
			break;
		case GREATER:
			result = RelationSymbol.LEQ;
			break;
		default:
			throw new UnsupportedOperationException("unknown numeric relation");
		}
		return result;
	}
	
	public BinaryNumericRelation(Term term) throws NotBinaryNumericRelationException {
		if (!(term instanceof ApplicationTerm)) {
			throw new NotBinaryNumericRelationException("no ApplicationTerm");
		}
		ApplicationTerm appTerm = (ApplicationTerm) term;
		String functionSymbolName = appTerm.getFunction().getName();
		Term[] params = appTerm.getParameters();
		boolean isNegated;
		if (functionSymbolName.equals("not")) {
			assert params.length == 1;
			Term notTerm = params[0];
			if (!(notTerm instanceof ApplicationTerm)) {
				throw new NotBinaryNumericRelationException("no ApplicationTerm");
			}
			isNegated = true;
			appTerm = (ApplicationTerm) notTerm;
			functionSymbolName = appTerm.getFunction().getName();
			params = appTerm.getParameters();
		} else {
			isNegated = false;
		}
		if (appTerm.getParameters().length != 2) {
			throw new NotBinaryNumericRelationException("not binary");
		}
		if (!appTerm.getParameters()[0].getSort().isNumericSort()) {
			throw new NotBinaryNumericRelationException("not numeric");
		} else {
			assert appTerm.getParameters()[1].getSort().isNumericSort();
		}
		
		RelationSymbol relSymb = null;
		for (RelationSymbol symb : RelationSymbol.values()) {
			if (symb.toString().equals(functionSymbolName)) {
				relSymb = isNegated ? getNegation(symb) : symb;
				break;
			}
		}
		if (relSymb == null) {
			throw new NotBinaryNumericRelationException(
					"no binary numberic relation symbol");
		} else {
			m_RelationSymbol = relSymb;
			m_Lhs = params[0];
			m_Rhs = params[1];
		}
	}
	

	class NotBinaryNumericRelationException extends Exception {

		private static final long serialVersionUID = 1L;

		public NotBinaryNumericRelationException(String message) {
			super(message);
		}
	}
	

}
