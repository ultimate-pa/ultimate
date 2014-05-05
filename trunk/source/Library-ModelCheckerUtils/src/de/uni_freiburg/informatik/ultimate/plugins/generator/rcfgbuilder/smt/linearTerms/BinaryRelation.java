package de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.smt.linearTerms;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * Helper class that can be used to detect if a relation has certain form.
 * @author Matthias Heizmann
 *
 */
public abstract class BinaryRelation {

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
	
	/**
	 * Given a relation symbol ▷, returns the relation symbol ◾ such that the
	 * relation ψ ◾ φ is equivalent to the relation ¬(ψ ▷ φ), which is the 
	 * negated relation.
	 */
	protected static RelationSymbol negateRelation(RelationSymbol symb) {
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
	
	/**
	 * Given a relation symbol ▷, returns the relation symbol ◾ such that the
	 * relation ψ ◾ φ is equivalent to the relation φ ▷ ψ, which is the relation
	 * where we swaped the parameters.
	 */
	protected static RelationSymbol swapParameters(RelationSymbol symb) {
		final RelationSymbol result;
		switch (symb) {
		case EQ:
			result = RelationSymbol.EQ;
			break;
		case DISTINCT:
			result = RelationSymbol.DISTINCT;
			break;
		case LEQ:
			result = RelationSymbol.GEQ;
			break;
		case GEQ:
			result = RelationSymbol.LEQ;
			break;
		case LESS:
			result = RelationSymbol.GREATER;
			break;
		case GREATER:
			result = RelationSymbol.LESS;
			break;
		default:
			throw new UnsupportedOperationException("unknown numeric relation");
		}
		return result;
	}
	
	

	protected final RelationSymbol m_RelationSymbol;
	protected final Term m_Lhs;
	protected final Term m_Rhs;

	public BinaryRelation(Term term) throws NoRelationOfThisKindException {
		if (!(term instanceof ApplicationTerm)) {
			throw new NoRelationOfThisKindException("no ApplicationTerm");
		}
		ApplicationTerm appTerm = (ApplicationTerm) term;
		String functionSymbolName = appTerm.getFunction().getName();
		Term[] params = appTerm.getParameters();
		boolean isNegated;
		if (functionSymbolName.equals("not")) {
			assert params.length == 1;
			Term notTerm = params[0];
			if (!(notTerm instanceof ApplicationTerm)) {
				throw new NoRelationOfThisKindException("no ApplicationTerm");
			}
			isNegated = true;
			appTerm = (ApplicationTerm) notTerm;
			functionSymbolName = appTerm.getFunction().getName();
			params = appTerm.getParameters();
		} else {
			isNegated = false;
		}
		if (appTerm.getParameters().length != 2) {
			throw new NoRelationOfThisKindException("not binary");
		}
		checkSort(appTerm.getParameters());

		
		RelationSymbol relSymb = getRelationSymbol(functionSymbolName, isNegated);
		for (RelationSymbol symb : RelationSymbol.values()) {
			if (symb.toString().equals(functionSymbolName)) {
				relSymb = isNegated ? negateRelation(symb) : symb;
				break;
			}
		}
		if (relSymb == null) {
			throw new NoRelationOfThisKindException(
					"no binary numberic relation symbol");
		} else {
			m_RelationSymbol = relSymb;
			m_Lhs = params[0];
			m_Rhs = params[1];
		}
	}
	
	/**
	 * Check if Sort of parameters is compatible. Throw Exception if not.
	 * @throws NoRelationOfThisKindException
	 */
	abstract protected void checkSort(Term[] params) 
			throws NoRelationOfThisKindException;
	
	/**
	 * Return the RelationSymbol for this relation resolve negation
	 * @param functionSymbolName function symbol name of the original term
	 * @param isNegated true iff the original term is negated
	 * @throws NoRelationOfThisKindException
	 */
	abstract protected RelationSymbol getRelationSymbol(
			String functionSymbolName, boolean isNegated) 
					throws NoRelationOfThisKindException;

	public RelationSymbol getRelationSymbol() {
		return m_RelationSymbol;
	}

	public Term getLhs() {
		return m_Lhs;
	}

	public Term getRhs() {
		return m_Rhs;
	}
	
	public class NoRelationOfThisKindException extends Exception {

		private static final long serialVersionUID = 1L;

		public NoRelationOfThisKindException(String message) {
			super(message);
		}
	}

}