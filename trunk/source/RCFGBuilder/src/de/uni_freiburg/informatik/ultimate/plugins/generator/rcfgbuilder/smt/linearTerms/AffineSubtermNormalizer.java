package de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.smt.linearTerms;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;

public class AffineSubtermNormalizer extends TermTransformer {
	
	private final Script m_Script;

	/**
	 * Transform all subterm that are an affine relation to positive normal form.
	 */
	public AffineSubtermNormalizer(Script script) {
		super();
		m_Script = script;
	}

	private static boolean hasAffineRelationSymbol(ApplicationTerm term) {
		String symb = term.getFunction().getName();
		return symb.equals("=") || symb.equals(">=") || symb.equals("<=") 
					|| symb.equals(">") || symb.equals("<");  
	}
	
	private static boolean firstParamIsNumeric(ApplicationTerm term) {
		return term.getParameters()[0].getSort().isNumericSort();
	}
	
	@Override
	protected void convert(Term term) {
		if (term instanceof ApplicationTerm) {
			ApplicationTerm appTerm = (ApplicationTerm) term;
			if (hasAffineRelationSymbol(appTerm) && firstParamIsNumeric(appTerm)
					&& appTerm.getParameters().length == 2) {
				AffineRelation affRel = null;
				try {
					affRel = new AffineRelation(appTerm);
				} catch (NotAffineException e) {
					setResult(appTerm);
					return;
				}
				Term pnf = affRel.positiveNormalForm(m_Script);
				setResult(pnf);
				return;
			}
		}
		super.convert(term);
	}

	
	
}
