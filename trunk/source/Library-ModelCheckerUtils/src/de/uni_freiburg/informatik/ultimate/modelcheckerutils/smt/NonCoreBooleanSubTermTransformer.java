package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;

/**
 * Transform non-CoreBoolean subterms of a term. Here, we call a term 
 * non-CoreBoolean if it is not an ApplicationTerm whose connective is defined
 * by the core theory and whose parameters dot not all have sort Bool.
 * 
 * @author Matthias Heizmann
 *
 */
public abstract class NonCoreBooleanSubTermTransformer {
	
	private NonCoreBooleanSubtermTransformerHelper m_TransformerHelper;
	
	public Term transform(Term term) {
		if (!term.getSort().getName().equals("Bool")) {
			throw new IllegalArgumentException("Input term of sort Bool");
		}
		m_TransformerHelper = new NonCoreBooleanSubtermTransformerHelper();
		Term result = m_TransformerHelper.transform(term);
		return result;
	}

	private static boolean hasBooleanParams(Term[] parameters) {
		for (Term term : parameters) {
			if (!term.getSort().getName().equals("Bool")) {
				return false;
			}
		}
		return true;
	}

	private static boolean isCoreBooleanConnective(String fun) {
		if (fun.equals("=")) {
			return true;
		} else if (fun.equals("and")) {
			return true;
		} else if (fun.equals("or")) {
			return true;
		} else if (fun.equals("=>")) {
			return true;
		} else if (fun.equals("xor")) {
			return true;
		} else if (fun.equals("distinct")) {
			return true;
		} else if (fun.equals("ite")) {
			return true;
		} else {
			return false;
		}
	}


	private class NonCoreBooleanSubtermTransformerHelper extends TermTransformer {

		@Override
		protected void convert(Term term) {
			assert term.getSort().getName().equals("Bool") : "not Bool";
			if (term instanceof ApplicationTerm) {
				ApplicationTerm appTerm = (ApplicationTerm) term;
				String funName = appTerm.getFunction().getName();
				if (isCoreBooleanConnective(funName) && 
						hasBooleanParams(appTerm.getParameters())) {
					super.convert(term);
				} else {
					Term transformed = transformNonCoreBooleanSubterm(term);
					setResult(transformed);
					return;
				}
			}
			super.convert(term);
		}
		
	}


	protected abstract Term transformNonCoreBooleanSubterm(Term term);

}
