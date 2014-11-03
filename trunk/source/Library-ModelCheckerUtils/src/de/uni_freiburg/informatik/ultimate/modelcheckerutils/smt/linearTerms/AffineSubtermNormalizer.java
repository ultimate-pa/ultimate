package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearTerms;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearTerms.BinaryRelation.NoRelationOfThisKindException;

/**
 * Transform all subterms that are an affine relation to positive normal form.
 * 
 * @author Matthias Heizmann
 */
public class AffineSubtermNormalizer extends TermTransformer {

	private final Script m_Script;
	private final Logger mLogger;

	public AffineSubtermNormalizer(Script script, Logger logger) {
		super();
		m_Script = script;
		mLogger = logger;
	}

	private static boolean isBinaryNumericRelation(Term term) {
		boolean result = true;
		try {
			new BinaryNumericRelation(term);
		} catch (NoRelationOfThisKindException e) {
			result = false;
		}
		return result;
	}

	@Override
	protected void convert(Term term) {
		if (!term.getSort().getName().equals("Bool")) {
			// do not descend further
			super.setResult(term);
			return;
		}
		if (isBinaryNumericRelation(term)) {
			AffineRelation affRel = null;
			try {
				affRel = new AffineRelation(term, false);
			} catch (NotAffineException e) {
				setResult(term);
				return;
			}
			Term pnf = affRel.positiveNormalForm(m_Script);
			setResult(pnf);
			return;
		}

		super.convert(term);
	}

}
