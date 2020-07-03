package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.linearterms;

import java.util.Collections;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.binaryrelation.RelationSymbol;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.binaryrelation.SolvedBinaryRelation;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.Case;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.SupportingTerm;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.MultiCaseSolvedBinaryRelation.Xnf;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * Represents a {@link Case}, that has not been finished yet, i.e. when there are still
 * case distinctions to be made.
 * Since this is a case that has not been finished yet, the SolvedBinaryRelation will always be null.
 * 
 * @author LeonardFichtner (leonard.fichtner@web.de)
 *
 */
public class IntermediateCase extends Case {
	
	private final Term mIntermediateRhs;
	private final RelationSymbol mIntermediateRelationSymbol;
	
	public IntermediateCase(final Set<SupportingTerm> supportingTerms, final Xnf xnf, 
							final Term rhs, final RelationSymbol relSym) {
		super(null, supportingTerms, xnf);
		mIntermediateRhs = rhs;
		mIntermediateRelationSymbol = relSym;
	}
	
	public Term getIntermediateRhs() {
		return mIntermediateRhs;
	}
	
	public RelationSymbol getIntermediateRelationSymbol() {
		return mIntermediateRelationSymbol;
	}
	
	/**
	 * Returns a case, that is similiar, 
	 * except that it now also consists of the SolvedBinaryRelation represented by
	 * "subject mRelationSymbol mIntermediateRhs"
	 */
	public Case finalizeCase(final Term subject) {
		return new Case(new SolvedBinaryRelation(subject, mIntermediateRhs, mIntermediateRelationSymbol, 
						Collections.emptyMap()), mSupportingTerms, mXnf);
	}
}
