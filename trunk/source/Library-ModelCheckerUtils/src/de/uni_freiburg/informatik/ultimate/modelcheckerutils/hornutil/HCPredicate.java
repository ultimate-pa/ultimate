
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.hornutil;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.BasicPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;

/**
 * @author mostafa.amin93@gmail.com
 * 
 */
public class HCPredicate extends BasicPredicate implements IPredicate {
	private static final long serialVersionUID = 1750137515726690834L;
	protected final HornClausePredicateSymbol mProgramPoint;

	protected HCPredicate(HornClausePredicateSymbol programPoint, int serialNumber, Term term,
			Set<IProgramVar> vars) {//, Term closedFormula) {
		super(serialNumber, new String[]{}, term, vars, null);
		mProgramPoint = programPoint;
	}
	
	public HCPredicate(Term formula, HCPredicate oldPredicate) {
		// TODO: Intersect oldPredicate.mVars with formula.vars
		this(oldPredicate.mProgramPoint, oldPredicate.mSerialNumber, formula, oldPredicate.mVars);
	}

	/**
	 * The published attributes. Update this and getFieldValue() if you add new
	 * attributes.
	 */
	private final static String[] s_AttribFields = { "ProgramPoint", "Procedures", "Formula", "Vars" };

	@Override
	protected String[] getFieldNames() {
		return s_AttribFields;
	}

	@Override
	protected Object getFieldValue(String field) {
		if (field == "ProgramPoint") {
			return mProcedures;
		} else {
			return super.getFieldValue(field);
		}
	}

	/*
	@Override
	public HornClausePredicateSymbol getProgramPoint() {
		return mProgramPoint;
	}
	*/

	/**
	 * @return the mAssertion
	 */
	@Override
	public Term getFormula() {
		return mFormula;
	}

	@Override
	public Term getClosedFormula() {
		return mClosedFormula;
	}

	@Override
	public Set<IProgramVar> getVars() {
		return mVars;
	}

	@Override
	public String toString() {
		String result = super.mSerialNumber + "#";
		if (mProgramPoint != null) {
			result += mProgramPoint.toString();
		}
		result += mFormula.toString();
		return result;
	}

	@Override
	public boolean isUnknown() {
		return false;
	}

	@Override
	public int hashCode() {
		return super.mSerialNumber;
	}
}