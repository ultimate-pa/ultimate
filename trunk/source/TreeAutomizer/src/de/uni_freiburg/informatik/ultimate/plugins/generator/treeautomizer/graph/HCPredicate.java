package de.uni_freiburg.informatik.ultimate.plugins.generator.treeautomizer.graph;

import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.models.annotation.Visualizable;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hornutil.HCVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hornutil.HornClausePredicateSymbol;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.BasicPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.util.HashUtils;

/**
 * @author mostafa.amin93@gmail.com
 *
 */
public class HCPredicate extends BasicPredicate implements IPredicate {
	private static final long serialVersionUID = 1750137515726690834L;
	private static final int serialHCPredicate = 1000000007;
	
	@Visualizable
	protected final HornClausePredicateSymbol mProgramPoint;

	private final Map<Term, HCVar> mProgramVars;
	
	protected HCPredicate(final HornClausePredicateSymbol programPoint, int serialNumber, final Term term,
			final Set<IProgramVar> vars, final Map<Term, HCVar> varsMap) {
		
		super(serialNumber, new String[]{}, term, vars, null);
		mProgramPoint = programPoint;
		
		mProgramVars = varsMap;
	}
	
	protected HCPredicate(final HornClausePredicateSymbol programPoint, final Term term, final Set<IProgramVar> vars,
			final Map<Term, HCVar> varsMap) {

		super(HashUtils.hashHsieh(serialHCPredicate, programPoint, term), new String[] {}, term, vars, null);
		mProgramPoint = programPoint;
		mProgramVars = varsMap;
	}
	
	protected HCPredicate(final HornClausePredicateSymbol programPoint, final Term term,
			final Map<Term, HCVar> varsMap) {
		this(programPoint, term, new HashSet<>(varsMap.values()), varsMap);
	}

	
	/**
	 * The published attributes. Update this and getFieldValue() if you add new attributes.
	 */
	private final static String[] s_AttribFields = { "ProgramPoint", "Formula", "Vars" };


	//@Override
	protected String[] getFieldNames() {
		return s_AttribFields;
	}

	public HCPredicate(final Term formula, final HCPredicate oldPredicate, final Map<Term, HCVar> varsMap) {
		// TODO: Intersect oldPredicate.mVars with formula.vars
		this(oldPredicate.mProgramPoint, HashUtils.hashHsieh(serialHCPredicate, formula, oldPredicate), formula,
				new HashSet<>(varsMap.values()), varsMap);

	}
	
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

	public Map<Term, HCVar> getVarsMap() {
		return mProgramVars;
	}
	
	@Override
	public String toString() {
		String result = "#"; // super.mSerialNumber + "#";
		if (mProgramPoint != null) {
			if (mProgramPoint.toString().equals("true")) {
				result += "True";
			} else if (mProgramPoint.toString().equals("false")) {
				result += "False";
			} else {
				result += mProgramPoint.toString();
			}
		}
		result += "@(" + mFormula.toString() + "::" + mProgramVars.toString() + ")";
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
