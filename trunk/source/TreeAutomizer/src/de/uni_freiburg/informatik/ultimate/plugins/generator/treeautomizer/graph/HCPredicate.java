/*
 * Copyright (C) 2016 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2016 Mostafa M.A. (mostafa.amin93@gmail.com)
 * Copyright (C) 2016 University of Freiburg
 *
 * This file is part of the ULTIMATE TreeAutomizer Plugin.
 *
 * The ULTIMATE TreeAutomizer Plugin is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TreeAutomizer Plugin is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TreeAutomizer Plugin. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TreeAutomizer Plugin, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TreeAutomizer Plugin grant you additional permission
 * to convey the resulting work.
 */
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
	
	/**
	 * The published attributes. Update this and getFieldValue() if you add new attributes.
	 */
	private static final String[] s_AttribFields = { "ProgramPoint", "Formula", "Vars" };

	protected HCPredicate(final HornClausePredicateSymbol programPoint, final int serialNumber, final Term term,
			final Set<IProgramVar> vars, final Map<Term, HCVar> varsMap, final Term closedFormula) {
		super(serialNumber, new String[]{}, term, vars, closedFormula);
		mProgramPoint = programPoint;
		mProgramVars = varsMap;
	}

	protected HCPredicate(final HornClausePredicateSymbol programPoint, final Term term,
			final Map<Term, HCVar> varsMap, final Term closedFormula) {
		this(programPoint, HashUtils.hashHsieh(serialHCPredicate, programPoint, term),
			term, new HashSet<>(varsMap.values()), varsMap, closedFormula);
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
			if (mProgramPoint.getName().equals("true")) {
				result += "True";
			} else if (mProgramPoint.getName().equals("false")) {
				result += "False";
			} else {
				result += mProgramPoint.getName();
			}
		}
		result += "@(" + mFormula.toString() + ")";//+ "::" + mProgramVars.toString() + ")";
		return result;
	}
	
	@Override
	public boolean isUnknown() {
		return false;
	}
	
	//@Override
	protected String[] getFieldNames() {
		return s_AttribFields;
	}
}
