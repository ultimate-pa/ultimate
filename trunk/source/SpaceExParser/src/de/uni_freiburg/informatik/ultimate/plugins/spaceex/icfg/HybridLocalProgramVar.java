/*
 * Copyright (C) 2017 Julian Loeffler (loefflju@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
 *
 * This file is part of the ULTIMATE SpaceExParser plug-in.
 *
 * The ULTIMATE SpaceExParser plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE SpaceExParser plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE SpaceExParser plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE SpaceExParser plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE SpaceExParser plug-in grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.plugins.spaceex.icfg;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.ILocalProgramVar;

public class HybridLocalProgramVar implements ILocalProgramVar {
	
	/**
	 * 
	 */
	private static final long serialVersionUID = -3777047546964046236L;
	
	private final TermVariable mTermVariable;
	private final ApplicationTerm mDefaultConstant;
	private final ApplicationTerm mPrimedConstant;
	private final String mId;
	private final String mProcedure;
	
	public HybridLocalProgramVar(final TermVariable termVariable, final ApplicationTerm defaultConstant,
			final ApplicationTerm primedConstant, final String id, final String procedure) {
		mTermVariable = termVariable;
		mDefaultConstant = defaultConstant;
		mPrimedConstant = primedConstant;
		mId = id;
		mProcedure = procedure;
	}
	
	@Override
	public TermVariable getTermVariable() {
		return mTermVariable;
	}
	
	@Override
	public ApplicationTerm getDefaultConstant() {
		return mDefaultConstant;
	}
	
	@Override
	public ApplicationTerm getPrimedConstant() {
		return mPrimedConstant;
	}
	
	@Override
	public Term getTerm() {
		return null;
	}
	
	@Override
	public boolean isGlobal() {
		// TODO Auto-generated method stub
		return false;
	}
	
	@Override
	public String getGloballyUniqueId() {
		// TODO Auto-generated method stub
		return mId;
	}
	
	@Override
	public String getProcedure() {
		// TODO Auto-generated method stub
		return mProcedure;
	}
	
	@Override
	public boolean isOldvar() {
		// TODO Auto-generated method stub
		return false;
	}
	
	@Override
	public String getIdentifier() {
		// TODO Auto-generated method stub
		return mId;
	}
	
}
