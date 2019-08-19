/*
 * Copyright (C) 2014-2015 Jan Leike (leike@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 University of Freiburg
 *
 * This file is part of the ULTIMATE ModelCheckerUtils Library.
 * 
 * The ULTIMATE ModelCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE ModelCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ModelCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ModelCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE ModelCheckerUtils Library grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transformations;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/**
 * Kind of {@link IReplacementVar} that cannot be used in an interprocedural 
 * analysis but do not require primed and unprimed constants.
 *
 * @author Jan Leike, Matthias Heizmann
 */
public class IntraproceduralReplacementVar implements IProgramVar, IReplacementVar {
	private static final long serialVersionUID = 5797704734079950805L;

	private final String mName;
	private final Term mDefinition;
	private final TermVariable mTermVariable;

	/**
	 * @param name
	 *            a globally unique name
	 * @param definition
	 *            the definition of this replacement variable, i.e., the term it replaces
	 * @param tv 
	 */
	public IntraproceduralReplacementVar(final String name, final Term definition, final TermVariable tv) {
		mName = name;
		mDefinition = definition;
		mTermVariable = tv;
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transformations.IReplacementVar#getDefinition()
	 */
	@Override
	public Term getDefinition() {
		return mDefinition;
	}

	@Override
	public String getGloballyUniqueId() {
		return mName;
	}

	@Override
	public Term getTerm() {
		return getTermVariable();
	}

	@Override
	public String toString() {
		return mName;
	}

	@Override
	public String getProcedure() {
		throw new UnsupportedOperationException("IntraproceduralReplacementVars do not have procedure");
	}

	@Override
	public boolean isGlobal() {
		throw new UnsupportedOperationException("IntraproceduralReplacementVars are neither old nor non-old");
	}

	@Override
	public boolean isOldvar() {
		throw new UnsupportedOperationException("IntraproceduralReplacementVars are neither old nor non-old");
	}

	@Override
	public TermVariable getTermVariable() {
		return mTermVariable;
	}

	@Override
	public ApplicationTerm getDefaultConstant() {
		throw new UnsupportedOperationException("IntraproceduralReplacementVars do not have SMT terms");
	}

	@Override
	public ApplicationTerm getPrimedConstant() {
		throw new UnsupportedOperationException("IntraproceduralReplacementVars do not have SMT terms");
	}

}
