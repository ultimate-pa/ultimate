/*
 * Copyright (C) 2014-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie;

import java.util.HashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.boogie.preprocessor.Activator;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.IFreshTermVariableConstructor;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
/**
 * Constructs fresh TermVariables (i.e., TermVariables that have not been used
 * before). Each constructed TermVariable is named as follows.
 * The name start with the prefix "v_".
 * Next follows the "basename" which is e.g., the name of a BoogieVar or a
 * name given by the caller of the VariableManager.
 * The name ends with the suffix "_n" where n is number that we use to ensure
 * that each variable is unique.
 * 
 * @author Matthias Heizmann
 *
 */
public class VariableManager implements IFreshTermVariableConstructor {
	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private final MultiElementCounter<TermVariable> mConstForTvCounter = 
			new MultiElementCounter<TermVariable>();
	/**
	 * Whenever we construct a TermVariable we store its basename.
	 * This is either the name of the BoogieVar for which it was constructed
	 * or the name for that it was constructed.
	 * Whenever we have to construct a fresh copy of a TermVariable
	 * we use the basename of this TermVariable to obtain a unique but very
	 * similar name for the new copy.
	 */
	private final Map<TermVariable, String> mTv2Basename = 
			new HashMap<TermVariable, String>();
	private final ManagedScript mScript;
	
	VariableManager(final ManagedScript script, final IUltimateServiceProvider services) {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(Activator.PLUGIN_ID);
		mScript = script;
	}
	
	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.ITermVariableConstructor#constructFreshTermVariable(java.lang.String, de.uni_freiburg.informatik.ultimate.logic.Sort)
	 */
	@Override
	public TermVariable constructFreshTermVariable(final String name, final Sort sort) {
		final String withoutSmtQuoteChar = SmtUtils.removeSmtQuoteCharacters(name);
		final TermVariable result = mScript.constructFreshTermVariable(withoutSmtQuoteChar, sort);
		mTv2Basename.put(result, withoutSmtQuoteChar);
		return result;
	}
	
	public TermVariable constructFreshCopy(final TermVariable tv) {
		String basename = mTv2Basename.get(tv);
		if (basename == null) {
			mLogger.warn("TermVariabe " + tv + 
					" not constructed by VariableManager. Cannot ensure absence of name clashes.");
			basename = SmtUtils.removeSmtQuoteCharacters(tv.getName());
		}
		final TermVariable result = mScript.constructFreshTermVariable(basename, tv.getSort());
		mTv2Basename.put(result, basename);
		return result;
	}
	

	public Term constructFreshConstant(final TermVariable tv) {
		final Integer newIndex = mConstForTvCounter.increase(tv);
		final String name = SmtUtils.removeSmtQuoteCharacters(tv.getName()) + "_fresh_" + newIndex;
		final Sort resultSort = tv.getSort();
		mScript.getScript().declareFun(name, new Sort[0], resultSort);
		return mScript.getScript().term(name);
	}
	

	
	

}
