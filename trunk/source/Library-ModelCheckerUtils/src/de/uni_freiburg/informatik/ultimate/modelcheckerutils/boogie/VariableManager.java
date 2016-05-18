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

import de.uni_freiburg.informatik.ultimate.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.boogie.preprocessor.Activator;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.IFreshTermVariableConstructor;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
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
	private final IUltimateServiceProvider m_Services;
	private final ILogger m_Logger;
	private final MultiElementCounter<String> m_TvForBasenameCounter = 
			new MultiElementCounter<String>();
	private final Map<TermVariable, Term> m_TermVariable2Constant = 
			new HashMap<TermVariable, Term>();
	private final MultiElementCounter<TermVariable> m_ConstForTvCounter = 
			new MultiElementCounter<TermVariable>();
	/**
	 * Whenever we construct a TermVariable we store its basename.
	 * This is either the name of the BoogieVar for which it was constructed
	 * or the name for that it was constructed.
	 * Whenever we have to construct a fresh copy of a TermVariable
	 * we use the basename of this TermVariable to obtain a unique but very
	 * similar name for the new copy.
	 */
	private final Map<TermVariable, String> m_Tv2Basename = 
			new HashMap<TermVariable, String>();
	private final Script m_Script;
	
	VariableManager(Script script, IUltimateServiceProvider services) {
		m_Services = services;
		m_Logger = m_Services.getLoggingService().getLogger(Activator.PLUGIN_ID);
		m_Script = script;
	}
	
	public TermVariable constructFreshTermVariable(BoogieVar bv) {
		final String basename = bv.toString();
		final Integer newIndex = m_TvForBasenameCounter.increase(basename);
		final Sort sort = bv.getTermVariable().getSort();
		TermVariable result = m_Script.variable(
				"v_" + basename + "_" + newIndex, sort);
		m_Tv2Basename.put(result, basename);
		return result;
	}
	
	public TermVariable constructFreshCopy(TermVariable tv) {
		String basename = m_Tv2Basename.get(tv);
		if (basename == null) {
			m_Logger.warn("TermVariabe " + tv + 
					" not constructed by VariableManager. Cannot ensure absence of name clashes.");
			basename = SmtUtils.removeSmtQuoteCharacters(tv.getName());
		}
		final Integer newIndex = m_TvForBasenameCounter.increase(basename);
		TermVariable result = m_Script.variable(
				"v_" + basename + "_" + newIndex, tv.getSort());
		m_Tv2Basename.put(result, basename);
		return result;
	}
	
	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.ITermVariableConstructor#constructFreshTermVariable(java.lang.String, de.uni_freiburg.informatik.ultimate.logic.Sort)
	 */
	@Override
	public TermVariable constructFreshTermVariable(String name, Sort sort) {
		String withoutSmtQuoteChar = SmtUtils.removeSmtQuoteCharacters(name);
		final Integer newIndex = m_TvForBasenameCounter.increase(withoutSmtQuoteChar);
		
		TermVariable result = m_Script.variable(
				"v_" + withoutSmtQuoteChar + "_" + newIndex, sort);
		m_Tv2Basename.put(result, withoutSmtQuoteChar);
		return result;
	}
	
	public Term getOrConstructCorrespondingConstant(TermVariable tv) {
		Term constant = m_TermVariable2Constant.get(tv);
		if (constant == null) {
			constant = SmtUtils.termVariable2constant(m_Script, tv);
			m_TermVariable2Constant.put(tv, constant);
		}
		return constant;
	}
	
	public Term getCorrespondingConstant(TermVariable tv) {
		return m_TermVariable2Constant.get(tv);
	}
	
	public Term constructFreshConstant(TermVariable tv) {
		final Integer newIndex = m_ConstForTvCounter.increase(tv);
		String name = SmtUtils.removeSmtQuoteCharacters(tv.getName()) + "_fresh_" + newIndex;
		Sort resultSort = tv.getSort();
		m_Script.declareFun(name, new Sort[0], resultSort);
		return m_Script.term(name);
	}
	
//	/**
//	 * Declare new constant that has same name and same sort as tv.
//	 */
//	public Term constructConstant(TermVariable tv) {
//		String name = tv.getName();
//		Sort sort = tv.getSort();
//		m_Script.declareFun(name, new Sort[0], sort);
//		return m_Script.term(name);
//	}

	/**
	 * Construct a TermVariable whose name is given by the BoogieVar bv and
	 * and additional suffix. This TermVariable is not unified.
	 * If you use this method make sure that you do not call it twice for the
	 * same combination of bv and suffix.
	 */
	public TermVariable constructTermVariableWithSuffix(BoogieVar bv, String suffix) {
		final String basename = bv.toString() + SmtUtils.removeSmtQuoteCharacters(suffix);
		final Integer newIndex = m_TvForBasenameCounter.increase(basename);
		final Sort sort = bv.getTermVariable().getSort();
		TermVariable result = m_Script.variable(
				"v_" + basename + "_" + newIndex, sort);
		m_Tv2Basename.put(result, basename);
		return result;
	}
	
	

}
