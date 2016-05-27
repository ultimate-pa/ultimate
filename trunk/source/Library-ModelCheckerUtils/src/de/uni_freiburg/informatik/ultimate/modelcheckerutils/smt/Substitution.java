/*
 * Copyright (C) 2013-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt;

import java.util.HashMap;
import java.util.Map;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.logic.FormulaUnLet;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Util;


/**
 * Substitutes TermVariables by Terms. Takes care that no quantified 
 * TermVariable is substituted. 
 * 2016-05-27 Matthias: This class is superseded by {@link SafeSubstitution}
 * and hence marked as deprecated.
 * 
 * @author Matthias Heizmann
 *
 */
@Deprecated
public class Substitution {
	private final Map<TermVariable,Term> mMapping;
	private final Script mScript;
	
	private final static boolean USE_SAFE_SUBSTITUTION = true;

	public Substitution(Map<TermVariable, Term> mapping, Script script) {
		mMapping = mapping;
		assert SmtUtils.neitherKeyNorValueIsNull(mapping) : "null in substitution";
		mScript = script;
	}
	
	public Term transform(Term term) {
		Term result = withLet(term);
		if (USE_SAFE_SUBSTITUTION) {
			final Term resultSS = withSS(term);
			assert (Util.checkSat(mScript, 
					mScript.term("distinct", result, resultSS)) != LBool.SAT) : 
						"Bug in safe substitution.";
			result = resultSS;
		}
		return result;
	}
	
	private Term withLet(Term term) {
		final TermVariable[] vars = new TermVariable[mMapping.size()];
		final Term[] values = new Term[mMapping.size()];
		int i=0;
		for (final Entry<TermVariable, Term> entry : mMapping.entrySet()) {
			vars[i] = entry.getKey();
			assert vars[i] != null : "substitution of null";
			values[i] = entry.getValue(); 
			assert values[i] != null : "substitution by null";
			i++;
		}
		Term result = mScript.let(vars, values, term);
		result = new FormulaUnLet().unlet(result);
		return result;
	}
	
	private Term withSS(Term term) {
		final Map<Term, Term> mapping = new HashMap<Term, Term>();
		for (final Entry<TermVariable, Term> entry : mMapping.entrySet()) {
			mapping.put(entry.getKey(), entry.getValue());
		}
		final Term result = (new SafeSubstitution(mScript, mapping)).transform(term);
		return result;
	}

}
