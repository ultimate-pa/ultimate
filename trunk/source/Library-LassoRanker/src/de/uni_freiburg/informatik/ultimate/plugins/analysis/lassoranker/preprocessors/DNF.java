/*
 * Copyright (C) 2012-2014 University of Freiburg
 *
 * This file is part of the ULTIMATE LassoRanker Library.
 *
 * The ULTIMATE LassoRanker Library is free software: you can redistribute it
 * and/or modify it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 *
 * The ULTIMATE LassoRanker Library is distributed in the hope that it will
 * be useful, but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE LassoRanker Library. If not,
 * see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE LassoRanker Library, or any covered work, by
 * linking or combining it with Eclipse RCP (or a modified version of
 * Eclipse RCP), containing parts covered by the terms of the Eclipse Public
 * License, the licensors of the ULTIMATE LassoRanker Library grant you
 * additional permission to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.preprocessors;

import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.exceptions.TermException;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.smt.normalForms.Dnf;


/**
 * Convert a formula into disjunctive normal form, i.e., a formula of the
 * form
 * 
 * <pre>OR ( AND ( NOT? inequality ) )</pre>
 * 
 * This includes a negation normal form (negations only occur before atoms).
 * 
 * @author Jan Leike
 */
public class DNF implements PreProcessor {
	@Override
	public String getDescription() {
		return "Transform the given term into disjunctive normal form.";
	}
	
	@Override
	public Term process(Script script, Term term) throws TermException {
		// Use the DNF transformer from RCFGBuilder
		Dnf dnf_transformer = new Dnf(script);
		return dnf_transformer.transform(term);
	}
}