/*
 * Copyright (C) 2016 Yu-Wen Chen 
 * Copyright (C) 2016 University of Freiburg
 *
 * This file is part of the ULTIMATE AbstractInterpretationV2 plug-in.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE AbstractInterpretationV2 plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE AbstractInterpretationV2 plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE AbstractInterpretationV2 plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp;

import java.util.HashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;

/**
 * 
 * @author Yu-Wen Chen (yuwenchen1105@gmail.com)
 */
public class PointerExpression {
	
	private Term term;
	private Map<TermVariable, IProgramVar> termMap;
	private boolean isConstant;
	
	public PointerExpression (Term term, Map<TermVariable, IProgramVar> termMap) {
		this.term = term;
		this.termMap = new HashMap<TermVariable, IProgramVar>(termMap);
		isConstant = false;
	}
	
	public PointerExpression (Term term, boolean isConstant) {
		this.term = term;
		termMap = null;
		this.isConstant = isConstant;
	}
	
	public Term getTerm() {
		return term;
	}
	public void setTerm(Term term) {
		this.term = term;
	}
	
	public Map<TermVariable, IProgramVar> getTermMap() {
		return termMap;
	}
	public void setTermMap(Map<TermVariable, IProgramVar> termMap) {
		this.termMap = termMap;
	}

	public boolean isConstant() {
		return isConstant;
	}

	public void setConstant(boolean isConstant) {
		this.isConstant = isConstant;
	}
	
	@Override
	public String toString() {
		return "Term: " + getTerm().toString();
	}
	
}
