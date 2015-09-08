/*
 * Copyright (C) 2014-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE TraceAbstraction plug-in.
 * 
 * The ULTIMATE TraceAbstraction plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE TraceAbstraction plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceAbstraction plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceAbstraction plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE TraceAbstraction plug-in grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SMT;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.MultiDimensionalSelect;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.TermVarsProc;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.PredicateUnifier;

/**
 * Generate predicates "x mod y == 0" for variables x that are used as offset
 * in pointers whose base type has size y.
 * Right now, this is a hack to find out if this is useful in practice.
 * 
 * @author Matthias Heizmann
 *
 */
public class DivisibilityPredicateGenerator {
	private final Script m_Script;
	private final PredicateUnifier m_PredicateUnifier;
	private final Boogie2SMT boogie2smt;

	public DivisibilityPredicateGenerator(SmtManager smtManger,
			PredicateUnifier predicateUnifier) {
		super();
		m_Script = smtManger.getScript();
		m_PredicateUnifier = predicateUnifier;
		boogie2smt = smtManger.getBoogie2Smt();
	}

	public Collection<IPredicate> divisibilityPredicates(Collection<IPredicate> preds) {
		Map<BoogieVar, Integer> offsetVar2size = new HashMap<>();
		List<IPredicate> result = new ArrayList<IPredicate>();
		for (IPredicate pred : preds) {
			for (BoogieVar bv : pred.getVars()) {
				if (isOffsetVar(bv)) {
					int size = getSize(bv);
					Integer oldValue = offsetVar2size.put(bv, size);
					assert oldValue == null || oldValue == size;
				}
			}
			List<MultiDimensionalSelect> mdsList = MultiDimensionalSelect.extractSelectDeep(pred.getFormula(), false);
			for (MultiDimensionalSelect mds : mdsList) {
				if (isLengthArray(mds.getArray())) {
					Term term = getDivisibilityTerm(mds.getSelectTerm(), Integer.valueOf(4));
					TermVarsProc tvp = TermVarsProc.computeTermVarsProc(term, boogie2smt);
					IPredicate unified = m_PredicateUnifier.getOrConstructPredicate(tvp);
					result.add(unified);
				}
			}
			
		}
		for (Entry<BoogieVar, Integer> entry  : offsetVar2size.entrySet()) {
			Term term = getDivisibilityTerm(entry.getKey().getTermVariable(), entry.getValue());
			Set<BoogieVar> vars = Collections.singleton(entry.getKey());
			String bvProc = entry.getKey().getProcedure();
			String[] procs = bvProc == null ? new String[0] : new String[]{bvProc};
//			Term closedTerm = PredicateUtils.computeClosedFormula(term, vars, m_Script);
//			TermVarsProc tvp = new TermVarsProc(term, vars , procedures , closedTerm);
			IPredicate unified = m_PredicateUnifier.getOrConstructPredicate(term, vars, procs);
			result.add(unified);
		}
		return result;
	}

	private int getSize(BoogieVar bv) {
		return 4;
	}

	private boolean isOffsetVar(BoogieVar bv) {
		if (bv.getTermVariable().getSort().getName().equals("Int")) {
			return bv.getIdentifier().contains("offset");
		} else {
			return false;
		}
	}
	
	private boolean isLengthArray(Term term) {
		if (term instanceof TermVariable) {
			TermVariable tv = (TermVariable) term;
			if (tv.toString().contains("#length")) {
				return true;
			} else {
				return false;
			}
		} else {
			return false;
		}
	}

	private Term getDivisibilityTerm(Term term, Integer value) {
		Term divisor = m_Script.numeral(BigInteger.valueOf(value));
		Term zero = m_Script.numeral(BigInteger.ZERO);
		Term divisible = m_Script.term("=", m_Script.term("mod", term, divisor), zero); 
		return divisible;
	}

}
