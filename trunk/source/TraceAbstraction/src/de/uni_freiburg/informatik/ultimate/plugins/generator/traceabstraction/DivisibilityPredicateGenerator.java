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
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
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

	public DivisibilityPredicateGenerator(SmtManager smtManger,
			PredicateUnifier predicateUnifier) {
		super();
		m_Script = smtManger.getScript();
		m_PredicateUnifier = predicateUnifier;
	}

	public Collection<IPredicate> divisibilityPredicates(Collection<IPredicate> preds) {
		Map<BoogieVar, Integer> offsetVar2size = new HashMap<>();
		for (IPredicate pred : preds) {
			for (BoogieVar bv : pred.getVars()) {
				if (isOffsetVar(bv)) {
					int size = getSize(bv);
					Integer oldValue = offsetVar2size.put(bv, size);
					assert oldValue == null || oldValue == size;
				}
			}
		}
		List<IPredicate> result = new ArrayList<IPredicate>();
		for (Entry<BoogieVar, Integer> entry  : offsetVar2size.entrySet()) {
			Term term = getDivisibilityTerm(entry.getKey(), entry.getValue());
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
		return bv.getIdentifier().contains("offset");
	}

	private Term getDivisibilityTerm(BoogieVar key, Integer value) {
		Term divisor = m_Script.numeral(BigInteger.valueOf(value));
		Term zero = m_Script.numeral(BigInteger.ZERO);
		Term divisible = m_Script.term("=", m_Script.term("mod", key.getTermVariable(), divisor), zero); 
		return divisible;
	}

}
