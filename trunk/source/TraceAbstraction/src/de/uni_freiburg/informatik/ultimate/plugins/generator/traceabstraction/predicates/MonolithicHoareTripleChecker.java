package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates;

import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;

public class MonolithicHoareTripleChecker implements IHoareTripleChecker {
	
	private final SmtManager m_SmtManager;
	
	

	public MonolithicHoareTripleChecker(SmtManager smtManager) {
		super();
		m_SmtManager = smtManager;
	}

	@Override
	public Validity checkInternal(IPredicate pre, CodeBlock cb, IPredicate succ) {
		return lbool2httv(m_SmtManager.isInductive(pre, cb, succ));
	}

	@Override
	public Validity checkCall(IPredicate pre, CodeBlock cb, IPredicate succ) {
		return lbool2httv(m_SmtManager.isInductiveCall(pre, (Call) cb, succ));
	}

	@Override
	public Validity checkReturn(IPredicate preLin, IPredicate preHier,
			CodeBlock cb, IPredicate succ) {
		return lbool2httv(m_SmtManager.isInductiveReturn(preLin, preHier, (Return) cb, succ));
	}

	
	
	public static Validity lbool2httv(LBool lbool) {
		switch (lbool) {
		case SAT:
			return Validity.INVALID;
		case UNKNOWN:
			return Validity.UNKNOWN;
		case UNSAT:
			return Validity.VALID;
		default:
			throw new AssertionError();
		}
		
	}
}
