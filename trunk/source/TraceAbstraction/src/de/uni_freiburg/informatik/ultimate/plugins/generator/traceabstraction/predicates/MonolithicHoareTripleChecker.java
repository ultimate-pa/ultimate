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
	public HTTV checkInternal(IPredicate pre, CodeBlock cb, IPredicate succ) {
		return lbool2httv(m_SmtManager.isInductive(pre, cb, succ));
	}

	@Override
	public HTTV checkCall(IPredicate pre, CodeBlock cb, IPredicate succ) {
		return lbool2httv(m_SmtManager.isInductiveCall(pre, (Call) cb, succ));
	}

	@Override
	public HTTV checkReturn(IPredicate preLin, IPredicate preHier,
			CodeBlock cb, IPredicate succ) {
		return lbool2httv(m_SmtManager.isInductiveReturn(preLin, preHier, (Return) cb, succ));
	}

	
	
	public static HTTV lbool2httv(LBool lbool) {
		switch (lbool) {
		case SAT:
			return HTTV.INVALID;
		case UNKNOWN:
			return HTTV.UNKNOWN;
		case UNSAT:
			return HTTV.VALID;
		default:
			throw new AssertionError();
		}
		
	}
}
