package de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer;

import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.EdgeChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;

/**
 * EdgeChecker that is aware of the special Honda and RankDecrease predicates
 * used in Buchi termination analysis.
 * @author heizmann@informatik.uni-freiburg.de
 *
 */
public class BuchiEdgeChecker extends EdgeChecker {

	private final IPredicate m_HondaPredicate;
	private final IPredicate m_RankDecrease;
	private final BoogieVar m_Unseeded;
	private final BoogieVar m_OldRank;

	public BuchiEdgeChecker(SmtManager smtManager, 
			BuchiModGlobalVarManager buchiModGlobalVarManager,
			IPredicate hondaPredicate,
			IPredicate rankDecrease, BoogieVar unseeded, BoogieVar oldRank) {
		super(smtManager, buchiModGlobalVarManager);
		m_HondaPredicate = hondaPredicate;
		m_RankDecrease = rankDecrease;
		m_Unseeded = unseeded;
		m_OldRank = oldRank;
	}
	@Override
	public LBool postInternalImplies(IPredicate p) {
		if (p == m_HondaPredicate) {
			p = m_RankDecrease;
		}
		return super.postInternalImplies(p);
	}
	@Override
	public LBool postCallImplies(IPredicate p) {
		if (p == m_HondaPredicate) {
			p = m_RankDecrease;
		}
		return super.postCallImplies(p);
	}
	@Override
	public LBool postReturnImplies(IPredicate p) {
		if (p == m_HondaPredicate) {
			p = m_RankDecrease;
		}
		return super.postReturnImplies(p);
	}
	@Override
	public LBool sdecInternalSelfloop(IPredicate p, CodeBlock cb) {
		return null; 
	}
	@Override
	public LBool sdecCallSelfloop(IPredicate p, CodeBlock cb) {
		return null;	}
	@Override
	public LBool sdecReturnSelfloopPre(IPredicate p, Return ret) {
		return null;	}
	@Override
	public LBool sdecReturnSelfloopHier(IPredicate p, Return ret) {
		return null;
	}
	@Override
	public LBool sdecInternalToFalse(IPredicate pre, CodeBlock cb) {
		return null;
	}
	@Override
	public LBool sdecInteral(IPredicate pre, CodeBlock cb, IPredicate post) {
		return null;
	}
	@Override
	public LBool sdLazyEcInteral(IPredicate pre, CodeBlock cb, IPredicate post) {
		return null;
	}
	@Override
	public LBool sdecCall(IPredicate pre, CodeBlock cb, IPredicate post) {
		return null;
	}
	@Override
	public LBool sdLazyEcCall(IPredicate pre, Call cb, IPredicate post) {
		return null;
	}
	@Override
	public LBool sdecReturn(IPredicate pre, IPredicate hier, CodeBlock cb,
			IPredicate post) {
		return null;
	}
	@Override
	public LBool sdLazyEcReturn(IPredicate pre, IPredicate hier, Return cb,
			IPredicate post) {
		return null;
	}

	

}
