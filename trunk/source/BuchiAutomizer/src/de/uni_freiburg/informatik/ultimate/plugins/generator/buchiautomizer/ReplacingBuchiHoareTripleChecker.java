package de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer;

import java.util.Map;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IInternalAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.IncrementalPlicationChecker.Validity;

/**
 * for fairness Swap out predicates for predicates known to the pu
 */
public class ReplacingBuchiHoareTripleChecker extends BuchiHoareTripleChecker {
	Map<IPredicate, IPredicate> mReplacementMap;

	public ReplacingBuchiHoareTripleChecker(final IHoareTripleChecker iHoareTripleChecker,
			final Map<IPredicate, IPredicate> replacementMap) {
		super(iHoareTripleChecker);
		mReplacementMap = replacementMap;
	}

	@Override
	public Validity checkInternal(IPredicate pre, final IInternalAction act, final IPredicate succ) {
		pre = replaceIfRankDecreasePredicate(pre);
		return mIHoareTripleChecker.checkInternal(mReplacementMap.get(pre), act, mReplacementMap.get(succ));
	}

}
