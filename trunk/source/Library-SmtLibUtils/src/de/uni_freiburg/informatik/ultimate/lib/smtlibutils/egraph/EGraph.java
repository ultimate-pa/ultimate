package de.uni_freiburg.informatik.ultimate.lib.smtlibutils.egraph;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.binaryrelation.BinaryEqualityRelation;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.util.datastructures.UnionFind;

public class EGraph {
	private final IUltimateServiceProvider mServices;
	private final ManagedScript mMgdScript;
	/**
	 * Internal Union find data structure to partition terms into equivalence classes
	 **/
	private final UnionFind<Term> mUnionFind;

	/**
	 * Constructs a new empty e graph
	 **/
	public EGraph(final ManagedScript mgdScript, final IUltimateServiceProvider services) {
		mUnionFind = new UnionFind<>();
		mMgdScript = mgdScript;
		mServices = services;

	}

	private void addTerm(final Term term) {
		if ((term instanceof ConstantTerm)) {
			mUnionFind.findAndConstructEquivalenceClassIfNeeded(term);
		} else if (term instanceof ApplicationTerm) {
			final ApplicationTerm appTerm = (ApplicationTerm) term;
			final Term representative = mUnionFind.find(appTerm);
			if (representative == null) {
				mUnionFind.makeEquivalenceClass(appTerm);
				for (final Term arg : appTerm.getParameters()) {
					addTerm(arg);
				}
			}
		} else {
			throw new UnsupportedOperationException("Unsupported term type");
		}

	}

	public void addFormula(final Term formula) {
		final Term[] conjuncts = SmtUtils.cannibalize(mMgdScript, mServices, false, formula);

		for (final Term term : conjuncts) {
			final BinaryEqualityRelation binaryEqRelation = BinaryEqualityRelation.convert(term);
			if (binaryEqRelation == null) {
				addTerm(term);
			} else {
				addTerm(binaryEqRelation.getLhs());
				addTerm(binaryEqRelation.getRhs());
				mUnionFind.union(binaryEqRelation.getLhs(), binaryEqRelation.getRhs());
			}
		}
	}
}
