/*
 * Copyright (C) 2017 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.vpdomain;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.CommuhashNormalForm;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearTerms.AffineTerm;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearTerms.AffineTermTransformer;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;

/**
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
public class EqNodeAndFunctionFactory extends AbstractNodeAndFunctionFactory<EqNode, Term> {

	private final IUltimateServiceProvider mServices;
	private final ManagedScript mMgdScript;

	private final Map<Term, EqNode> mTermToEqNode = new HashMap<>();

//	private final VPDomainPreanalysis mPreAnalysis;

	public EqNodeAndFunctionFactory(final IUltimateServiceProvider services, final ManagedScript script) {
//		mPreAnalysis = preAnalysis;
		mServices = services;
		mMgdScript = script;
	}

	public ManagedScript getScript() {
		return mMgdScript;
	}


	@Override
	public EqNode getOrConstructNode(final Term term) {
		if (SmtUtils.isFunctionApplication(term, "select")) {
			return getOrConstructEqFunctionNode((ApplicationTerm) term);
		} else if (isAtomic(term)) {
			return getOrConstructEqAtomicBaseNode(term);
		} else {
			return getOrConstructNonAtomicBaseNode(term);
		}
	}

	private EqNode getOrConstructNonAtomicBaseNode(final Term term) {
		final Term normalizedTerm = normalizeTerm(term);
		EqNode result = mTermToEqNode.get(normalizedTerm);
		if (result == null) {
			result = getBaseElement(normalizedTerm);
			mTermToEqNode.put(normalizedTerm, result);
		}
		assert result instanceof EqNonAtomicBaseNode;
		return result;
	}

	private EqNode getOrConstructEqFunctionNode(final ApplicationTerm selectTerm) {
		EqNode result = mTermToEqNode.get(selectTerm);

		if (result == null) {
			final EqNode funcNode = getOrConstructNode(selectTerm.getParameters()[0]);
			final EqNode argNode = getOrConstructNode(selectTerm.getParameters()[1]);
			result = super.getOrConstructFuncAppElement(funcNode, argNode);

			mTermToEqNode.put(selectTerm, result);
		}
		assert result instanceof EqFunctionApplicationNode;
		return result;
	}

	private EqNode getOrConstructEqAtomicBaseNode(final Term term) {
		final Term normalizedTerm = normalizeTerm(term);

		EqNode result = mTermToEqNode.get(normalizedTerm);
		if (result == null) {
			result = getBaseElement(normalizedTerm);
			mTermToEqNode.put(normalizedTerm, result);
		}
		assert result instanceof EqAtomicBaseNode;
		return result;

	}

	private Term normalizeTerm(final Term term) {
		if (term instanceof TermVariable) {
			return term;
		}

		mMgdScript.lock(this);
		final AffineTerm affineTerm = (AffineTerm) new AffineTermTransformer(mMgdScript.getScript()).transform(term);
		mMgdScript.unlock(this);

		if (affineTerm.isErrorTerm()) {
			return new CommuhashNormalForm(mServices, mMgdScript.getScript()).transform(term);
		}
		return affineTerm.toTerm(mMgdScript.getScript());
	}

	/**
	 *
	 * @param term
	 * @return
	 */
	@Override
	public EqNode getExistingNode(final Term term) {
		final EqNode result = mTermToEqNode.get(normalizeTerm(term));
		assert result != null;
		return result;
	}

	/**
	 * Checks if the given term is a literal.
	 * Examples of literals (sometimes called constants, but we have other uses for that word) are:
	 *  1, 2, -1, true, false, 1bv16 (bitvector constant/literal)
	 *
	 * The defining trait of literals for our purposes is that two different literals always have a different value,
	 * too.
	 *
	 * @param term
	 * @return
	 */
	private boolean isTermALiteral(final Term term) {
		if (term instanceof TermVariable) {
			return false;
		}
		if (SmtUtils.isTrue(term) || SmtUtils.isFalse(term)) {
			return true;
		}
		if (term instanceof ConstantTerm) {
			return true;
		}

		mMgdScript.lock(this);
		final AffineTerm affineTerm = (AffineTerm) new AffineTermTransformer(mMgdScript.getScript()).transform(term);
		mMgdScript.unlock(this);

		if (affineTerm.isErrorTerm()) {
			return false;
		}

		if (affineTerm.isConstant()) {
			return true;
		}
		return false;
	}

	/**
	 * We call a Term atomic here if it is either a TermVariable, or does not contain any TermVariables.
	 * (this has nothing to do with Boolean atoms)
	 *
	 * Explanation:
	 * Atomic in this sense means dependency-free.
	 * I.e.: if we havoc some other term (a TermVariable), can we guarantee that this term is not concerned by that.
	 *
	 * @param term
	 * @return
	 */
	private boolean isAtomic(final Term term) {
		return term instanceof TermVariable || term.getFreeVars().length == 0;
	}

	@Override
	protected EqNode newBaseElement(final Term term) {
		if (isAtomic(term)) {
			// term has no dependencies on other terms --> use an EqAtomicBaseNode
			return new EqAtomicBaseNode(term, isTermALiteral(term), this);
		} else {
			assert term.getFreeVars().length > 0;
			final Collection<EqNode> supportingNodes = new ArrayList<>();
			for (final TermVariable fv : term.getFreeVars()) {
				supportingNodes.add(getOrConstructNode(fv));
			}
			return new EqNonAtomicBaseNode(term, supportingNodes, this);
		}
	}

	@Override
	protected EqNode newFuncAppElement(final EqNode func, final EqNode arg) {
		final Term selectTerm = buildSelectTerm(func, arg);
		return new EqFunctionApplicationNode(func, arg, selectTerm, this);
	}

	private Term buildSelectTerm(final EqNode func, final EqNode arg) {
		mMgdScript.lock(this);
		final Term selectTerm = mMgdScript.term(this, "select", func.getTerm(), arg.getTerm());
		mMgdScript.unlock(this);
		return selectTerm;
	}

	/**
	 * Determines if a given term should get a node with or without the isFunction flag set.
	 *
	 * @param term
	 * @return
	 */
	boolean isFunction(final Term term) {
		return term.getSort().isArraySort();
	}
}
