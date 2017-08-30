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
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.CommuhashNormalForm;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.Substitution;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.ArrayIndex;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.MultiDimensionalSelect;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.VPDomainPreanalysis;

/**
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
public class EqNodeAndFunctionFactory extends AbstractNodeAndFunctionFactory<EqNode, EqFunction, Term> {

	ManagedScript mMgdScript;

	private final Map<Term, EqNode> mTermToEqNode = new HashMap<>();

	private final Map<Term, EqFunction> mTermToEqFunction = new HashMap<>();

	private final VPDomainPreanalysis mPreAnalysis;

	public EqNodeAndFunctionFactory(final VPDomainPreanalysis preAnalysis, final ManagedScript script) {
		mPreAnalysis = preAnalysis;
		mMgdScript = script;
	}

	public ManagedScript getScript() {
		return mMgdScript;
	}


	@Override
	public EqNode getOrConstructNode(final Term term) {
		if (term instanceof ApplicationTerm && ((ApplicationTerm) term).getParameters().length > 0) {
			if ("select".equals(((ApplicationTerm) term).getFunction().getName())) {
				return getOrConstructEqFunctionNode((ApplicationTerm) term);
			} else if (((ApplicationTerm) term).getFunction().isIntern()) {
				return getOrConstructNonAtomicBaseNode(term);
			} else {
				throw new UnsupportedOperationException();
			}
		} else if (term instanceof ApplicationTerm && ((ApplicationTerm) term).getParameters().length == 0) {
			return getOrConstructEqAtomicBaseNode(term);
		} else if (term instanceof TermVariable) {
			return getOrConstructEqAtomicBaseNode(term);
		} else if (term instanceof ConstantTerm) {
			return getOrConstructEqAtomicBaseNode(term);
		} else {
			throw new UnsupportedOperationException();
		}
	}

	private EqNode getOrConstructNonAtomicBaseNode(final Term term) {
		mMgdScript.lock(this);
		final Term normalizedTerm = new CommuhashNormalForm(
				mPreAnalysis.getServices(), mMgdScript.getScript()).transform(term);
		mMgdScript.unlock(this);
		EqNode result = mTermToEqNode.get(normalizedTerm);
		if (result == null) {
//			result = new EqNonAtomicBaseNode(normalizedTerm, this);
			result = getBaseElement(normalizedTerm);
			mTermToEqNode.put(normalizedTerm, result);
		}
		assert result instanceof EqNonAtomicBaseNode;
		return result;
	}

	private EqNode getOrConstructEqFunctionNode(final ApplicationTerm selectTerm) {
		EqNode result = mTermToEqNode.get(selectTerm);

		if (result == null) {
			final MultiDimensionalSelect mds = new MultiDimensionalSelect(selectTerm);

			final EqFunction function = getOrConstructFunction(mds.getArray());

			final List<EqNode> args = new ArrayList<>();
			for (final Term index : mds.getIndex()) {
				args.add(getOrConstructNode(index));
			}

//			result = new EqFunctionNode(function, args, selectTerm, this);
			result = super.getFuncAppElement(function, args);
			mTermToEqNode.put(selectTerm, result);
		}
		assert result instanceof EqFunctionNode;
		assert result.getTerm() == selectTerm;
		return result;
	}

	private EqNode getOrConstructEqAtomicBaseNode(final Term term) {
		EqNode result = mTermToEqNode.get(term);
		if (result == null) {
//			result = new EqAtomicBaseNode(term, this);
			result = getBaseElement(term);
			mTermToEqNode.put(term, result);
		}
		assert result instanceof EqAtomicBaseNode;
		return result;

	}

	@Override
	public EqFunction getOrConstructFunction(final Term term) {
		if (term instanceof ApplicationTerm && ((ApplicationTerm) term).getParameters().length > 0) {
			if ("store".equals(((ApplicationTerm) term).getFunction().getName())) {
				throw new UnsupportedOperationException();
			} else {
				throw new UnsupportedOperationException();
			}
		} else if (term instanceof ApplicationTerm && ((ApplicationTerm) term).getParameters().length == 0) {
			return getOrConstructAtomicEqFunction(term);
		} else if (term instanceof TermVariable) {
			return getOrConstructAtomicEqFunction(term);
		} else if (term instanceof ConstantTerm) {
			return getOrConstructAtomicEqFunction(term);
		} else {
			throw new UnsupportedOperationException();
		}
	}

	private EqFunction getOrConstructAtomicEqFunction(final Term term) {
		assert !(term instanceof ApplicationTerm) || !"store".equals(((ApplicationTerm) term).getFunction().getName());
		EqFunction result = mTermToEqFunction.get(term);
		if (result == null) {
			result = new EqFunction(term, this);
			mTermToEqFunction.put(term, result);
		}
		return result;
	}

	public EqFunction constructRenamedEqFunction(final EqFunction eqFunction, final Map<Term, Term> substitutionMapping) {
		final Term substitutedTerm = new Substitution(mMgdScript, substitutionMapping).transform(eqFunction.getTerm());
		return getOrConstructFunction(substitutedTerm);
	}

	/**
	 *
	 * @param term
	 * @return
	 */
	@Override
	public EqNode getExistingNode(final Term term) {
		final Term normalizedTerm;
		if (term instanceof ApplicationTerm && !SmtUtils.isConstant(term)) {
			mMgdScript.lock(this);
			normalizedTerm = new CommuhashNormalForm(
					mPreAnalysis.getServices(), mMgdScript.getScript()).transform(term);
			mMgdScript.unlock(this);
		} else {
			normalizedTerm = term;
		}
		return mTermToEqNode.get(normalizedTerm);
	}

	/**
	 *
	 * @param term
	 * @return
	 */
	@Override
	public EqFunction getExistingFunction(final Term term) {
		final EqFunction res = mTermToEqFunction.get(term);
		if (res == null) {
			throw new IllegalArgumentException("this method expects that the given term is already known to this "
					+ "factory");
		}
		return res;
	}

	@Override
	protected EqNode newBaseElement(final Term c) {
		assert SmtUtils.isConstant(c) || c instanceof TermVariable || c instanceof ConstantTerm;
		return new EqAtomicBaseNode(c, this);
//		assert false;
//		return getOrConstructEqAtomicBaseNode(c);
	}

	@Override
	protected EqNode newFuncAppElement(final EqFunction func, final List<EqNode> args) {
		mMgdScript.lock(this);
//		final Term[] argTerms = args.stream().map(node -> node.getTerm()).collect(Collectors.toList())
//				.toArray(new Term[args.size()]);
//		final ApplicationTerm selectTerm = (ApplicationTerm) mMgdScript.term(this, f.getFunctionName(), argTerms);
		final ArrayIndex ai = new ArrayIndex(args.stream().map(node -> node.getTerm()).collect(Collectors.toList()));
		final Term selectTerm = SmtUtils.multiDimensionalSelect(mMgdScript.getScript(), func.getTerm(), ai);
		mMgdScript.unlock(this);
		return new EqFunctionNode(func, args, selectTerm, this);
//		return getExistingNode(selectTerm);
//		return getOrConstructEqFunctionNode(selectTerm);
//		assert false;
//		return null;
	}

}
