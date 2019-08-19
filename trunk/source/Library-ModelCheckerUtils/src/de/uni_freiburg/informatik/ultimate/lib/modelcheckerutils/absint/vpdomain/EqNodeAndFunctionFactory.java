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
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.vpdomain;

import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramConst;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.CommuhashNormalForm;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.Substitution;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.arrays.MultiDimensionalSort;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.linearterms.AffineTerm;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.linearterms.AffineTermTransformer;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/**
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
public class EqNodeAndFunctionFactory extends AbstractNodeAndFunctionFactory<EqNode, Term> {

	private final IUltimateServiceProvider mServices;
	private final ManagedScript mMgdScript;
	private final Set<Term> mNonTheoryLiteralTerms;

	private final Map<Term, EqNode> mTermToEqNode = new HashMap<>();
	private final Map<Term, Term> mNormalizationCache = new HashMap<>();
	private final List<String> mTrackedArraySubstrings;
	private final Set<String> mMixArrayFunctions;

	public EqNodeAndFunctionFactory(final IUltimateServiceProvider services, final ManagedScript script,
			final Set<IProgramConst> additionalLiterals, final List<String> trackedArraySubstrings,
			final Set<String> mixArrayFunctions) {
		mServices = services;
		mMgdScript = script;
		mNonTheoryLiteralTerms = additionalLiterals.stream().map(pc -> pc.getTerm()).collect(Collectors.toSet());
		mTrackedArraySubstrings = trackedArraySubstrings;
		mMixArrayFunctions = mixArrayFunctions;
	}

	public ManagedScript getScript() {
		return mMgdScript;
	}

	@Override
	public EqNode getOrConstructNode(final Term term) {
		if (isConstantArray(term)) {
			return getOrConstructConstantArray(term);
		} else if (isMixArray(term)) {
			return getOrConstructMixArray(term);
		} else if (SmtUtils.isFunctionApplication(term, "select")) {
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
			result = getBaseElement(normalizedTerm, false);
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
			result = getBaseElement(normalizedTerm, isTermALiteral(normalizedTerm));
			mTermToEqNode.put(normalizedTerm, result);
		}
		assert result instanceof EqAtomicBaseNode;
		return result;

	}

	private Term normalizeTerm(final Term term) {
		if (term instanceof TermVariable) {
			return term;
		}
		Term result = mNormalizationCache.get(term);
		if (result != null) {
			return result;
		}

		mMgdScript.lock(this);
		final AffineTerm affineTerm = (AffineTerm) new AffineTermTransformer(mMgdScript.getScript()).transform(term);
		mMgdScript.unlock(this);

		if (affineTerm.isErrorTerm()) {
			result = new CommuhashNormalForm(mServices, mMgdScript.getScript()).transform(term);
		} else {
			result = affineTerm.toTerm(mMgdScript.getScript());
		}
		mNormalizationCache.put(term, result);
		return result;

	}

	@Override
	public boolean hasNode(final Term term) {
		return mTermToEqNode.get(normalizeTerm(term)) != null;
	}

	/**
	 *
	 * @param term
	 * @return
	 */
	@Override
	public EqNode getExistingNode(final Term term) {
		final EqNode result = mTermToEqNode.get(normalizeTerm(term));
		return result;
	}

	/**
	 * Checks if the given term is a literal. Examples of literals (sometimes called
	 * constants, but we have other uses for that word) are: 1, 2, -1, true, false,
	 * 1bv16 (bitvector constant/literal)
	 *
	 * The defining trait of literals for our purposes is that two different
	 * literals always have a different value.
	 *
	 * @param term
	 * @return
	 */
	private boolean isTermALiteral(final Term term) {
		if (term instanceof TermVariable) {
			return false;
		}
		if (SmtUtils.isTrueLiteral(term) || SmtUtils.isFalseLiteral(term)) {
			return true;
		}
		if (term instanceof ConstantTerm) {
			return true;
		}

		if (mNonTheoryLiteralTerms.contains(term)) {
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
	 * We call a Term atomic here if it is either a TermVariable, or does not
	 * contain any TermVariables. (this has nothing to do with Boolean atoms)
	 *
	 * Explanation: Atomic in this sense means dependency-free. I.e.: if we havoc
	 * some other term (a TermVariable), can we guarantee that this term is not
	 * concerned by that.
	 *
	 * @param term
	 * @return
	 */
	private boolean isAtomic(final Term term) {
		return term instanceof TermVariable || term.getFreeVars().length == 0;
	}

	@Override
	protected EqNode newBaseElement(final Term term, final boolean isLiteral) {
		// no constant array, "normal case"
		if (isAtomic(term)) {
			// term has no dependencies on other terms --> use an EqAtomicBaseNode
			// return new EqAtomicBaseNode(term, isTermALiteral(term), this);
			return new EqAtomicBaseNode(term, isLiteral, this, dependsOnUntrackedArray(term));
		} else {
			assert !isLiteral;
			assert term.getFreeVars().length > 0;
			final Set<EqNode> supportingNodes = new HashSet<>();
			for (final TermVariable fv : term.getFreeVars()) {
				supportingNodes.add(getOrConstructNode(fv));
			}
			return new EqNonAtomicBaseNode(term, supportingNodes, this, dependsOnUntrackedArray(term));
		}
	}

	private boolean isConstantArray(final Term term) {
		if (!term.getSort().isArraySort()) {
			return false;
		}
		if (!(term instanceof ApplicationTerm)) {
			return false;
		}

		final ApplicationTerm at = (ApplicationTerm) term;

		final Term def = at.getFunction().getDefinition();
		if (def != null) {
			return isConstantArray(def);
		}

		if (at.getFunction().getName().equals("const")) {
			return true;
		}
		return false;
	}

	private boolean isMixArray(final Term term) {
		if (!term.getSort().isArraySort()) {
			return false;
		}
		if (!(term instanceof ApplicationTerm)) {
			return false;
		}

		final ApplicationTerm at = (ApplicationTerm) term;

		final Term def = at.getFunction().getDefinition();
		if (def != null) {
			return isMixArray(def);
		}

		if (mMixArrayFunctions.contains(at.getFunction().getName())) {
			return true;
		}
		return false;
	}

	private EqMixArrayNode getOrConstructMixArray(final Term term) {
		assert isMixArray(term);
		final EqNode result = mTermToEqNode.get(term);
		if (result != null) {
			return (EqMixArrayNode) result;
		}

		final ApplicationTerm at = (ApplicationTerm) term;

		final Term def = at.getFunction().getDefinition();
		if (def != null) {
			throw new AssertionError("not yet implemented");
//			assert at.getParameters().length == 3;
//			// we need to substitute the variable in the definition by the argument of at
//			final TermVariable var = at.getFunction().getDefinitionVars()[0];
//			final Term value = at.getParameters()[0];
//			final Term defSubstituted =
//					new Substitution(mMgdScript, Collections.singletonMap(var, value)).transform(def);
//
//			return getOrConstructMixArray(defSubstituted);
		}

		/*
		 * expecting this to have the form (mix-Array.. a b nondet) where nondet is an array with boolean value type
		 * that is unconstrained (it being constrained would not make our treatment unsound, though..)
		 */
		assert at.getParameters().length == 3;
		assert at.getParameters()[2].getSort().isArraySort()
			&& new MultiDimensionalSort(at.getParameters()[2].getSort()).getArrayValueSort().getName().equals("Bool");
		assert mMixArrayFunctions.contains(at.getFunction().getName());

		final EqNode array1 = getOrConstructNode(at.getParameters()[0]);
		final EqNode array2 = getOrConstructNode(at.getParameters()[1]);

		final EqMixArrayNode newMixArrayNode = new EqMixArrayNode(term, this, array1, array2);
		mTermToEqNode.put(term, newMixArrayNode);
		return newMixArrayNode;
	}

	private EqConstantArrayNode getOrConstructConstantArray(final Term term) {
		assert isConstantArray(term);
		final EqNode result = mTermToEqNode.get(term);
		if (result != null) {
			return (EqConstantArrayNode) result;
		}

		final ApplicationTerm at = (ApplicationTerm) term;

		final Term def = at.getFunction().getDefinition();
		if (def != null) {
			assert at.getParameters().length == 1;
			// we need to substitute the variable in the definition by the argument of at
			final TermVariable var = at.getFunction().getDefinitionVars()[0];
			final Term value = at.getParameters()[0];
			final Term defSubstituted =
					new Substitution(mMgdScript, Collections.singletonMap(var, value)).transform(def);

			return getOrConstructConstantArray(defSubstituted);
		}

		// TODO: define this string somewhere (also occurs in SolverBuilder, currently)
		assert at.getFunction().getName().equals("const");

		final EqNode value = getOrConstructNode(at.getParameters()[0]);
		final EqConstantArrayNode newConstArrayNode = new EqConstantArrayNode(term, this, value);
		mTermToEqNode.put(term, newConstArrayNode);
		return newConstArrayNode;
	}

	private boolean dependsOnUntrackedArray(final Term term) {
		if (mTrackedArraySubstrings == null) {
			return false;
		}

		if (SmtUtils.isFunctionApplication(term, "select")) {
			return dependsOnUntrackedArray(((ApplicationTerm) term).getParameters()[0]);
		}
		if (term.getSort().isArraySort() && (SmtUtils.isConstant(term) || term instanceof TermVariable)) {
			for (final String s : mTrackedArraySubstrings) {
				if (term.toString().contains(s)) {
					return false;
				}
			}
			return true;
		}
		return false;
	}

	@Override
	protected EqNode newFuncAppElement(final EqNode func, final EqNode arg) {
		final Term selectTerm = buildSelectTerm(func, arg);
		return new EqFunctionApplicationNode(func, arg, selectTerm, this, dependsOnUntrackedArray(selectTerm));
	}

	private Term buildSelectTerm(final EqNode func, final EqNode arg) {
		mMgdScript.lock(this);
		final Term selectTerm = mMgdScript.term(this, "select", func.getTerm(), arg.getTerm());
		mMgdScript.unlock(this);
		return selectTerm;
	}

	/**
	 * Determines if a given term should get a node with or without the isFunction
	 * flag set.
	 *
	 * @param term
	 * @return
	 */
	boolean isFunction(final Term term) {
		return term.getSort().isArraySort();
	}

	public Set<Term> getNonTheoryLiterals() {
		return Collections.unmodifiableSet(mNonTheoryLiteralTerms);
	}

	@Override
	public Term getNonTheoryLiteralDisequalities() {
		return SmtUtils.and(mMgdScript.getScript(), CongruenceClosureSmtUtils
				.createDisequalityTermsForNonTheoryLiterals(mMgdScript.getScript(), getNonTheoryLiterals()));
	}
}
