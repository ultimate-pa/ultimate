package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.linearterms;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.Substitution;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.linearterms.QuantifierSequence.QuantifiedVariables;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation3;

/**
 * Takes a formula in prenex normal form (see {@link PrenexNormalForm}) and computes a formula in Skolem normal
 * form.
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
public class SkolemNormalForm  {

	private Term mResult;
	private final ManagedScript mMgdScript;

	private final HashRelation3<String, Sort[], Sort> mSkolemFunctions;

	public SkolemNormalForm(final ManagedScript mgdScript, final Term inputFormula) {
		mMgdScript = mgdScript;
		mSkolemFunctions = new HashRelation3<>();

		assert new PrenexNormalForm(mgdScript).transform(inputFormula) == inputFormula : "input formula must be in "
				+ "prenex normal form";

		if (!(inputFormula instanceof QuantifiedFormula)) {
			mResult = inputFormula;
		} else {
			skolemize((QuantifiedFormula) inputFormula);
		}
	}

	private void skolemize(final QuantifiedFormula inputFormula) {

		mMgdScript.lock(this);

		final QuantifierSequence qs = new QuantifierSequence(mMgdScript.getScript(), inputFormula);

		final Map<Term, Term> substitutionMapping = new HashMap<>();

		QuantifiedVariables universalQuantifiersInScope =
				new QuantifiedVariables(QuantifiedFormula.FORALL, Collections.emptySet());

		for (final QuantifiedVariables qb : qs.getQuantifierBlocks()) {
			if (qb.getQuantifier() == QuantifiedFormula.FORALL) {
				universalQuantifiersInScope =
						new QuantifiedVariables(QuantifiedFormula.FORALL,
								DataStructureUtils.union(qb.getVariables(),
										universalQuantifiersInScope.getVariables()));
			} else {
				// qb.getQuantifier() == QuantifiedFormula.EXISTS
				final List<TermVariable> universalVars =  new ArrayList<>(universalQuantifiersInScope.getVariables());
				final Term[] universalVarsArray =
						universalVars.toArray(new Term[universalVars.size()]);

				final List<Sort> paramSortList = universalVars.stream()
						.map(tv -> tv.getSort())
						.collect(Collectors.toList());
				final Sort[] paramSorts = paramSortList.toArray(new Sort[paramSortList.size()]);
				for (final TermVariable existVar : qb.getVariables()) {
					final Sort resultSort = existVar.getSort();

					final String skolemFunctionName =
							getFreshFunctionSymbol(paramSorts, resultSort);
					mMgdScript.declareFun(this, skolemFunctionName, paramSorts, resultSort);

					final Term ufAppTerm = mMgdScript.term(this, skolemFunctionName, universalVarsArray);
					substitutionMapping.put(existVar, ufAppTerm);
				}
			}
		}

		final Term newInnerTerm = new Substitution(mMgdScript, substitutionMapping).transform(qs.getInnerTerm());

		if (universalQuantifiersInScope.getVariables().isEmpty()) {
			mResult = newInnerTerm;
		} else {
			try {
				mResult = QuantifierSequence.prependQuantifierSequence(mMgdScript.getScript(),
						Collections.singletonList(universalQuantifiersInScope), newInnerTerm);
			} catch (final Exception ex) {
				throw new AssertionError();
			}
		}

		mMgdScript.unlock(this);
	}

	String getFreshFunctionSymbol(final Sort[] parameterSorts, final Sort resultSort) {
		final String name = mMgdScript.constructFreshSkolemFunctionName(parameterSorts, resultSort);
		mSkolemFunctions.addTriple(name, parameterSorts, resultSort);
		return name;
	}

	/**
	 *
	 * @return skolemized formula
	 */
	public Term getSkolemizedFormula() {
		return mResult;
	}

	/**
	 * @return all Skolem functions that have been introduced by this transformation
	 */
	public HashRelation3<String, Sort[], Sort> getSkolemFunctions() {
		return mSkolemFunctions;
	}

}
