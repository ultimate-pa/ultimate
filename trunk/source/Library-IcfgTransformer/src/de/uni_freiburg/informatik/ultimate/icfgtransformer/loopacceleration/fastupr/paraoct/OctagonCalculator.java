package de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.fastupr.paraoct;

import java.math.BigDecimal;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.fastupr.FastUPRUtils;
import de.uni_freiburg.informatik.ultimate.logic.NonRecursive;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;

public class OctagonCalculator extends NonRecursive {

	FastUPRUtils mUtils;
	ManagedScript mManagedScript;

	public OctagonCalculator(final FastUPRUtils utils, final ManagedScript mgdScript) {
		mUtils = utils;
		mManagedScript = mgdScript;
	}

	public OctagonConjunction normalizeVarNames(final OctagonConjunction conjunc, final Map<IProgramVar, TermVariable> inVars,
			final Map<IProgramVar, TermVariable> outVars) {

		mUtils.debug("Normalizing VarNames for:");
		mUtils.debug(conjunc.toString());

		OctagonConjunction result = conjunc;

		final Sort intSort = SmtSortUtils.getIntSort(mManagedScript);
		for (final IProgramVar p : inVars.keySet()) {
			String name;
			if (outVars.get(p).equals(inVars.get(p))) {
				name = "oct_" + p.toString() + "_inout";
				final TermVariable newVar = mManagedScript.constructFreshTermVariable(name,
						intSort);
				result = replaceVars(result, inVars.get(p), newVar);
				inVars.put(p, newVar);
				outVars.put(p, newVar);
			} else {
				name = "oct_" + p.toString() + "_in";
				final TermVariable newVar = mManagedScript.constructFreshTermVariable(name,
						intSort);
				result = replaceVars(result, inVars.get(p), newVar);
				inVars.put(p, newVar);
			}
			mUtils.debug(inVars.toString());
		}

		for (final IProgramVar p : outVars.keySet()) {
			if (!outVars.get(p).equals(inVars.get(p))) {
				final String name = "oct_" + p.toString() + "_out";
				final TermVariable newVar = mManagedScript.constructFreshTermVariable(name,
						intSort);
				result = replaceVars(result, outVars.get(p), newVar);
				outVars.put(p, newVar);
			}
		}
		mUtils.debug(result.toString());
		return result;
	}

	private OctagonConjunction replaceVars(final OctagonConjunction conjunc, final TermVariable oldVar, final TermVariable newVar) {

		mUtils.debug("Replacing " + oldVar.toString() + " with " + newVar.toString());

		final OctagonConjunction result = new OctagonConjunction();

		for (final OctagonTerm t : conjunc.getTerms()) {

			mUtils.debug("Replacing in:");
			mUtils.debug(t.toString());

			boolean replaceFirst = false;
			boolean replaceSecond = false;

			if (t.getFirstVar().equals(oldVar)) {
				mUtils.debug(t.getFirstVar().toString() + " = " + oldVar.toString());
				replaceFirst = true;
			}

			if (t.getSecondVar().equals(oldVar)) {
				mUtils.debug(t.getSecondVar().toString() + " = " + oldVar.toString());
				replaceSecond = true;
			}

			if (t instanceof OneVarOctTerm) {
				final OneVarOctTerm newTerm = new OneVarOctTerm((BigDecimal) t.getValue(),
						(replaceFirst ? newVar : t.getFirstVar()), t.isFirstNegative());
				result.addTerm(newTerm);
				mUtils.debug(newTerm.toString());
			} else if (t instanceof TwoVarOctTerm) {
				final TwoVarOctTerm newTerm = new TwoVarOctTerm((BigDecimal) t.getValue(),
						(replaceFirst ? newVar : t.getFirstVar()), t.isFirstNegative(),
						(replaceSecond ? newVar : t.getSecondVar()), t.isSecondNegative());
				result.addTerm(newTerm);
				mUtils.debug(newTerm.toString());
			}
			mUtils.debug(">> replaced.");
		}

		mUtils.debug(">>> All replaced.");
		return result;
	}

	public OctagonConjunction sequentialize(final OctagonConjunction conjunc, final Map<IProgramVar, TermVariable> inVars,
			final Map<IProgramVar, TermVariable> outVars, final int count) {

		mUtils.debug("Sequentializing " + count + " times:" + conjunc.toString());

		final HashSet<TermVariable> variables = new HashSet<>();
		final HashSet<TermVariable> inVarSet = new HashSet<>();
		final HashSet<TermVariable> outVarSet = new HashSet<>();

		getVariableSets(inVarSet, outVarSet, variables, inVars, outVars);

		OctagonConjunction result = conjunc;

		mUtils.debug("> Getting Variable Mapping:");
		mUtils.debug("inVars: " + inVars.toString());
		mUtils.debug("outVars: " + outVars.toString());

		final Map<TermVariable, TermVariable> termMapping = getTermMapping(inVars, outVars);
		final Map<TermVariable, TermVariable> reverseTermMapping = getReverseTermMapping(termMapping);

		mUtils.debug(termMapping.toString());

		for (int i = 0; i < count - 1; i++) {
			mUtils.debug("Binary Sequentialize > " + (i + 1));
			result = binarySequentialize(result, conjunc, variables, inVarSet, outVarSet, reverseTermMapping);
			mUtils.debug(result.toString());
		}

		mUtils.debug("Result: " + result.toString());

		return result;
	}

	public void getVariableSets(HashSet<TermVariable> inVarSet, HashSet<TermVariable> outVarSet,
			HashSet<TermVariable> variableSet, final Map<IProgramVar, TermVariable> inVarMap,
			final Map<IProgramVar, TermVariable> outVarMap) {

		variableSet = new HashSet<>();
		inVarSet = new HashSet<>();
		outVarSet = new HashSet<>();

		for (final IProgramVar p : inVarMap.keySet()) {
			variableSet.add(inVarMap.get(p));
			inVarSet.add(inVarMap.get(p));
		}

		for (final IProgramVar p : outVarMap.keySet()) {
			variableSet.add(outVarMap.get(p));
			if (inVarSet.contains(outVarMap.get(p))) {
				inVarSet.remove(outVarMap.get(p));
			} else {
				outVarSet.add(outVarMap.get(p));
			}
		}
	}

	public OctagonConjunction binarySequentialize(final OctagonConjunction first, final OctagonConjunction second,
			final Map<IProgramVar, TermVariable> inVars, final Map<IProgramVar, TermVariable> outVars) {
		final HashSet<TermVariable> variables = new HashSet<>();
		final HashSet<TermVariable> inVarSet = new HashSet<>();
		final HashSet<TermVariable> outVarSet = new HashSet<>();

		getVariableSets(inVarSet, outVarSet, variables, inVars, outVars);

		final Map<TermVariable, TermVariable> termMapping = getTermMapping(inVars, outVars);
		final Map<TermVariable, TermVariable> reverseTermMapping = getReverseTermMapping(termMapping);

		return binarySequentialize(first, second, variables, inVarSet, outVarSet, reverseTermMapping);

	}

	OctagonConjunction binarySequentialize(final OctagonConjunction first, OctagonConjunction second,
			final HashSet<TermVariable> variables, final HashSet<TermVariable> inVarSet, final HashSet<TermVariable> outVarSet,
			final Map<TermVariable, TermVariable> variableMapping) {

		final Map<TermVariable, OctagonSubstitution> firstSubstitutions = new HashMap<>();
		final Map<TermVariable, OctagonSubstitution> secondSubstitutions = new HashMap<>();
		HashSet<SubstitutionTermContainer> firstContainers = new HashSet<>();
		HashSet<SubstitutionTermContainer> secondContainers = new HashSet<>();

		for (final TermVariable t : outVarSet) {
			firstSubstitutions.put(t, getSubstitution(t, first));
			secondSubstitutions.put(t, getSubstitution(t, second));
		}

		mUtils.debug(firstSubstitutions.toString());
		mUtils.debug(secondSubstitutions.toString());

		secondContainers = getContainers(second);
		firstContainers = getContainers(first);

		secondContainers = substituteInVars(secondContainers, inVarSet, variableMapping);

		mUtils.debug("> Result:");
		mUtils.debug(secondContainers.toString());

		second = substitute(secondContainers, outVarSet, firstSubstitutions);

		mUtils.debug(second.toString());

		// first = substitute(firstContainers, outVarSet, firstSubstitutions);

		mUtils.debug(">> Substitutions finished.");
		final OctagonConjunction inputConstraints = getInputConstraints(first, inVarSet);
		mUtils.debug(inputConstraints.toString());
		final OctagonConjunction result = conjunction(inputConstraints, second);

		return second;
	}

	private OctagonConjunction getInputConstraints(final OctagonConjunction first, final HashSet<TermVariable> inVarSet) {
		final OctagonConjunction result = new OctagonConjunction();
		for (final OctagonTerm t : first.getTerms()) {
			if (inVarSet.contains(t.getFirstVar()) && inVarSet.contains(t.getSecondVar())) {
				result.addTerm(t);
			}
		}
		return result;
	}

	private HashSet<SubstitutionTermContainer> getContainers(final OctagonConjunction second) {
		final HashSet<SubstitutionTermContainer> result = new HashSet<>();
		for (final OctagonTerm t : second.getTerms()) {
			result.add(new SubstitutionTermContainer(t));
		}
		return result;
	}

	private HashSet<SubstitutionTermContainer> substituteInVars(final HashSet<SubstitutionTermContainer> terms,
			final HashSet<TermVariable> varSet, final Map<TermVariable, TermVariable> variableMapping) {

		mUtils.debug("> Subsituting inVars with outVars");
		mUtils.debug("Variable Set: " + varSet.toString());
		mUtils.debug("Variable Mapping: " + variableMapping.toString());

		final HashSet<SubstitutionTermContainer> result = new HashSet<>();

		mUtils.debug(terms.toString());

		for (final SubstitutionTermContainer c : terms) {

			mUtils.debug("test");

			final OctagonTerm t = c.getTerm();

			SubstitutionTermContainer container = null;
			OctagonTerm newTerm = null;

			mUtils.debug("Replacing in Term:" + t.toString());

			if (t instanceof OneVarOctTerm) {

				TermVariable firstVar = t.getFirstVar();
				if (varSet.contains(firstVar)) {
					firstVar = variableMapping.get(firstVar);
				}
				newTerm = new OneVarOctTerm((BigDecimal) t.getValue(), firstVar, t.isFirstNegative());
				mUtils.debug("New Term:" + newTerm.toString());
				container = new SubstitutionTermContainer(newTerm, false);
			} else {
				TermVariable firstVar = t.getFirstVar();
				TermVariable secondVar = t.getSecondVar();
				boolean firstLocked = true;
				boolean secondLocked = true;

				if (varSet.contains(firstVar)) {
					firstVar = variableMapping.get(firstVar);
					firstLocked = false;
				}
				if (varSet.contains(secondVar)) {
					secondVar = variableMapping.get(secondVar);
					secondLocked = false;
				}
				newTerm = new TwoVarOctTerm((BigDecimal) t.getValue(), firstVar, t.isFirstNegative(), secondVar,
						t.isSecondNegative());
				mUtils.debug("New Term:" + newTerm.toString());
				container = new SubstitutionTermContainer(newTerm, firstLocked, secondLocked);

			}

			result.add(container);
		}

		mUtils.debug("Variables substituted.");

		return result;
	}

	private OctagonConjunction substitute(final HashSet<SubstitutionTermContainer> terms, final HashSet<TermVariable> varSet,
			final Map<TermVariable, OctagonSubstitution> substitutions) {

		mUtils.debug("> Substituting a set of variables.");
		mUtils.debug("varSet:" + varSet.toString());

		final OctagonConjunction result = new OctagonConjunction();
		final HashSet<OctagonTerm> resultSet = new HashSet<>();

		for (final SubstitutionTermContainer c : terms) {

			final OctagonTerm t = c.getTerm();
			mUtils.debug("-Substituting in: " + t.toString());
			mUtils.debug(c.isFirstLocked());

			if (varSet.contains(t.getFirstVar()) && !c.isFirstLocked()) {

				if (t instanceof TwoVarOctTerm && varSet.contains(t.getSecondVar()) && !c.isSecondLocked()) {
					resultSet.addAll(getTermSubstitutions(t, substitutions, 0));
				} else {
					resultSet.addAll(getTermSubstitutions(t, substitutions, 1));
				}
			} else if (varSet.contains(t.getSecondVar()) && !c.isSecondLocked()) {
				resultSet.addAll(getTermSubstitutions(t, substitutions, 2));
			} else {
				resultSet.add(t);
			}
		}

		for (final OctagonTerm t : resultSet) {
			result.addTerm(t);
		}

		return result;
	}

	private HashSet<OctagonTerm> getTermSubstitutions(final OctagonTerm t,
			final Map<TermVariable, OctagonSubstitution> substitutions, final int which) {

		final HashSet<OctagonTerm> result = new HashSet<>();

		if (which != 0) {
			final TermVariable toReplace = (which == 1 ? t.getFirstVar() : t.getSecondVar());
			final boolean negative = (which == 1 ? t.isFirstNegative() : t.isSecondNegative());

			mUtils.debug("Variable " + which + ": " + toReplace.toString());

			HashSet<OctagonSubstitutionTerm> subs = null;

			if (negative) {
				subs = substitutions.get(toReplace).getLesserSubsitutions();
			} else {
				subs = substitutions.get(toReplace).getGreaterSubsitutions();
			}

			mUtils.debug("Substitutions: " + subs.toString());

			for (final OctagonSubstitutionTerm sub : subs) {
				final OctagonTerm newTerm = getTermFromSubsitution(t, toReplace, sub, which);
				if (!newTerm.equals(null)) {
					result.add(newTerm);
				}
			}

		} else {

			// If both firstVar and secondVar need to be substituted.

			final TermVariable replaceFirst = t.getFirstVar();
			final TermVariable replaceSecond = t.getSecondVar();
			final boolean firstNegative = t.isFirstNegative();
			final boolean secondNegative = t.isSecondNegative();

			mUtils.debug(replaceFirst.toString() + " and " + replaceSecond.toString());

			HashSet<OctagonSubstitutionTerm> subs = null;
			final HashSet<OctagonTerm> tempResults = new HashSet<>();

			if (firstNegative) {
				subs = substitutions.get(replaceFirst).getLesserSubsitutions();
			} else {
				subs = substitutions.get(replaceFirst).getGreaterSubsitutions();
			}

			// Build temporary Terms substituting only the first Variable.

			for (final OctagonSubstitutionTerm sub : subs) {
				final OctagonTerm newTerm = getTermFromSubsitution(t, replaceFirst, sub, 1);
				if (!newTerm.equals(null)) {
					tempResults.add(newTerm);
				}
			}

			if (secondNegative) {
				subs = substitutions.get(replaceSecond).getLesserSubsitutions();
			} else {
				subs = substitutions.get(replaceSecond).getGreaterSubsitutions();
			}

			// For each temporary Term substitute the second Variable.

			for (final OctagonTerm tempTerm : tempResults) {
				for (final OctagonSubstitutionTerm sub : subs) {
					final OctagonTerm newTerm = getTermFromSubsitution(tempTerm, replaceSecond, sub, 2);
					if (!newTerm.equals(null)) {
						result.add(newTerm);
					}
				}

			}

		}
		return result;
	}

	private OctagonTerm getTermFromSubsitution(final OctagonTerm t, final TermVariable toReplace, final OctagonSubstitutionTerm sub,
			final int which) {

		mUtils.debug("-Building new substituted Term from " + t.toString() + " with substitution " + sub.toString());

		OctagonTerm result = null;

		if (t instanceof OneVarOctTerm) {
			if (sub.isZeroVar()) {
				result = null;
			} else {
				result = new OneVarOctTerm(((BigDecimal) t.getValue()).add(sub.getValue().multiply(new BigDecimal(2))),
						sub.getVar(), sub.isVarNegative());
			}

		} else {
			if (sub.isZeroVar()) {
				result = new OneVarOctTerm(((BigDecimal) t.getValue()).add(sub.getValue()),
						(which == 1 ? t.getSecondVar() : t.getFirstVar()),
						(which == 1 ? t.isSecondNegative() : t.isFirstNegative()));
			} else {
				result = new TwoVarOctTerm(((BigDecimal) t.getValue()).add(sub.getValue()),
						(which == 1 ? t.getSecondVar() : t.getFirstVar()),
						(which == 1 ? t.isSecondNegative() : t.isFirstNegative()), sub.getVar(), sub.isVarNegative());
			}
		}

		mUtils.debug("-Result: " + result.toString());
		return result;
	}

	private OctagonConjunction conjunction(final OctagonConjunction first, final OctagonConjunction second) {
		final OctagonConjunction result = new OctagonConjunction();
		for (final OctagonTerm t : first.getTerms()) {
			result.addTerm(t);
		}

		for (final OctagonTerm t : second.getTerms()) {
			result.addTerm(t);
		}

		return result;
	}

	private Map<TermVariable, TermVariable> getTermMapping(final Map<IProgramVar, TermVariable> inVars,
			final Map<IProgramVar, TermVariable> outVars) {

		final Map<TermVariable, TermVariable> result = new HashMap<>();

		for (final IProgramVar p : outVars.keySet()) {
			final TermVariable outVar = outVars.get(p);
			final TermVariable inVar = inVars.get(p);
			if (outVar != null && inVar != null) {
				result.put(outVar, inVar);
			}
		}
		return result;
	}

	public Map<TermVariable, TermVariable> getReverseTermMapping(final Map<TermVariable, TermVariable> termMapping) {
		final Map<TermVariable, TermVariable> result = new HashMap<>();
		for (final TermVariable t : termMapping.keySet()) {
			result.put(termMapping.get(t), t);
		}

		return result;
	}

	private OctagonSubstitution getSubstitution(final TermVariable var, final OctagonConjunction conjunc) {
		final OctagonSubstitution result = new OctagonSubstitution(var);
		for (final OctagonTerm t : conjunc.getTerms()) {
			result.addSubstitution(t);
		}
		return result;

	}

	private class OctagonSubstitution {
		private final TermVariable mVar;
		private final HashSet<OctagonSubstitutionTerm> mGreaterEqThan;
		private final HashSet<OctagonSubstitutionTerm> mLesserEqThan;

		OctagonSubstitution(final TermVariable var) {
			mVar = var;
			mGreaterEqThan = new HashSet<>();
			mLesserEqThan = new HashSet<>();
		}

		void addSubstitution(final OctagonTerm term) {
			if (term.getFirstVar().equals(mVar)) {
				addSubstitution(term, true);
			} else if (term.getSecondVar().equals(mVar)) {
				addSubstitution(term, false);
			}
		}

		void addSubstitution(final OctagonTerm term, final boolean first) {

			OctagonSubstitutionTerm subTerm;
			boolean greater = false;

			if (first) {
				if (term instanceof OneVarOctTerm) {
					subTerm = new OctagonSubstitutionTerm((BigDecimal) term.getValue());
				} else {
					subTerm = new OctagonSubstitutionTerm((BigDecimal) term.getValue(), term.getSecondVar(),
							term.isSecondNegative());
				}
				if (term.isFirstNegative()) {
					greater = true;
				}
			} else {
				subTerm = new OctagonSubstitutionTerm((BigDecimal) term.getValue(), term.getFirstVar(),
						term.isFirstNegative());
				if (term.isSecondNegative()) {
					greater = true;
				}
			}

			addSubstitution(subTerm, greater);
		}

		void addSubstitution(final OctagonSubstitutionTerm term, final boolean greater) {
			if (greater) {
				mGreaterEqThan.add(term);
			} else {
				mLesserEqThan.add(term);
			}
		}

		HashSet<OctagonSubstitutionTerm> getGreaterSubsitutions() {
			return mGreaterEqThan;
		}

		HashSet<OctagonSubstitutionTerm> getLesserSubsitutions() {
			return mLesserEqThan;
		}

		@Override
		public String toString() {
			String result = " > Substitution for " + mVar.toString() + ":\n";
			result = result + ("Greater Equal Than: ");
			for (final OctagonSubstitutionTerm t : mGreaterEqThan) {
				result = result + (t.toString() + "; ");
			}
			result = result + ("\nLesser Equal Than: ");
			for (final OctagonSubstitutionTerm t : mLesserEqThan) {
				result = result + (t.toString() + "; ");
			}
			result = result + "\n";
			return result;
		}
	}

	private class OctagonSubstitutionTerm {
		private final TermVariable mVar;
		private final boolean mNegativeVar;
		private final BigDecimal mConstant;

		OctagonSubstitutionTerm(final BigDecimal constant) {
			this(constant, null, true);
		}

		public BigDecimal getValue() {
			return mConstant;
		}

		OctagonSubstitutionTerm(final BigDecimal constant, final TermVariable var, final boolean negative) {
			mConstant = constant;
			mVar = var;
			mNegativeVar = negative;
		}

		boolean isZeroVar() {
			return mVar.equals(null);
		}

		boolean isVarNegative() {
			return mNegativeVar;
		}

		TermVariable getVar() {
			return mVar;
		}

		@Override
		public String toString() {
			return (mVar.equals(null) ? mConstant.toString()
					: (mNegativeVar ? "-" + mVar.toString() : mVar.toString()) + ", " + mConstant.toString());
		}
	}

	private class SubstitutionTermContainer {
		private final OctagonTerm mTerm;
		private final boolean mFirstLocked;
		private final boolean mSecondLocked;

		SubstitutionTermContainer(final OctagonTerm term) {
			this(term, true, true);
		}

		SubstitutionTermContainer(final OctagonTerm term, final boolean locked) {
			this(term, locked, true);
		}

		SubstitutionTermContainer(final OctagonTerm term, final boolean first, final boolean second) {
			mTerm = term;
			mFirstLocked = first;
			mSecondLocked = second;
		}

		@Override
		public String toString() {
			return mTerm.toString();
		}

		OctagonTerm getTerm() {
			return mTerm;
		}

		boolean isFirstLocked() {
			return mFirstLocked;
		}

		boolean isSecondLocked() {
			return mSecondLocked;
		}
	}

	public ArrayList<TermVariable> getSortedVariables(final Map<IProgramVar, TermVariable> inVarMap,
			final Map<IProgramVar, TermVariable> outVarMap) {

		final ArrayList<TermVariable> sorted = new ArrayList<>();

		final HashSet<TermVariable> inVars = new HashSet<>();
		final HashSet<TermVariable> outVars = new HashSet<>();
		final HashSet<TermVariable> mixedVars = new HashSet<>();

		for (final IProgramVar p : inVarMap.keySet()) {
			inVars.add(inVarMap.get(p));
		}
		for (final IProgramVar p : outVarMap.keySet()) {
			if (!inVars.contains(outVarMap.get(p))) {
				outVars.add(outVarMap.get(p));
			} else {
				inVars.remove(outVarMap.get(p));
				mixedVars.add(outVarMap.get(p));
			}
		}

		final List<TermVariable> inVarList = new ArrayList<>(inVars);
		final List<TermVariable> outVarList = new ArrayList<>(outVars);
		final List<TermVariable> mixedVarList = new ArrayList<>(mixedVars);

		final Comparator<TermVariable> compare = new Comparator<TermVariable>() {
			@Override
			public int compare(final TermVariable one, final TermVariable other) {
				return one.toString().compareTo(other.toString());
			}
		};

		Collections.sort(inVarList, compare);
		Collections.sort(mixedVarList, compare);
		Collections.sort(outVarList, compare);

		inVarList.addAll(mixedVarList);
		inVarList.addAll(outVarList);

		sorted.addAll(inVarList);

		return sorted;
	}
}
