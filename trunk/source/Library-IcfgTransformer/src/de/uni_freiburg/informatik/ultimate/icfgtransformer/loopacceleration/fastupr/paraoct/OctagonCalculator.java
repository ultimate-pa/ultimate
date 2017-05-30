package de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.fastupr.paraoct;

import java.math.BigDecimal;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.fastupr.FastUPRUtils;
import de.uni_freiburg.informatik.ultimate.logic.NonRecursive;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;

/**
 * Class to rename variables and calculate sequential composition of
 * OctagonConjunctions.
 */
public class OctagonCalculator extends NonRecursive {

	private final FastUPRUtils mUtils;
	private final ManagedScript mManagedScript;

	/**
	 *
	 * @param utils
	 * @param mgdScript
	 */
	public OctagonCalculator(FastUPRUtils utils, ManagedScript mgdScript) {
		mUtils = utils;
		mManagedScript = mgdScript;
	}

	/**
	 * Removes all Variables that are both inVars and outVars. All occurences in
	 * Terms are replaced with a fresh inVar and two new Terms are created to
	 * make a fresh outVar = inVar.
	 *
	 * @param conjunc
	 *            Conjunction to compute
	 * @param inVars
	 *            Mappings for InVars
	 * @param outVars
	 *            Mappings for OutVars
	 * @return OctagonConjunction without inOutVars.
	 */
	public OctConjunction removeInOutVars(OctConjunction conjunc, Map<IProgramVar, TermVariable> inVars,
			Map<IProgramVar, TermVariable> outVars) {
		OctConjunction result = conjunc;
		for (final Entry<IProgramVar, TermVariable> e : inVars.entrySet()) {
			if (outVars.containsValue(e.getValue())) {

				final String inName = "oct_" + e.getKey().toString() + "_in";
				final TermVariable inVar = mManagedScript.constructFreshTermVariable(inName,
						mManagedScript.getScript().sort("Int"));
				final String outName = "oct_" + e.getKey().toString() + "_out";
				final TermVariable outVar = mManagedScript.constructFreshTermVariable(outName,
						mManagedScript.getScript().sort("Int"));

				result = replaceInOutVars(result, e.getValue(), inVar);
				result = getInOutVarTerms(result, e.getValue(), inVar, outVar);
				inVars.put(e.getKey(), inVar);
				outVars.put(e.getKey(), outVar);

			}
		}
		return result;
	}

	private static OctConjunction getInOutVarTerms(OctConjunction conjunc, TermVariable value, TermVariable inVar,
			TermVariable outVar) {
		final OctConjunction result = conjunc;
		result.addTerm(OctagonFactory.createTwoVarOctTerm(BigDecimal.ZERO, inVar, false, outVar, true));
		result.addTerm(OctagonFactory.createTwoVarOctTerm(BigDecimal.ZERO, inVar, true, outVar, false));
		return result;
	}

	private static OctConjunction replaceInOutVars(OctConjunction conjunc, TermVariable inOutVar, TermVariable inVar) {
		final OctConjunction result = new OctConjunction();
		for (final OctTerm t : conjunc.getTerms()) {
			if (t.isOneVar() && t.getFirstVar().equals(inOutVar)) {
				result.addTerm(OctagonFactory.createOneVarOctTerm(t.getValue(), inVar, t.isFirstNegative()));
			} else if (t.getFirstVar().equals(inOutVar)) {
				result.addTerm(OctagonFactory.createTwoVarOctTerm(t.getValue(), inVar, t.isFirstNegative(),
						t.getSecondVar(), t.isSecondNegative()));
			} else if (t.getSecondVar().equals(inOutVar)) {
				result.addTerm(OctagonFactory.createTwoVarOctTerm(t.getValue(), t.getFirstVar(), t.isFirstNegative(),
						inVar, t.isSecondNegative()));
			} else {
				result.addTerm(t);
			}
		}
		return result;
	}

	/**
	 * Normalizes Varnames of given conjunction and also changes them in the
	 * given inVar and outVar Maps. InVars will be namend (varname)_in, OutVars
	 * (varname)_out, Variables that are InVars and OutVars (varname)_inout
	 *
	 * @param conjunc
	 *            Conjunction to compute
	 * @param inVars
	 *            Mappings for InVars
	 * @param outVars
	 *            Mappings for OutVars
	 * @return OctagonConjunction with changed names.
	 */
	public OctConjunction normalizeVarNames(OctConjunction conjunc, Map<IProgramVar, TermVariable> inVars,
			Map<IProgramVar, TermVariable> outVars) {

		mUtils.debug("Normalizing VarNames for:");
		mUtils.debug(conjunc.toString());

		OctConjunction result = conjunc;

		for (final IProgramVar p : inVars.keySet()) {
			String name;
			if (outVars.get(p).equals(inVars.get(p))) {
				name = "oct_" + p.toString() + "_inout";
				final TermVariable newVar = mManagedScript.constructFreshTermVariable(name,
						mManagedScript.getScript().sort("Int"));
				result = replaceVars(result, inVars.get(p), newVar);
				inVars.put(p, newVar);
				outVars.put(p, newVar);
			} else {
				name = "oct_" + p.toString() + "_in";
				final TermVariable newVar = mManagedScript.constructFreshTermVariable(name,
						mManagedScript.getScript().sort("Int"));
				result = replaceVars(result, inVars.get(p), newVar);
				inVars.put(p, newVar);
			}
			mUtils.debug(inVars.toString());
		}

		for (final IProgramVar p : outVars.keySet()) {
			if (!outVars.get(p).equals(inVars.get(p))) {
				final String name = "oct_" + p.toString() + "_out";
				final TermVariable newVar = mManagedScript.constructFreshTermVariable(name,
						mManagedScript.getScript().sort("Int"));
				result = replaceVars(result, outVars.get(p), newVar);
				outVars.put(p, newVar);
			}
		}
		mUtils.debug(result.toString());
		return result;
	}

	private OctConjunction replaceVars(OctConjunction conjunc, TermVariable oldVar, TermVariable newVar) {

		mUtils.debug("Replacing " + oldVar.toString() + " with " + newVar.toString());

		final OctConjunction result = new OctConjunction();

		for (final OctTerm t : conjunc.getTerms()) {

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

			if (t.isOneVar()) {
				final OctTerm newTerm = OctagonFactory.createOneVarOctTerm(t.getValue(),
						replaceFirst ? newVar : t.getFirstVar(), t.isFirstNegative());
				result.addTerm(newTerm);
				mUtils.debug(newTerm.toString());
			} else {
				final OctTerm newTerm = OctagonFactory.createTwoVarOctTerm(t.getValue(),
						replaceFirst ? newVar : t.getFirstVar(), t.isFirstNegative(),
						replaceSecond ? newVar : t.getSecondVar(), t.isSecondNegative());
				result.addTerm(newTerm);
				mUtils.debug(newTerm.toString());
			}
			mUtils.debug(">> replaced.");
		}

		mUtils.debug(">>> All replaced.");
		return result;
	}

	/**
	 * Caluclates the sequential composition of a given conjunction count times.
	 * (R^count)
	 *
	 * @param conjunc
	 *            Conjunction to sequentialize
	 * @param inVars
	 *            inVar Map of the Conjunction
	 * @param outVars
	 *            outVar Map of the Conjunction
	 * @param count
	 *            amount of compositions
	 * @return The composition as a new Conjunction
	 */
	public OctConjunction sequentialize(OctConjunction conjunc, Map<IProgramVar, TermVariable> inVars,
			Map<IProgramVar, TermVariable> outVars, int count) {

		mUtils.debug("Sequentializing " + count + " times:" + conjunc.toString());

		final HashSet<TermVariable> variables = new HashSet<>();
		final HashSet<TermVariable> inVarSet = new HashSet<>();
		final HashSet<TermVariable> outVarSet = new HashSet<>();

		getVariableSets(inVarSet, outVarSet, variables, inVars, outVars);

		OctConjunction result = conjunc;

		mUtils.debug("> Getting Variable Mapping:");
		mUtils.debug("inVars: " + inVars.toString());
		mUtils.debug("outVars: " + outVars.toString());

		final Map<TermVariable, TermVariable> termMapping = getTermMapping(inVars, outVars);
		final Map<TermVariable, TermVariable> reverseTermMapping = getReverseTermMapping(termMapping);

		mUtils.debug(termMapping.toString());

		for (int i = 0; i < count - 1; i++) {
			mUtils.debug("Binary Sequentialize > " + (i + 1));
			result = binarySequentialize(result, conjunc, inVarSet, outVarSet, reverseTermMapping);
			mUtils.debug(result.toString());
		}

		mUtils.debug("Result: " + result.toString());

		return result;
	}

	private static void getVariableSets(HashSet<TermVariable> inVarSet, HashSet<TermVariable> outVarSet,
			HashSet<TermVariable> variableSet, Map<IProgramVar, TermVariable> inVarMap,
			Map<IProgramVar, TermVariable> outVarMap) {

		variableSet.clear();
		inVarSet.clear();
		outVarSet.clear();

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

	/**
	 * Computes a sequential composition of two OctagonConjunction with the same
	 * inVars and outVars.
	 *
	 * @param first
	 *            first conjunction
	 * @param second
	 *            second conjunction
	 * @param inVars
	 *            inVar Map of both conjunctions
	 * @param outVars
	 *            outVar Map of both conjunctions
	 * @return Conjunction of the sequential composition.
	 */
	public OctConjunction binarySequentialize(OctConjunction first, OctConjunction second,
			Map<IProgramVar, TermVariable> inVars, Map<IProgramVar, TermVariable> outVars) {
		final HashSet<TermVariable> variables = new HashSet<>();
		final HashSet<TermVariable> inVarSet = new HashSet<>();
		final HashSet<TermVariable> outVarSet = new HashSet<>();

		getVariableSets(inVarSet, outVarSet, variables, inVars, outVars);

		final Map<TermVariable, TermVariable> termMapping = getTermMapping(inVars, outVars);
		final Map<TermVariable, TermVariable> reverseTermMapping = getReverseTermMapping(termMapping);

		return binarySequentialize(first, second, inVarSet, outVarSet, reverseTermMapping);

	}

	OctConjunction binarySequentialize(OctConjunction first, OctConjunction second, HashSet<TermVariable> inVarSet,
			HashSet<TermVariable> outVarSet, Map<TermVariable, TermVariable> variableMapping) {

		final Map<TermVariable, OctagonSubstitution> firstSubstitutions = new HashMap<>();
		final Map<TermVariable, OctagonSubstitution> secondSubstitutions = new HashMap<>();

		for (final TermVariable t : outVarSet) {
			firstSubstitutions.put(t, getSubstitution(t, first));
			secondSubstitutions.put(t, getSubstitution(t, second));
		}

		mUtils.debug(firstSubstitutions.toString());
		mUtils.debug(secondSubstitutions.toString());

		HashSet<SubstitutionTermContainer> secondContainers = getContainers(second);
		final HashSet<SubstitutionTermContainer> firstContainers = getContainers(first);

		secondContainers = substituteInVars(secondContainers, inVarSet, variableMapping);

		mUtils.debug("> Result:");
		mUtils.debug(secondContainers.toString());

		final OctConjunction secondSubstituted = substitute(secondContainers, outVarSet, firstSubstitutions);
		final OctConjunction firstFinal = getInTerms(first, inVarSet);

		mUtils.debug(second.toString());

		// first = substitute(firstContainers, outVarSet, firstSubstitutions);

		mUtils.debug(">> Substitutions finished.");
		final OctConjunction inputConstraints = getInputConstraints(first, inVarSet);
		mUtils.debug(inputConstraints.toString());
		final OctConjunction result = conjunction(firstFinal, secondSubstituted);
		return result;
	}

	private OctConjunction getInTerms(OctConjunction first, HashSet<TermVariable> inVars) {
		final OctConjunction result = new OctConjunction();

		for (final OctTerm t : first.getTerms()) {
			if (inVars.contains(t.getFirstVar()) && inVars.contains(t.getSecondVar())) {
				result.addTerm(t);
			}
		}

		return result;
	}

	private static OctConjunction getInputConstraints(OctConjunction first, HashSet<TermVariable> inVarSet) {
		final OctConjunction result = new OctConjunction();
		for (final OctTerm t : first.getTerms()) {
			if (inVarSet.contains(t.getFirstVar()) && inVarSet.contains(t.getSecondVar())) {
				result.addTerm(t);
			}
		}
		return result;
	}

	private HashSet<SubstitutionTermContainer> getContainers(OctConjunction second) {
		final HashSet<SubstitutionTermContainer> result = new HashSet<>();
		for (final OctTerm t : second.getTerms()) {
			result.add(new SubstitutionTermContainer(t));
		}
		return result;
	}

	private HashSet<SubstitutionTermContainer> substituteInVars(HashSet<SubstitutionTermContainer> terms,
			HashSet<TermVariable> varSet, Map<TermVariable, TermVariable> variableMapping) {

		mUtils.debug("> Subsituting inVars with outVars");
		mUtils.debug("Variable Set: " + varSet.toString());
		mUtils.debug("Variable Mapping: " + variableMapping.toString());

		final HashSet<SubstitutionTermContainer> result = new HashSet<>();

		mUtils.debug(terms.toString());

		for (final SubstitutionTermContainer c : terms) {

			final OctTerm t = c.getTerm();

			SubstitutionTermContainer container;
			OctTerm newTerm;

			mUtils.debug("Replacing in Term:" + t.toString());

			if (t.isOneVar()) {

				TermVariable firstVar = t.getFirstVar();
				if (varSet.contains(firstVar)) {
					firstVar = variableMapping.get(firstVar);
				}
				newTerm = OctagonFactory.createOneVarOctTerm(t.getValue(), firstVar, t.isFirstNegative());
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
				newTerm = OctagonFactory.createTwoVarOctTerm(t.getValue(), firstVar, t.isFirstNegative(), secondVar,
						t.isSecondNegative());
				mUtils.debug("New Term:" + newTerm.toString());
				container = new SubstitutionTermContainer(newTerm, firstLocked, secondLocked);

			}

			result.add(container);
		}

		mUtils.debug("InVars substituted.");

		return result;
	}

	private OctConjunction substitute(HashSet<SubstitutionTermContainer> terms, HashSet<TermVariable> varSet,
			Map<TermVariable, OctagonSubstitution> substitutions) {

		mUtils.debug("> Substituting a set of variables.");
		mUtils.debug("varSet:" + varSet.toString());

		final OctConjunction result = new OctConjunction();
		final HashSet<OctTerm> resultSet = new HashSet<>();

		for (final SubstitutionTermContainer c : terms) {

			final OctTerm t = c.getTerm();
			mUtils.debug("-Substituting in: " + t.toString());
			mUtils.debug(c.isFirstLocked());

			if (varSet.contains(t.getFirstVar()) && !c.isFirstLocked()) {

				if (!t.isOneVar() && varSet.contains(t.getSecondVar()) && !c.isSecondLocked()) {
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

		for (final OctTerm t : resultSet) {
			result.addTerm(t);
		}

		return result;
	}

	private HashSet<OctTerm> getTermSubstitutions(OctTerm t, Map<TermVariable, OctagonSubstitution> substitutions,
			int which) {

		final HashSet<OctTerm> result = new HashSet<>();

		if (which != 0) {
			final TermVariable toReplace = which == 1 ? t.getFirstVar() : t.getSecondVar();
			final boolean negative = which == 1 ? t.isFirstNegative() : t.isSecondNegative();

			mUtils.debug("Variable " + which + ": " + toReplace.toString());

			HashSet<OctagonSubstitutionTerm> subs;

			if (negative) {
				subs = substitutions.get(toReplace).getLesserSubsitutions();
			} else {
				subs = substitutions.get(toReplace).getGreaterSubsitutions();
			}

			mUtils.debug("Substitutions: " + subs.toString());

			for (final OctagonSubstitutionTerm sub : subs) {
				final OctTerm newTerm = getTermFromSubsitution(t, sub, which);
				if (newTerm != null) {
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

			HashSet<OctagonSubstitutionTerm> subs;
			final HashSet<OctTerm> tempResults = new HashSet<>();

			if (firstNegative) {
				subs = substitutions.get(replaceFirst).getLesserSubsitutions();
			} else {
				subs = substitutions.get(replaceFirst).getGreaterSubsitutions();
			}

			// Build temporary Terms substituting only the first Variable.

			for (final OctagonSubstitutionTerm sub : subs) {
				final OctTerm newTerm = getTermFromSubsitution(t, sub, 1);
				if (newTerm != null) {
					tempResults.add(newTerm);
				}
			}

			if (secondNegative) {
				subs = substitutions.get(replaceSecond).getLesserSubsitutions();
			} else {
				subs = substitutions.get(replaceSecond).getGreaterSubsitutions();
			}

			// For each temporary Term substitute the second Variable.

			for (final OctTerm tempTerm : tempResults) {
				for (final OctagonSubstitutionTerm sub : subs) {
					final OctTerm newTerm = getTermFromSubsitution(tempTerm, sub, 2);
					if (newTerm != null) {
						result.add(newTerm);
					}
				}

			}

		}
		return result;
	}

	private OctTerm getTermFromSubsitution(OctTerm t, OctagonSubstitutionTerm sub, int which) {

		mUtils.debug("-Building new substituted Term from " + t.toString() + " with substitution " + sub.toString());

		OctTerm result;

		// For OneVarTerms the previous term with two vars needs to be doubled.

		if (t.isOneVar()) {
			if (sub.isZeroVar()) {
				result = null;
			} else {
				result = OctagonFactory.createOneVarOctTerm(getSubsitutionValue(t.getValue(), sub.getValue(), 0),
						sub.getVar(), sub.isVarNegative());
			}
		} else {
			if (sub.isZeroVar()) {
				result = OctagonFactory.createOneVarOctTerm(getSubsitutionValue(t.getValue(), sub.getValue(), 1),
						which == 1 ? t.getSecondVar() : t.getFirstVar(),
						which == 1 ? t.isSecondNegative() : t.isFirstNegative());
			} else {
				result = OctagonFactory.createTwoVarOctTerm(getSubsitutionValue(t.getValue(), sub.getValue(), 2),
						which == 1 ? t.getSecondVar() : t.getFirstVar(),
						which == 1 ? t.isSecondNegative() : t.isFirstNegative(), sub.getVar(), sub.isVarNegative());
			}
		}

		mUtils.debug("-Result: " + (result != null ? result.toString() : "null"));
		return result;
	}

	private Object getSubsitutionValue(Object value1, Object value2, int i) {
		if (i == 2) {
			return addValues(value1, value2);
		} else if (i == 1) {
			return addValues(value1, value2, new BigDecimal(2), BigDecimal.ONE);
		}
		return addValues(value1, value2, BigDecimal.ONE, new BigDecimal(2));
	}

	private Object addValues(Object value1, Object value2) {
		return addValues(value1, value2, BigDecimal.ONE, BigDecimal.ONE);
	}

	private static Object addValues(Object value1, Object value2, BigDecimal one, BigDecimal two) {
		if (value1 instanceof ParametricOctValue) {
			value1 = ((ParametricOctValue) value1).multipy(one);
			if (value2 instanceof ParametricOctValue) {
				value2 = ((ParametricOctValue) value2).multipy(two);
			} else {
				value2 = ((BigDecimal) value2).multiply(two);
			}
			return ((ParametricOctValue) value1).add(value2);
		} else if (value2 instanceof ParametricOctValue) {
			value2 = ((ParametricOctValue) value2).multipy(two);
			if (value1 instanceof ParametricOctValue) {
				value1 = ((ParametricOctValue) value1).multipy(one);
			} else {
				value1 = ((BigDecimal) value1).multiply(one);
			}
			return ((ParametricOctValue) value2).add(value1);
		}
		value1 = ((BigDecimal) value1).multiply(one);
		value2 = ((BigDecimal) value2).multiply(two);
		return ((BigDecimal) value1).add((BigDecimal) value2);
	}

	/**
	 * Create a new conjunction of two existing conjunctions resutl = C and C'
	 *
	 * @param first
	 *            first conjunction
	 * @param second
	 *            second conjunction
	 * @return conjunction of both OctagonConjunctions
	 */
	private OctConjunction conjunction(OctConjunction first, OctConjunction second) {
		final OctConjunction result = new OctConjunction();
		for (final OctTerm t : first.getTerms()) {
			result.addTerm(t);
		}

		for (final OctTerm t : second.getTerms()) {
			result.addTerm(t);
		}

		return result;
	}

	private static Map<TermVariable, TermVariable> getTermMapping(Map<IProgramVar, TermVariable> inVars,
			Map<IProgramVar, TermVariable> outVars) {

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

	/**
	 *
	 * @param termMapping
	 * @return
	 */
	public static Map<TermVariable, TermVariable> getReverseTermMapping(Map<TermVariable, TermVariable> termMapping) {
		final Map<TermVariable, TermVariable> result = new HashMap<>();
		for (final TermVariable t : termMapping.keySet()) {
			result.put(termMapping.get(t), t);
		}

		return result;
	}

	private OctagonSubstitution getSubstitution(TermVariable var, OctConjunction conjunc) {
		final OctagonSubstitution result = new OctagonSubstitution(var);
		for (final OctTerm t : conjunc.getTerms()) {
			result.addSubstitution(t);
		}
		return result;

	}

	private class SubstitutionTermContainer {
		private final OctTerm mTerm;
		private final boolean mFirstLocked;
		private final boolean mSecondLocked;

		SubstitutionTermContainer(OctTerm term) {
			this(term, true, true);
		}

		SubstitutionTermContainer(OctTerm term, boolean locked) {
			this(term, locked, true);
		}

		SubstitutionTermContainer(OctTerm term, boolean first, boolean second) {
			mTerm = term;
			mFirstLocked = first;
			mSecondLocked = second;
		}

		@Override
		public String toString() {
			return mTerm.toString();
		}

		OctTerm getTerm() {
			return mTerm;
		}

		boolean isFirstLocked() {
			return mFirstLocked;
		}

		boolean isSecondLocked() {
			return mSecondLocked;
		}
	}

	/**
	 *
	 * @param inVarMap
	 * @param outVarMap
	 * @return
	 */
	public List<TermVariable> getSortedVariables(Map<IProgramVar, TermVariable> inVarMap,
			Map<IProgramVar, TermVariable> outVarMap) {

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

		final Comparator<TermVariable> compare = new Comparator<TermVariable>() {
			@Override
			public int compare(TermVariable one, TermVariable other) {
				return one.toString().compareTo(other.toString());
			}
		};

		final List<TermVariable> inVarList = new ArrayList<>(inVars);
		final List<TermVariable> outVarList = new ArrayList<>(outVars);
		final List<TermVariable> mixedVarList = new ArrayList<>(mixedVars);

		Collections.sort(inVarList, compare);
		Collections.sort(mixedVarList, compare);
		Collections.sort(outVarList, compare);

		inVarList.addAll(mixedVarList);
		inVarList.addAll(outVarList);

		final ArrayList<TermVariable> sorted = new ArrayList<>();
		sorted.addAll(inVarList);

		return sorted;
	}

	public FastUPRUtils getUtils() {
		return mUtils;
	}

	public boolean isTrivial(Map<IProgramVar, TermVariable> inVars, Map<IProgramVar, TermVariable> outVars) {
		for (final Entry<IProgramVar, TermVariable> e : inVars.entrySet()) {
			if (!outVars.containsValue(e.getValue())) {
				return false;
			}
		}
		for (final Entry<IProgramVar, TermVariable> e : outVars.entrySet()) {
			if (!inVars.containsValue(e.getValue())) {
				return false;
			}
		}
		return true;
	}
}
