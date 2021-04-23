/*
 * Copyright (C) 2017 Jill Enke (enkei@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
 *
 * This file is part of the ULTIMATE IcfgTransformer library.
 *
 * The ULTIMATE IcfgTransformer is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE IcfgTransformer is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE IcfgTransformer library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE IcfgTransformer library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE IcfgTransformer grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.fastupr.paraoct;

import java.math.BigDecimal;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.fastupr.FastUPRUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.logic.NonRecursive;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/**
 * Class to rename variables and calculate sequential composition of OctagonConjunctions.
 */
public class OctagonCalculator extends NonRecursive {

	private final FastUPRUtils mUtils;
	private final ManagedScript mManagedScript;

	/**
	 *
	 * @param utils
	 * @param mgdScript
	 */
	public OctagonCalculator(final FastUPRUtils utils, final ManagedScript mgdScript) {
		mUtils = utils;
		mManagedScript = mgdScript;
	}

	/**
	 * Removes all Variables that are both inVars and outVars. All occurences in Terms are replaced with a fresh inVar
	 * and two new Terms are created to make a fresh outVar = inVar.
	 *
	 * @param conjunc
	 *            Conjunction to compute
	 * @param inVars
	 *            Mappings for InVars
	 * @param outVars
	 *            Mappings for OutVars
	 * @return OctagonConjunction without inOutVars.
	 */
	public OctConjunction removeInOutVars(final OctConjunction conjunc, final Map<IProgramVar, TermVariable> inVars,
			final Map<IProgramVar, TermVariable> outVars) {
		OctConjunction result = conjunc;
		for (final Entry<IProgramVar, TermVariable> e : inVars.entrySet()) {
			if (outVars.containsValue(e.getValue())) {

				final Sort varSort = mManagedScript.getScript().sort(SmtSortUtils.INT_SORT);

				final String inName = "oct_" + e.getKey().toString() + "_in";
				final TermVariable inVar = mManagedScript.constructFreshTermVariable(inName, varSort);
				final String outName = "oct_" + e.getKey().toString() + "_out";
				final TermVariable outVar = mManagedScript.constructFreshTermVariable(outName, varSort);

				result = replaceInOutVars(result, e.getValue(), inVar);
				result = getInOutVarTerms(result, inVar, outVar);
				inVars.put(e.getKey(), inVar);
				outVars.put(e.getKey(), outVar);

			}
		}
		return result;
	}

	private static OctConjunction getInOutVarTerms(final OctConjunction conjunc, final TermVariable inVar,
			final TermVariable outVar) {
		final OctConjunction result = conjunc;
		result.addTerm(OctagonFactory.createTwoVarOctTerm(BigDecimal.ZERO, inVar, false, outVar, true));
		result.addTerm(OctagonFactory.createTwoVarOctTerm(BigDecimal.ZERO, inVar, true, outVar, false));
		return result;
	}

	private static OctConjunction replaceInOutVars(final OctConjunction conjunc, final TermVariable inOutVar,
			final TermVariable inVar) {
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
	 * Normalizes Varnames of given conjunction and also changes them in the given inVar and outVar Maps. InVars will be
	 * namend (varname)_in, OutVars (varname)_out, Variables that are InVars and OutVars (varname)_inout
	 *
	 * @param conjunc
	 *            Conjunction to compute
	 * @param inVars
	 *            Mappings for InVars
	 * @param outVars
	 *            Mappings for OutVars
	 * @return OctagonConjunction with changed names.
	 */
	public OctConjunction normalizeVarNames(final OctConjunction conjunc, final Map<IProgramVar, TermVariable> inVars,
			final Map<IProgramVar, TermVariable> outVars) {

		mUtils.debug("Normalizing VarNames for:");
		mUtils.debug(conjunc.toString());

		OctConjunction result = conjunc;

		final Sort varSort = mManagedScript.getScript().sort(SmtSortUtils.INT_SORT);

		for (final IProgramVar p : inVars.keySet()) {
			String name;
			if (outVars.containsKey(p) && outVars.get(p).equals(inVars.get(p))) {
				name = "oct_" + p.toString() + "_inout";
				final TermVariable newVar = mManagedScript.constructFreshTermVariable(name, varSort);
				result = replaceVars(result, inVars.get(p), newVar);
				inVars.put(p, newVar);
				outVars.put(p, newVar);
			} else {
				name = "oct_" + p.toString() + "_in";
				final TermVariable newVar = mManagedScript.constructFreshTermVariable(name, varSort);
				result = replaceVars(result, inVars.get(p), newVar);
				inVars.put(p, newVar);
			}
			mUtils.debug(inVars.toString());
		}

		for (final IProgramVar p : outVars.keySet()) {
			if (outVars.containsKey(p) && !outVars.get(p).equals(inVars.get(p))) {
				final String name = "oct_" + p.toString() + "_out";
				final TermVariable newVar = mManagedScript.constructFreshTermVariable(name, varSort);
				result = replaceVars(result, outVars.get(p), newVar);
				outVars.put(p, newVar);
			}
		}
		mUtils.debug(result.toString());
		return result;
	}

	private OctConjunction replaceVars(final OctConjunction conjunc, final TermVariable oldVar,
			final TermVariable newVar) {

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
				final OctTerm newTerm =
						OctagonFactory.createTwoVarOctTerm(t.getValue(), replaceFirst ? newVar : t.getFirstVar(),
								t.isFirstNegative(), replaceSecond ? newVar : t.getSecondVar(), t.isSecondNegative());
				result.addTerm(newTerm);
				mUtils.debug(newTerm.toString());
			}
			mUtils.debug(">> replaced.");
		}

		mUtils.debug(">>> All replaced.");
		return result;
	}

	/**
	 * Caluclates the sequential composition of a given conjunction count times. (R^count)
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
	public OctConjunction sequentialize(final OctConjunction conjunc, final Map<IProgramVar, TermVariable> inVars,
			final Map<IProgramVar, TermVariable> outVars, final int count) {

		mUtils.debug("Sequentializing " + count + " times:" + conjunc.toString());

		final Set<TermVariable> variables = new LinkedHashSet<>();
		final Set<TermVariable> inVarSet = new LinkedHashSet<>();
		final Set<TermVariable> outVarSet = new LinkedHashSet<>();

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

	private static void getVariableSets(final Set<TermVariable> inVarSet, final Set<TermVariable> outVarSet,
			final Set<TermVariable> variableSet, final Map<IProgramVar, TermVariable> inVarMap,
			final Map<IProgramVar, TermVariable> outVarMap) {

		assert variableSet.isEmpty() && inVarSet.isEmpty() && outVarSet.isEmpty();

		for (final Entry<IProgramVar, TermVariable> p : inVarMap.entrySet()) {
			final TermVariable value = p.getValue();
			variableSet.add(value);
			inVarSet.add(value);
		}

		for (final Entry<IProgramVar, TermVariable> p : outVarMap.entrySet()) {
			final TermVariable value = p.getValue();
			variableSet.add(value);
			if (inVarSet.contains(value)) {
				inVarSet.remove(value);
			} else {
				outVarSet.add(value);
			}
		}
	}

	/**
	 * Computes a sequential composition of two OctagonConjunction with the same inVars and outVars.
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
	public OctConjunction binarySequentialize(final OctConjunction first, final OctConjunction second,
			final Map<IProgramVar, TermVariable> inVars, final Map<IProgramVar, TermVariable> outVars) {
		final Set<TermVariable> variables = new LinkedHashSet<>();
		final Set<TermVariable> inVarSet = new LinkedHashSet<>();
		final Set<TermVariable> outVarSet = new LinkedHashSet<>();

		getVariableSets(inVarSet, outVarSet, variables, inVars, outVars);

		final Map<TermVariable, TermVariable> termMapping = getTermMapping(inVars, outVars);
		final Map<TermVariable, TermVariable> reverseTermMapping = getReverseTermMapping(termMapping);

		return binarySequentialize(first, second, inVarSet, outVarSet, reverseTermMapping);

	}

	private OctConjunction binarySequentialize(final OctConjunction first, final OctConjunction second,
			final Set<TermVariable> inVarSet, final Set<TermVariable> outVarSet,
			final Map<TermVariable, TermVariable> variableMapping) {

		final Map<TermVariable, OctagonSubstitution> firstSubstitutions = new LinkedHashMap<>();

		for (final TermVariable t : outVarSet) {
			firstSubstitutions.put(t, getSubstitution(t, first));
		}

		mUtils.debug(firstSubstitutions.toString());

		final Set<SubstitutionTermContainer> secondContainers =
				substituteInVars(getContainers(second), inVarSet, variableMapping);

		mUtils.debug("> Result:");
		mUtils.debug(secondContainers.toString());

		final OctConjunction secondSubstituted = substitute(secondContainers, outVarSet, firstSubstitutions);

		mUtils.debug(second.toString());

		mUtils.debug(">> Substitutions finished.");
		final OctConjunction inputConstraints = getInputConstraints(first, inVarSet);
		final OctConjunction outputConstraints = getOutputConstraints(second, outVarSet);
		mUtils.debug(inputConstraints.toString());
		final OctConjunction constraints = conjunction(inputConstraints, outputConstraints);
		return conjunction(secondSubstituted, constraints);
	}

	private static OctConjunction getOutputConstraints(final OctConjunction second, final Set<TermVariable> outVarSet) {
		final OctConjunction result = new OctConjunction();
		for (final OctTerm t : second.getTerms()) {
			if (outVarSet.contains(t.getFirstVar()) && outVarSet.contains(t.getSecondVar())) {
				result.addTerm(t);
			}
		}
		return result;
	}

	private static OctConjunction getInputConstraints(final OctConjunction first, final Set<TermVariable> inVarSet) {
		final OctConjunction result = new OctConjunction();
		for (final OctTerm t : first.getTerms()) {
			if (inVarSet.contains(t.getFirstVar()) && inVarSet.contains(t.getSecondVar())) {
				result.addTerm(t);
			}
		}
		return result;
	}

	private Set<SubstitutionTermContainer> getContainers(final OctConjunction second) {
		final Set<SubstitutionTermContainer> result = new LinkedHashSet<>();
		for (final OctTerm t : second.getTerms()) {
			result.add(new SubstitutionTermContainer(t));
		}
		return result;
	}

	private Set<SubstitutionTermContainer> substituteInVars(final Set<SubstitutionTermContainer> terms,
			final Set<TermVariable> varSet, final Map<TermVariable, TermVariable> variableMapping) {

		mUtils.debug("> Subsituting inVars with outVars");
		mUtils.debug("Variable Set: " + varSet.toString());
		mUtils.debug("Variable Mapping: " + variableMapping.toString());

		final Set<SubstitutionTermContainer> result = new LinkedHashSet<>();

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

	private OctConjunction substitute(final Set<SubstitutionTermContainer> terms, final Set<TermVariable> varSet,
			final Map<TermVariable, OctagonSubstitution> substitutions) {

		mUtils.debug("> Substituting a set of variables.");
		mUtils.debug("varSet:" + varSet.toString());

		final OctConjunction result = new OctConjunction();
		final Set<OctTerm> resultSet = new LinkedHashSet<>();

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

	private Set<OctTerm> getTermSubstitutions(final OctTerm t,
			final Map<TermVariable, OctagonSubstitution> substitutions, final int which) {

		final Set<OctTerm> result = new LinkedHashSet<>();

		if (which != 0) {
			final TermVariable toReplace = which == 1 ? t.getFirstVar() : t.getSecondVar();
			final boolean negative = which == 1 ? t.isFirstNegative() : t.isSecondNegative();

			mUtils.debug("Variable " + which + ": " + toReplace.toString());

			Set<OctagonSubstitutionTerm> subs;

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

			Set<OctagonSubstitutionTerm> subs;
			final Set<OctTerm> tempResults = new LinkedHashSet<>();

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
					final OctTerm newTerm =
							getTermFromSubsitution(tempTerm, sub, tempTerm.getFirstVar().equals(replaceSecond) ? 1 : 2);
					if (newTerm != null) {
						result.add(newTerm);
					}
				}

			}

		}
		return result;
	}

	private OctTerm getTermFromSubsitution(final OctTerm t, final OctagonSubstitutionTerm sub, final int which) {

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
		} else if (sub.isZeroVar()) {
			result = OctagonFactory.createOneVarOctTerm(getSubsitutionValue(t.getValue(), sub.getValue(), 1),
					which == 1 ? t.getSecondVar() : t.getFirstVar(),
					which == 1 ? t.isSecondNegative() : t.isFirstNegative());
		} else {
			result = OctagonFactory.createTwoVarOctTerm(getSubsitutionValue(t.getValue(), sub.getValue(), 2),
					which == 1 ? t.getSecondVar() : t.getFirstVar(),
					which == 1 ? t.isSecondNegative() : t.isFirstNegative(), sub.getVar(), sub.isVarNegative());
		}

		mUtils.debug("-Result: " + (result != null ? result.toString() : "null"));
		return result;
	}

	private Object getSubsitutionValue(final Object value1, final Object value2, final int i) {
		if (i == 2) {
			return addValues(value1, value2);
		}
		if (i == 1) {
			return addValues(value1, value2, new BigDecimal(2), BigDecimal.ONE);
		}
		return addValues(value1, value2, BigDecimal.ONE, new BigDecimal(2));
	}

	private static Object addValues(final Object value1, final Object value2) {
		return addValues(value1, value2, BigDecimal.ONE, BigDecimal.ONE);
	}

	private static Object addValues(final Object value1, final Object value2, final BigDecimal one,
			final BigDecimal two) {
		Object finalValue1 = value1;
		Object finalValue2 = value2;

		if (finalValue1 instanceof ParametricOctValue) {
			finalValue1 = ((ParametricOctValue) finalValue1).multipy(one);
			if (finalValue2 instanceof ParametricOctValue) {
				finalValue2 = ((ParametricOctValue) finalValue2).multipy(two);
			} else {
				finalValue2 = ((BigDecimal) finalValue2).multiply(two);
			}
			return ((ParametricOctValue) finalValue1).add(finalValue2);
		}
		if (finalValue2 instanceof ParametricOctValue) {
			finalValue2 = ((ParametricOctValue) finalValue2).multipy(two);
			if (finalValue1 instanceof ParametricOctValue) {
				finalValue1 = ((ParametricOctValue) finalValue1).multipy(one);
			} else {
				finalValue1 = ((BigDecimal) finalValue1).multiply(one);
			}
			return ((ParametricOctValue) finalValue2).add(finalValue1);
		}
		finalValue1 = ((BigDecimal) finalValue1).multiply(one);
		finalValue2 = ((BigDecimal) finalValue2).multiply(two);
		return ((BigDecimal) finalValue1).add((BigDecimal) finalValue2);
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
	private static OctConjunction conjunction(final OctConjunction first, final OctConjunction second) {
		final OctConjunction result = new OctConjunction();
		for (final OctTerm t : first.getTerms()) {
			result.addTerm(t);
		}

		for (final OctTerm t : second.getTerms()) {
			result.addTerm(t);
		}

		return result;
	}

	private static Map<TermVariable, TermVariable> getTermMapping(final Map<IProgramVar, TermVariable> inVars,
			final Map<IProgramVar, TermVariable> outVars) {

		final Map<TermVariable, TermVariable> result = new LinkedHashMap<>();

		for (final Entry<IProgramVar, TermVariable> p : outVars.entrySet()) {
			final TermVariable outVar = p.getValue();
			final TermVariable inVar = inVars.get(p.getKey());
			if (outVar != null && inVar != null) {
				result.put(outVar, inVar);
			}
		}
		return result;
	}

	public static Map<TermVariable, TermVariable>
			getReverseTermMapping(final Map<TermVariable, TermVariable> termMapping) {
		final Map<TermVariable, TermVariable> result = new LinkedHashMap<>();
		for (final TermVariable t : termMapping.keySet()) {
			result.put(termMapping.get(t), t);
		}

		return result;
	}

	private static OctagonSubstitution getSubstitution(final TermVariable var, final OctConjunction conjunc) {
		final OctagonSubstitution result = new OctagonSubstitution(var);
		for (final OctTerm t : conjunc.getTerms()) {
			result.addSubstitution(t);
		}
		return result;

	}

	private static class SubstitutionTermContainer {
		private final OctTerm mTerm;
		private final boolean mFirstLocked;
		private final boolean mSecondLocked;

		SubstitutionTermContainer(final OctTerm term) {
			this(term, true, true);
		}

		SubstitutionTermContainer(final OctTerm term, final boolean locked) {
			this(term, locked, true);
		}

		SubstitutionTermContainer(final OctTerm term, final boolean first, final boolean second) {
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

	public List<TermVariable> getSortedVariables(final Map<IProgramVar, TermVariable> inVarMap,
			final Map<IProgramVar, TermVariable> outVarMap) {

		final Set<TermVariable> inVars = new LinkedHashSet<>();
		final Set<TermVariable> outVars = new LinkedHashSet<>();
		final Set<TermVariable> mixedVars = new LinkedHashSet<>();

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

		final Comparator<TermVariable> compare = (one, other) -> one.toString().compareTo(other.toString());

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

	/**
	 * Checks if the Mapping of a Transformula is Trival: It only contains inOutVars;
	 *
	 * @param inVars
	 * @param outVars
	 * @return
	 */
	public boolean isTrivial(final Map<IProgramVar, TermVariable> inVars,
			final Map<IProgramVar, TermVariable> outVars) {
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
