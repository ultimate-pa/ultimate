/*
 * Copyright (C) 2015 Jan Leike (leike@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 University of Freiburg
 *
 * This file is part of the ULTIMATE LassoRanker Library.
 *
 * The ULTIMATE LassoRanker Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE LassoRanker Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE LassoRanker Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE LassoRanker Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE LassoRanker Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.function.Function;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transformations.IReplacementVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transformations.IReplacementVarOrConst;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transformations.ReplacementVarFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transformations.ReplacementVarUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramConst;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.Substitution;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/**
 * Some static methods for {@link ModifiableTransFormula}
 *
 * @author Matthias Heizmann
 */
public class ModifiableTransFormulaUtils {
	public static boolean allVariablesAreInVars(final List<Term> terms, final ModifiableTransFormula tf) {
		return terms.stream().allMatch(x -> allVariablesAreInVars(x, tf));
	}

	public static boolean allVariablesAreOutVars(final List<Term> terms, final ModifiableTransFormula tf) {
		return terms.stream().allMatch(x -> allVariablesAreOutVars(x, tf));
	}

	public static boolean allVariablesAreVisible(final List<Term> terms, final ModifiableTransFormula tf) {
		return terms.stream().allMatch(x -> allVariablesAreVisible(x, tf));
	}

	public static boolean allVariablesAreInVars(final Term term, final ModifiableTransFormula tf) {
		return Arrays.stream(term.getFreeVars()).allMatch(x -> isInVar(x, tf));
	}

	public static boolean allVariablesAreOutVars(final Term term, final ModifiableTransFormula tf) {
		return Arrays.stream(term.getFreeVars()).allMatch(x -> isOutVar(x, tf));
	}

	public static boolean allVariablesAreVisible(final Term term, final ModifiableTransFormula tf) {
		return Arrays.stream(term.getFreeVars()).allMatch(x -> isVisible(x, tf));
	}

	private static boolean isVisible(final TermVariable tv, final ModifiableTransFormula tf) {
		return isInVar(tv, tf) || isOutVar(tv, tf);
	}

	public static boolean isInVar(final TermVariable tv, final ModifiableTransFormula tf) {
		return tf.getInVarsReverseMapping().keySet().contains(tv);
	}

	public static boolean isOutVar(final TermVariable tv, final ModifiableTransFormula tf) {
		return tf.getOutVarsReverseMapping().keySet().contains(tv);
	}

	public static LBool implies(final IUltimateServiceProvider services, final ILogger logger,
			final ModifiableTransFormula antecedent, final ModifiableTransFormula consequent,
			final ManagedScript mgdScript, final IIcfgSymbolTable symbTab) {
		final Term antecentTerm = renameToConstants(services, logger, mgdScript, symbTab, antecedent);
		final Term consequentTerm = renameToConstants(services, logger, mgdScript, symbTab, consequent);
		mgdScript.getScript().push(1);
		mgdScript.getScript().assertTerm(antecentTerm);
		mgdScript.getScript().assertTerm(SmtUtils.not(mgdScript.getScript(), consequentTerm));
		mgdScript.getScript().assertTerm(
				getAdditionalEqualities(Arrays.asList(antecedent, consequent), symbTab, mgdScript.getScript()));
		final LBool result = mgdScript.getScript().checkSat();
		mgdScript.getScript().pop(1);
		return result;
	}

	/**
	 * Returns a conjunction of equalities of primed and unprimed constants, for which the corresponding variables don't
	 * occur in the {@code transformulas} directly, but as free variable in the definition of another occurring
	 * variable.
	 */
	private static Term getAdditionalEqualities(final List<ModifiableTransFormula> transformulas,
			final IIcfgSymbolTable symbTab, final Script script) {
		final Set<Term> result = new HashSet<>();
		final Set<TermVariable> vars = new HashSet<>();
		final Set<IProgramVar> programVars = new HashSet<>();
		for (final ModifiableTransFormula tf : transformulas) {
			for (final IProgramVar programVar : tf.getInVars().keySet()) {
				programVars.add(programVar);
				vars.addAll(Arrays.asList(ReplacementVarUtils.getDefinition(programVar).getFreeVars()));
			}
			for (final IProgramVar programVar : tf.getOutVars().keySet()) {
				programVars.add(programVar);
				vars.addAll(Arrays.asList(ReplacementVarUtils.getDefinition(programVar).getFreeVars()));
			}
		}
		for (final TermVariable var : vars) {
			final IProgramVar boogieVar = symbTab.getProgramVar(var);
			if (!programVars.contains(boogieVar)) {
				final Term equality =
						SmtUtils.binaryEquality(script, boogieVar.getDefaultConstant(), boogieVar.getPrimedConstant());
				result.add(equality);
			}
		}
		return SmtUtils.and(script, result);
	}

	/**
	 * Rename all to inVars/outVars by default/primed constants (including the definitions of
	 * {@link IReplacementVarOrConst}s. Quantify auxVars existentially.
	 *
	 * @param services
	 * @param logger
	 */
	private static Term renameToConstants(final IUltimateServiceProvider services, final ILogger logger,
			final ManagedScript mgdScript, final IIcfgSymbolTable symbTab, final ModifiableTransFormula tf) {
		final Map<Term, Term> substitutionMapping = new HashMap<>();
		for (final Entry<IProgramVar, TermVariable> entry : tf.getInVars().entrySet()) {
			if (entry.getKey() instanceof IReplacementVarOrConst) {
				final Term definition = ReplacementVarUtils.getDefinition(entry.getKey());
				substitutionMapping.put(entry.getValue(),
						renameVars(mgdScript, symbTab, definition, IProgramVar::getDefaultConstant));
			} else {
				substitutionMapping.put(entry.getValue(), entry.getKey().getDefaultConstant());
			}
		}
		for (final Entry<IProgramVar, TermVariable> entry : tf.getOutVars().entrySet()) {
			if (entry.getKey() instanceof IReplacementVarOrConst) {
				final Term definition = ReplacementVarUtils.getDefinition(entry.getKey());
				substitutionMapping.put(entry.getValue(),
						renameVars(mgdScript, symbTab, definition, IProgramVar::getPrimedConstant));
			} else {
				substitutionMapping.put(entry.getValue(), entry.getKey().getPrimedConstant());
			}
		}
		Term result = Substitution.apply(mgdScript, substitutionMapping, tf.getFormula());
		result = SmtUtils.and(mgdScript.getScript(), result,
				constructEqualitiesForCoinciding(mgdScript.getScript(), tf));
		if (!tf.getAuxVars().isEmpty()) {
			logger.warn(tf.getAuxVars().size() + " quantified variables");
			final TermVariable[] auxVarsArray = tf.getAuxVars().toArray(new TermVariable[tf.getAuxVars().size()]);
			result = mgdScript.getScript().quantifier(QuantifiedFormula.EXISTS, auxVarsArray, result);
		}
		assert (Arrays.asList(result.getFreeVars()).isEmpty()) : "there must not be a TermVariable left";
		return result;
	}

	private static Term renameVars(final ManagedScript mgdScript, final IIcfgSymbolTable symbTab, final Term term,
			final Function<IProgramVar, Term> termProvider) {
		final Map<Term, Term> substitutionMapping = new HashMap<>();
		for (final TermVariable tv : term.getFreeVars()) {
			final IProgramVar bv = symbTab.getProgramVar(tv);
			if (bv == null) {
				throw new IllegalArgumentException("term contains unknown variable");
			}
			substitutionMapping.put(tv, termProvider.apply(bv));
		}
		return Substitution.apply(mgdScript, substitutionMapping, term);
	}

	/**
	 * Compute the RankVar of a given TermVariable and return its definition.
	 */
	public static Term getDefinition(final ModifiableTransFormula tf, final TermVariable tv) {
		IProgramVar rv = tf.getInVarsReverseMapping().get(tv);
		if (rv == null) {
			rv = tf.getOutVarsReverseMapping().get(tv);
		}
		if (rv == null) {
			return null;
		}
		return ReplacementVarUtils.getDefinition(rv);
	}

	/**
	 * Compute the RankVar for each TermVariable that occurs in the Term term. Return a term in which each TermVarialbe
	 * is substituted by the definition of the RankVar. Throws an IllegalArgumentException if there occurs term contains
	 * a TermVariable that does not have a RankVar (e.g., an auxiliary variable).
	 */
	public static Term translateTermVariablesToDefinitions(final ManagedScript script, final ModifiableTransFormula tf,
			final Term term) {
		final Map<Term, Term> substitutionMapping = new HashMap<>();
		for (final TermVariable tv : term.getFreeVars()) {
			final Term definition = getDefinition(tf, tv);
			if (definition == null) {
				throw new IllegalArgumentException(tv + "has no RankVar");
			}
			substitutionMapping.put(tv, definition);
		}
		return Substitution.apply(script, substitutionMapping, term);
	}

	public static List<Term> translateTermVariablesToDefinitions(final ManagedScript script,
			final ModifiableTransFormula tf, final List<Term> terms) {
		return terms.stream().map(term -> translateTermVariablesToDefinitions(script, tf, term))
				.collect(Collectors.toList());
	}

	public static Term translateTermVariablesToInVars(final ManagedScript script, final ModifiableTransFormula tf,
			final Term term, final IIcfgSymbolTable symbolTable) {
		final Map<Term, Term> substitutionMapping = new HashMap<>();
		for (final TermVariable tv : term.getFreeVars()) {
			final IProgramVar bv = symbolTable.getProgramVar(tv);
			final Term inVar = tf.getInVars().get(bv);
			assert inVar != null : "no inVar for " + bv;
			substitutionMapping.put(tv, inVar);
		}
		return Substitution.apply(script, substitutionMapping, term);
	}

	public static boolean inVarAndOutVarCoincide(final IProgramVar rv, final ModifiableTransFormula rf) {
		return rf.getInVars().get(rv) == rf.getOutVars().get(rv);
	}

	private static Term constructEqualitiesForCoinciding(final Script script, final ModifiableTransFormula tf) {
		final ArrayList<Term> conjuncts = new ArrayList<>();
		for (final IProgramVar rv : tf.getInVars().keySet()) {
			if (!(rv instanceof IReplacementVarOrConst)) {
				if (inVarAndOutVarCoincide(rv, tf)) {
					final IProgramVar bv = rv;
					conjuncts.add(SmtUtils.binaryEquality(script, bv.getDefaultConstant(), bv.getPrimedConstant()));
				}
			}
		}
		return SmtUtils.and(script, conjuncts);
	}

	/**
	 * Construct a modifiable copy of the input.
	 */
	public static ModifiableTransFormula buildTransFormula(final TransFormula inputTf, final ManagedScript mgdScript) {
		return buildTransFormulaHelper(inputTf, null, mgdScript);
	}

	/**
	 * Construct a modifiable copy of the input. Additionally add a {@link ReplacementVar} for all non-theory constants.
	 *
	 */
	public static ModifiableTransFormula buildTransFormula(final TransFormula inputTf,
			final ReplacementVarFactory replacementVarFactory, final ManagedScript mgdScript) {
		return buildTransFormulaHelper(inputTf, replacementVarFactory, mgdScript);
	}

	private static ModifiableTransFormula buildTransFormulaHelper(final TransFormula inputTf,
			final ReplacementVarFactory replacementVarFactory, final ManagedScript mgdScript) {
		final Map<Term, Term> substitutionMapping = new HashMap<>();

		// construct copies of auxVars
		final Set<TermVariable> auxVars = new HashSet<>();
		for (final TermVariable auxVar : inputTf.getAuxVars()) {
			final TermVariable newAuxVar = mgdScript.constructFreshCopy(auxVar);
			auxVars.add(newAuxVar);
			substitutionMapping.put(auxVar, newAuxVar);
		}
		final ModifiableTransFormula newTf = new ModifiableTransFormula((Term) null);
		if (replacementVarFactory != null) {
			// Add constant variables as in- and outVars
			for (final IProgramConst progConst : inputTf.getNonTheoryConsts()) {
				final ApplicationTerm constVar = progConst.getDefaultConstant();
				final IReplacementVar repVar =
						(IReplacementVar) replacementVarFactory.getOrConstuctReplacementVar(constVar, true);
				newTf.addInVar(repVar, repVar.getTermVariable());
				newTf.addOutVar(repVar, repVar.getTermVariable());
				substitutionMapping.put(constVar, repVar.getTermVariable());
			}
		} else {
			newTf.addNonTheoryConsts(inputTf.getNonTheoryConsts());
		}

		final Term formula = Substitution.apply(mgdScript, substitutionMapping, inputTf.getFormula());
		newTf.setFormula(formula);

		// Add existing in- and outVars
		for (final Map.Entry<IProgramVar, TermVariable> entry : inputTf.getInVars().entrySet()) {
			newTf.addInVar(entry.getKey(), entry.getValue());
		}
		for (final Map.Entry<IProgramVar, TermVariable> entry : inputTf.getOutVars().entrySet()) {
			newTf.addOutVar(entry.getKey(), entry.getValue());
		}
		newTf.addAuxVars(auxVars);

		return newTf;
	}

}
