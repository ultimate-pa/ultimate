/*
 * Copyright (C) 2017 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
 *
 * This file is part of the ULTIMATE ModelCheckerUtils Library.
 *
 * The ULTIMATE ModelCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ModelCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ModelCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ModelCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ModelCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier;

import java.util.Arrays;
import java.util.Collection;
import java.util.LinkedHashSet;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SubtermPropertyChecker;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.binaryrelation.RelationSymbol;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.normalforms.NnfTransformer;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.normalforms.NnfTransformer.QuantifierHandling;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier.QuantifierPusher.PqeTechniques;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/**
 * This class provides static methods for handling quantified formulas and
 * auxiliary methods for algorithms that handle quantified formulas. <br />
 * The motivation for many of these methods is the following: Several of our
 * algorithms are very similar, but not identical for the two different
 * quantifiers. E.g., an algorithm may construct
 * <li>a conjunction for one quantifier and a disjunction for the other
 * quantifier,
 * <li>an equality for one quantifier and a not-equals relation for the other
 * quantifier,
 * <li>a negation for one quantifier and no additional operation for the other
 * quantifier. <br />
 * In order to write down algorithms and methods that are parameterized by the
 * quantifier we use the following terminology which is inspired by the view
 * that existential quantification is an infinite disjunction and universal
 * quantification is an infinite conjunction.
 * <li>∃ is the dual quantifier for ∀, ∀ is the dual quantifier for ∃
 * <li>∃ is the corresponding quantifier for ∨, ∀ is the corresponding
 * quantifier for ∧
 * <li>∨ is the corresponding finite connective for ∃, ∧ is the corresponding
 * finite connective for ∀
 * <li>a <em>corresponding finite junction</em> is a disjunction for ∃ and a
 * conjunction for ∀
 * <li>∧ is the dual finite connective for ∃, ∨ is the dual finite connective
 * for ∀
 * <li>a <em>dual finite junction</em> is a conjunction for ∃ and a disjunction
 * for ∀
 * <li>= is the DER-Operator for ∃, ≠ is the DER-Operator for ∀ (see
 * {@link DualJunctionDer})
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class QuantifierUtils {

	private static final String UNKNOWN_QUANTIFIER = "unknown quantifier";

	private QuantifierUtils() {
		// do not instantiate
	}

	/**
	 * @return false iff some subformula is a {@link QuantifiedFormula}.
	 */
	public static boolean isQuantifierFree(final Term term) {
		return !new SubtermPropertyChecker(x -> (x instanceof QuantifiedFormula)).isSatisfiedBySomeSubterm(term);
	}

	public static Term flattenQuantifiers(final Script script, final QuantifiedFormula qf) {
		return SmtUtils.quantifier(script, qf.getQuantifier(), Arrays.asList(qf.getVariables()), qf.getSubformula());
	}

	public static String getAsciiAbbreviation(final int quantifier) {
		if (quantifier == 0) {
			return "E";
		} else if (quantifier == 1) {
			return "A";
		} else {
			throw new AssertionError(UNKNOWN_QUANTIFIER);
		}
	}

	public static int getDualQuantifier(final int quantifier) {
		if (quantifier == QuantifiedFormula.EXISTS) {
			return 1;
		} else if (quantifier == QuantifiedFormula.FORALL) {
			return 0;
		} else {
			throw new UnsupportedOperationException(UNKNOWN_QUANTIFIER);
		}
	}

	/**
	 * Construct disjunction for ∃, construct conjunction for ∀.
	 */
	public static Term applyCorrespondingFiniteConnective(final Script script, final int quantifier,
			final Collection<Term> correspondingFiniteJuncts) {
		final Term result;
		if (quantifier == QuantifiedFormula.EXISTS) {
			result = SmtUtils.or(script, correspondingFiniteJuncts);
		} else if (quantifier == QuantifiedFormula.FORALL) {
			result = SmtUtils.and(script, correspondingFiniteJuncts);
		} else {
			throw new AssertionError(UNKNOWN_QUANTIFIER);
		}
		return result;
	}

	/**
	 * Construct disjunction for ∃, construct conjunction for ∀.
	 */
	public static Term applyCorrespondingFiniteConnective(final Script script, final int quantifier,
			final Term... correspondingFiniteJuncts) {
		return applyCorrespondingFiniteConnective(script, quantifier, Arrays.asList(correspondingFiniteJuncts));
	}

	/**
	 * Construct conjunction for ∃, construct disjunction for ∀.
	 */
	public static Term applyDualFiniteConnective(final Script script, final int quantifier,
			final Collection<Term> dualFiniteJunction) {
		final Term result;
		if (quantifier == QuantifiedFormula.EXISTS) {
			result = SmtUtils.and(script, dualFiniteJunction);
		} else if (quantifier == QuantifiedFormula.FORALL) {
			result = SmtUtils.or(script, dualFiniteJunction);
		} else {
			throw new AssertionError(UNKNOWN_QUANTIFIER);
		}
		return result;
	}

	/**
	 * Construct conjunction for ∃, construct disjunction for ∀.
	 */
	public static Term applyDualFiniteConnective(final Script script, final int quantifier,
			final Term... dualFiniteJunction) {
		return applyDualFiniteConnective(script, quantifier, Arrays.asList(dualFiniteJunction));
	}

	/**
	 * @return ∃ for "or", ∀ for "and"
	 */
	public static int getCorrespondingQuantifier(final String booleanConnective) {
		if (booleanConnective.equals("and")) {
			return QuantifiedFormula.FORALL;
		} else if (booleanConnective.equals("or")) {
			return QuantifiedFormula.EXISTS;
		} else {
			throw new AssertionError("unsupported connective " + booleanConnective);
		}
	}

	public static String getNameOfCorrespondingJuncts(final int quantifier) {
		String result;
		if (quantifier == QuantifiedFormula.EXISTS) {
			result = "disjuncts";
		} else if (quantifier == QuantifiedFormula.FORALL) {
			result = "conjuncts";
		} else {
			throw new AssertionError(UNKNOWN_QUANTIFIER);
		}
		return result;
	}

	public static String getNameOfDualJuncts(final int quantifier) {
		String result;
		if (quantifier == QuantifiedFormula.EXISTS) {
			result = "conjuncts";
		} else if (quantifier == QuantifiedFormula.FORALL) {
			result = "disjuncts";
		} else {
			throw new AssertionError(UNKNOWN_QUANTIFIER);
		}
		return result;
	}

	/**
	 * Return all disjuncts for ∃, return all conjuncts for ∀. <br />
	 * If the topmost symbol of the input is not the corresponding finite
	 * connective, we consider the input as a 1-ary corresponding finite junction
	 * and return a singleton array.
	 */
	public static Term[] getCorrespondingFiniteJuncts(final int quantifier, final Term correspondingFiniteJunction) {
		final Term[] correspondingFiniteJuncts;
		if (quantifier == QuantifiedFormula.EXISTS) {
			correspondingFiniteJuncts = SmtUtils.getDisjuncts(correspondingFiniteJunction);
		} else if (quantifier == QuantifiedFormula.FORALL) {
			correspondingFiniteJuncts = SmtUtils.getConjuncts(correspondingFiniteJunction);
		} else {
			throw new AssertionError(UNKNOWN_QUANTIFIER);
		}
		return correspondingFiniteJuncts;
	}

	/**
	 * Return all conjuncts for ∃, return all disjuncts for ∀. <br />
	 * If the topmost symbol of the input is not the corresponding finite
	 * connective, we consider the input as a 1-ary corresponding finite junction
	 * and return a singleton array.
	 */
	public static Term[] getDualFiniteJuncts(final int quantifier, final Term dualFiniteJunction) {
		final Term[] dualFiniteJuncts;
		if (quantifier == QuantifiedFormula.EXISTS) {
			dualFiniteJuncts = SmtUtils.getConjuncts(dualFiniteJunction);
		} else if (quantifier == QuantifiedFormula.FORALL) {
			dualFiniteJuncts = SmtUtils.getDisjuncts(dualFiniteJunction);
		} else {
			throw new AssertionError(UNKNOWN_QUANTIFIER);
		}
		return dualFiniteJuncts;
	}

	/**
	 * @return true iff the quantifier is ∃ and the term is a conjunction or the
	 *         quantifier is ∀ and the term is a disjunction.
	 */
	public static boolean isDualFiniteJunction(final int quantifier, final Term term) {
		return getDualFiniteJuncts(quantifier, term).length > 1;
	}

	/**
	 * @return true iff the quantifier is ∃ and the term is a disjunction or the
	 *         quantifier is ∀ and the term is a conjunction.
	 */
	public static boolean isCorrespondingFiniteJunction(final int quantifier, final Term term) {
		return getCorrespondingFiniteJuncts(quantifier, term).length > 1;
	}

	/**
	 * @return The term `false` for ∃ and the term `true` for ∀.
	 */
	public static Term getNeutralElement(final Script script, final int quantifier) {
		if (quantifier == QuantifiedFormula.EXISTS) {
			return script.term("false");
		} else if (quantifier == QuantifiedFormula.FORALL) {
			return script.term("true");
		} else {
			throw new AssertionError(UNKNOWN_QUANTIFIER);
		}
	}

	/**
	 * @return The term `true` for ∃ and the term `false` for ∀.
	 */
	public static Term getAbsorbingElement(final Script script, final int quantifier) {
		if (quantifier == QuantifiedFormula.EXISTS) {
			return script.term("true");
		} else if (quantifier == QuantifiedFormula.FORALL) {
			return script.term("false");
		} else {
			throw new AssertionError(UNKNOWN_QUANTIFIER);
		}
	}

	public static String getDualBooleanConnective(final String booleanConnective) {
		if (booleanConnective.equals("and")) {
			return "or";
		} else if (booleanConnective.equals("or")) {
			return "and";
		} else {
			throw new AssertionError("unsupported connective " + booleanConnective);
		}
	}

	/**
	 * @return inputTerm if quantifier for ∃, negate inputTerm for ∀
	 */
	public static Term negateIfUniversal(final Script script, final int quantifier, final Term inputTerm) {
		Term result;
		if (quantifier == QuantifiedFormula.EXISTS) {
			result = inputTerm;
		} else if (quantifier == QuantifiedFormula.FORALL) {
			result = SmtUtils.not(script, inputTerm);
		} else {
			throw new AssertionError(UNKNOWN_QUANTIFIER);
		}
		return result;
	}

	/**
	 * @return inputTerm if quantifier for ∃, negate inputTerm and transform to NNF
	 *         for ∀
	 */
	public static Term negateIfUniversal(final IUltimateServiceProvider services, final ManagedScript mgdScript,
			final int quantifier, final Term inputTerm) {
		Term result;
		if (quantifier == QuantifiedFormula.EXISTS) {
			result = inputTerm;
		} else if (quantifier == QuantifiedFormula.FORALL) {
			result = new NnfTransformer(mgdScript, services, QuantifierHandling.IS_ATOM)
					.transform(SmtUtils.not(mgdScript.getScript(), inputTerm));
		} else {
			throw new AssertionError(UNKNOWN_QUANTIFIER);
		}
		return result;
	}

	/**
	 * @return inputTerm if quantifier for ∀, negate inputTerm for ∃
	 */
	public static Term negateIfExistential(final Script script, final int quantifier, final Term inputTerm) {
		Term result;
		if (quantifier == QuantifiedFormula.EXISTS) {
			result = SmtUtils.not(script, inputTerm);
		} else if (quantifier == QuantifiedFormula.FORALL) {
			result = inputTerm;
		} else {
			throw new AssertionError(UNKNOWN_QUANTIFIER);
		}
		return result;
	}

	/**
	 * @return inputTerm if quantifier for ∀, negate inputTerm and transform to NNF
	 *         for ∃
	 */
	public static Term negateIfExistential(final IUltimateServiceProvider services, final ManagedScript mgdScript,
			final int quantifier, final Term inputTerm) {
		Term result;
		if (quantifier == QuantifiedFormula.EXISTS) {
			result = new NnfTransformer(mgdScript, services, QuantifierHandling.IS_ATOM)
					.transform(SmtUtils.not(mgdScript.getScript(), inputTerm));
		} else if (quantifier == QuantifiedFormula.FORALL) {
			result = inputTerm;
		} else {
			throw new AssertionError(UNKNOWN_QUANTIFIER);
		}
		return result;
	}

	/**
	 * Construct equality for ∃, construct not-equals relation for ∀.
	 */
	public static Term applyDerOperator(final Script script, final int quantifier, final Term lhs, final Term rhs) {
		Term result;
		if (quantifier == QuantifiedFormula.EXISTS) {
			result = SmtUtils.binaryEquality(script, lhs, rhs);
		} else if (quantifier == QuantifiedFormula.FORALL) {
			result = SmtUtils.distinct(script, lhs, rhs);
		} else {
			throw new AssertionError(UNKNOWN_QUANTIFIER);
		}
		return result;
	}

	/**
	 * Construct not-equals relation for ∃, construct equality for ∀.
	 */
	public static Term applyAntiDerOperator(final Script script, final int quantifier, final Term lhs, final Term rhs) {
		Term result;
		if (quantifier == QuantifiedFormula.EXISTS) {
			result = SmtUtils.distinct(script, lhs, rhs);
		} else if (quantifier == QuantifiedFormula.FORALL) {
			result = SmtUtils.binaryEquality(script, lhs, rhs);
		} else {
			throw new AssertionError(UNKNOWN_QUANTIFIER);
		}
		return result;
	}

	/**
	 * @return `=` for ∃, `≠` for ∀
	 */
	public static RelationSymbol getDerOperator(final int quantifier) {
		if (quantifier == QuantifiedFormula.EXISTS) {
			return RelationSymbol.EQ;
		} else if (quantifier == QuantifiedFormula.FORALL) {
			return RelationSymbol.DISTINCT;
		} else {
			throw new AssertionError(UNKNOWN_QUANTIFIER);
		}
	}

	public static boolean isDerRelationSymbol(final int quantifier, final RelationSymbol relSymb) {
		return relSymb.equals(getDerOperator(quantifier));
	}

	/**
	 * Transform to DNF for existential quantifier, transform to CNF for universal
	 * quantifier.
	 */
	public static Term transformToXnf(final IUltimateServiceProvider services, final Script script,
			final int quantifier, final ManagedScript mgdScript, Term term,
			final XnfConversionTechnique xnfConversionTechnique) throws AssertionError {
		if (quantifier == QuantifiedFormula.EXISTS) {
			term = SmtUtils.toDnf(services, mgdScript, term, xnfConversionTechnique);
		} else if (quantifier == QuantifiedFormula.FORALL) {
			term = SmtUtils.toCnf(services, mgdScript, term, xnfConversionTechnique);
		} else {
			throw new AssertionError(UNKNOWN_QUANTIFIER);
		}
		return term;
	}

	/**
	 * @return A new set that is the projection of vars to the free variables of
	 *         term.
	 */
	public static LinkedHashSet<TermVariable> projectToFreeVars(final Collection<TermVariable> vars, final Term term) {
		final LinkedHashSet<TermVariable> result = new LinkedHashSet<>();
		for (final TermVariable freeVar : term.getFreeVars()) {
			if (vars.contains(freeVar)) {
				result.add(freeVar);
			}
		}
		return result;
	}

	@FunctionalInterface
	public interface IQuantifierEliminator {
		public Term eliminate(final IUltimateServiceProvider services, final ManagedScript script,
				final boolean applyDistributivity, final PqeTechniques quantifierEliminationTechniques,
				final SimplificationTechnique simplificationTechnique, final Context context, final Term inputTerm);
	}
}
