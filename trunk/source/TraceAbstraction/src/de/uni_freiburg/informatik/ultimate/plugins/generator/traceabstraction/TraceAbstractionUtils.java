/*
 * Copyright (C) 2016 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceAbstraction plug-in.
 *
 * The ULTIMATE TraceAbstraction plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceAbstraction plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceAbstraction plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceAbstraction plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceAbstraction plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.util.PartitionBackedSetOfPairs;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IcfgUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.ModifiableGlobalsTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.debugidentifiers.DebugIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramOldVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.IncrementalHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.MonolithicHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.IHoareTripleChecker.Validity;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.Substitution;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SubstitutionWithLocalSimplification;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.ISLPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.TermVarsProc;
import de.uni_freiburg.informatik.ultimate.logic.FormulaUnLet;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgLocation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.CachingHoareTripleCheckerMap;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.EfficientHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IMLPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.HoareAnnotationPositions;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.HoareTripleChecks;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap3;

/**
 * Provides static auxiliary methods for trace abstraction.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class TraceAbstractionUtils {

	/**
	 * @param <LCS>
	 *            local control state, e.g., {@link BoogieIcfgLocation} for sequential programs or a set of
	 *            {@link BoogieIcfgLocation}s for parallel programs.
	 * @param <LCSP>
	 *            local control state provider, e.g., {@link ISLPredicate}, or {@link IMLPredicate}
	 */
	public static <LCSP extends IPredicate, LCS> PartitionBackedSetOfPairs<IPredicate> computePartition(
			final INestedWordAutomaton<?, IPredicate> automaton, final ILogger logger,
			final Function<LCSP, LCS> lcsProvider) {
		logger.debug("Start computation of initial partition.");
		final Collection<IPredicate> states = automaton.getStates();
		final HashRelation<LCS, IPredicate> lcs2p = new HashRelation<>();
		for (final IPredicate p : states) {
			final LCSP sp = (LCSP) p;
			lcs2p.addPair(lcsProvider.apply(sp), p);
		}
		final Collection<Set<IPredicate>> partition = new ArrayList<>();
		for (final LCS pp : lcs2p.getDomain()) {
			final Set<IPredicate> statesWithSameLcs = new HashSet<>(lcs2p.getImage(pp));
			partition.add(statesWithSameLcs);
		}
		logger.debug("Finished computation of initial partition.");
		return new PartitionBackedSetOfPairs<>(partition);
	}

	public static IHoareTripleChecker constructEfficientHoareTripleChecker(final IUltimateServiceProvider services,
			final HoareTripleChecks hoareTripleChecks, final CfgSmtToolkit csToolkit,
			final IPredicateUnifier predicateUnifier) throws AssertionError {
		final IHoareTripleChecker solverHtc = constructSmtHoareTripleChecker(hoareTripleChecks, csToolkit);
		return new EfficientHoareTripleChecker(solverHtc, csToolkit, predicateUnifier);
	}

	public static IHoareTripleChecker constructSmtHoareTripleChecker(final HoareTripleChecks hoareTripleChecks,
			final CfgSmtToolkit csToolkit) throws AssertionError {
		final IHoareTripleChecker solverHtc;
		switch (hoareTripleChecks) {
		case MONOLITHIC:
			solverHtc = new MonolithicHoareTripleChecker(csToolkit);
			break;
		case INCREMENTAL:
			solverHtc = new IncrementalHoareTripleChecker(csToolkit, false);
			break;
		default:
			throw new AssertionError("unknown value");
		}
		return solverHtc;
	}

	public static IHoareTripleChecker constructEfficientHoareTripleCheckerWithCaching(
			final IUltimateServiceProvider services, final HoareTripleChecks hoareTripleChecks,
			final CfgSmtToolkit csToolkit, final IPredicateUnifier predicateUnifier) throws AssertionError {
		final IHoareTripleChecker ehtc =
				constructEfficientHoareTripleChecker(services, hoareTripleChecks, csToolkit, predicateUnifier);
		return new CachingHoareTripleCheckerMap(services, ehtc, predicateUnifier);
	}

	public static IHoareTripleChecker constructEfficientHoareTripleCheckerWithCaching(
			final IUltimateServiceProvider services, final HoareTripleChecks hoareTripleChecks,
			final CfgSmtToolkit csToolkit, final IPredicateUnifier predicateUnifier,
			final NestedMap3<IAction, IPredicate, IPredicate, Validity> initialInternalCache,
			final NestedMap3<IAction, IPredicate, IPredicate, Validity> initialCallCache,
			final Map<IPredicate, NestedMap3<IAction, IPredicate, IPredicate, Validity>> initialReturnCache)
			throws AssertionError {
		final IHoareTripleChecker ehtc =
				constructEfficientHoareTripleChecker(services, hoareTripleChecks, csToolkit, predicateUnifier);
		return new CachingHoareTripleCheckerMap(services, ehtc, predicateUnifier, initialInternalCache,
				initialCallCache, initialReturnCache);
	}

	/**
	 * Returns a predicate which states that old(g)=g for all global variables g that are modifiable by procedure proc
	 * according to ModifiableGlobalVariableManager modGlobVarManager.
	 */
	public static TermVarsProc getOldVarsEquality(final String proc,
			final ModifiableGlobalsTable modifiableGlobalsTable, final Script script) {
		final Set<IProgramVar> vars = new HashSet<>();
		Term term = script.term("true");
		for (final IProgramVar bv : modifiableGlobalsTable.getModifiedBoogieVars(proc)) {
			vars.add(bv);
			final IProgramVar bvOld = ((IProgramNonOldVar) bv).getOldVar();
			vars.add(bvOld);
			final TermVariable tv = bv.getTermVariable();
			final TermVariable tvOld = bvOld.getTermVariable();
			final Term equality = script.term("=", tv, tvOld);
			term = SmtUtils.and(script, term, equality);
		}
		final String[] procs = new String[0];
		final TermVarsProc result =
				new TermVarsProc(term, vars, procs, PredicateUtils.computeClosedFormula(term, vars, script));
		return result;

	}

	/**
	 * Construct Predicate which represents the same Predicate as ps, but where all globalVars are renamed to
	 * oldGlobalVars.
	 *
	 * @param services
	 * @param mgdScript
	 * @param predicateFactory
	 * @param simplificationTechnique
	 */
	public static IPredicate renameGlobalsToOldGlobals(final IPredicate ps, final IUltimateServiceProvider services,
			final ManagedScript mgdScript, final BasicPredicateFactory predicateFactory,
			final SimplificationTechnique simplificationTechnique) {
		if (predicateFactory.isDontCare(ps)) {
			throw new UnsupportedOperationException("don't cat not expected");
		}
		final Map<Term, Term> substitutionMapping = new HashMap<>();
		for (final IProgramVar pv : ps.getVars()) {
			if (pv instanceof IProgramNonOldVar) {
				final IProgramVar oldVar = ((IProgramNonOldVar) pv).getOldVar();
				substitutionMapping.put(pv.getTermVariable(), oldVar.getTermVariable());
			}
		}
		Term renamedFormula = new Substitution(mgdScript, substitutionMapping).transform(ps.getFormula());
		renamedFormula = SmtUtils.simplify(mgdScript, renamedFormula, services, simplificationTechnique);
		final IPredicate result = predicateFactory.newPredicate(renamedFormula);
		return result;
	}

	/**
	 * Construct Term which represents the same set of states as ps, but where all globalVars are renamed to
	 * oldGlobalVars.
	 *
	 */
	public static Term renameGlobalsToOldGlobals(final IPredicate ps, final IUltimateServiceProvider services,
			final ManagedScript mgdScript) {
		final Map<Term, Term> substitutionMapping = new HashMap<>();
		for (final IProgramVar pv : ps.getVars()) {
			if (pv instanceof IProgramNonOldVar) {
				final IProgramVar oldVar = ((IProgramNonOldVar) pv).getOldVar();
				substitutionMapping.put(pv.getTermVariable(), oldVar.getTermVariable());
			}
		}
		final Term result =
				new SubstitutionWithLocalSimplification(mgdScript, substitutionMapping).transform(ps.getFormula());
		return result;
	}

	public static <LOC extends IcfgLocation> Set<LOC> getLocationsForWhichHoareAnnotationIsComputed(
			final IIcfg<LOC> root, final HoareAnnotationPositions hoareAnnotationPositions) {
		final Set<LOC> hoareAnnotationLocs = new HashSet<>();
		switch (hoareAnnotationPositions) {
		case All:
			for (final Entry<String, Map<DebugIdentifier, LOC>> entry : root.getProgramPoints().entrySet()) {
				hoareAnnotationLocs.addAll(entry.getValue().values());
			}
			break;
		case LoopsAndPotentialCycles:
			hoareAnnotationLocs.addAll(IcfgUtils.getPotentialCycleProgramPoints(root));
			hoareAnnotationLocs.addAll(root.getLoopLocations());
			break;
		default:
			throw new AssertionError("unknown value " + hoareAnnotationPositions);
		}
		return hoareAnnotationLocs;
	}

	/**
	 * For each oldVar in vars that is not modifiable by procedure proc: substitute the oldVar by the corresponding
	 * globalVar in term and remove the oldvar from vars.
	 *
	 * @param modifiableGlobals
	 * @param script
	 */
	public static Term substituteOldVarsOfNonModifiableGlobals(final String proc, final Set<IProgramVar> vars,
			final Term term, final ModifiableGlobalsTable modifiableGlobals, final Script script) {
		final Set<IProgramNonOldVar> modifiableGlobalsOfProc = modifiableGlobals.getModifiedBoogieVars(proc);
		final List<IProgramVar> replacedOldVars = new ArrayList<>();

		final ArrayList<TermVariable> replacees = new ArrayList<>();
		final ArrayList<Term> replacers = new ArrayList<>();

		for (final IProgramVar bv : vars) {
			if (bv instanceof IProgramOldVar) {
				final IProgramNonOldVar pnov = ((IProgramOldVar) bv).getNonOldVar();
				if (!modifiableGlobalsOfProc.contains(pnov)) {
					replacees.add(bv.getTermVariable());
					replacers.add(((IProgramOldVar) bv).getNonOldVar().getTermVariable());
					replacedOldVars.add(bv);
				}
			}
		}

		final TermVariable[] substVars = replacees.toArray(new TermVariable[replacees.size()]);
		final Term[] substValues = replacers.toArray(new Term[replacers.size()]);
		Term result = script.let(substVars, substValues, term);
		result = new FormulaUnLet().unlet(result);

		for (final IProgramVar bv : replacedOldVars) {
			vars.remove(bv);
			vars.add(((IProgramOldVar) bv).getNonOldVar());
		}
		return result;
	}
}
