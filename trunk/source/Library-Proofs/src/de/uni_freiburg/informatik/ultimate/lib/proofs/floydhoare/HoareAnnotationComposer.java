/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2014-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE Proofs Library.
 *
 * The ULTIMATE Proofs Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Proofs Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Proofs Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Proofs Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Proofs Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.proofs.floydhoare;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.ModifiableGlobalsTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramOldVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IMLPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.ISLPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.TermVarsProc;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.ExtendedSimplificationResult;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.Substitution;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.normalforms.NnfTransformer;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.normalforms.NnfTransformer.QuantifierHandling;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.DAGSize;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation3;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap2;

/**
 * Hoare annotation for invariants computed by single CEGAR loop
 *
 * @author heizmann@informatik.uni-freiburg.de
 *
 */
public class HoareAnnotationComposer {

	private static final boolean AVOID_IMPLICATIONS = true;
	/**
	 * What is the precondition for a context? Strongest postcondition or entry given by automaton?
	 */
	private static final boolean USE_ENTRY = true;

	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private final CfgSmtToolkit mCsToolkit;
	private final PredicateFactory mPredicateFactory;
	private final HoareAnnotationFragments<?> mHoareAnnotationFragments;

	private final HoareAnnotationStatisticsGenerator mHoareAnnotationStatisticsGenerator;

	private final NestedMap2<IPredicate, IPredicate, Term> mLoc2callPred2disjunction;

	private int mNumberOfFragments = 0;
	private final Map<IPredicate, IPredicate> mLoc2hoare;

	private final IPredicate mSurrogateForEmptyCallPred;

	public HoareAnnotationComposer(final CfgSmtToolkit csToolkit, final PredicateFactory predicateFactory,
			final HoareAnnotationFragments<?> hoareAnnotationFragments, final IUltimateServiceProvider services) {
		mServices = services;
		mLogger = services.getLoggingService().getLogger(getClass());
		mCsToolkit = csToolkit;
		mPredicateFactory = predicateFactory;
		mHoareAnnotationFragments = hoareAnnotationFragments;
		mHoareAnnotationStatisticsGenerator = new HoareAnnotationStatisticsGenerator();
		mSurrogateForEmptyCallPred =
				mPredicateFactory.newPredicate(mCsToolkit.getManagedScript().getScript().term("true"));
		final HashRelation3<IPredicate, IPredicate, Term> loc2callPred2disjuncts =
				constructLoc2CallPred2DisjunctsMapping();
		mLoc2callPred2disjunction = constructLoc2Callpred2DisjunctionMapping(loc2callPred2disjuncts);
		mHoareAnnotationStatisticsGenerator.setNumberOfFragments(mNumberOfFragments);
		mHoareAnnotationStatisticsGenerator.setLocationsWithHoareAnnotation(mLoc2callPred2disjunction.keySet().size());
		mHoareAnnotationStatisticsGenerator.setPreInvPairs(mLoc2callPred2disjunction.size());
		mLoc2hoare = combineInter(mLoc2callPred2disjunction);

	}

	private Map<IPredicate, IPredicate>
			combineInter(final NestedMap2<IPredicate, IPredicate, Term> loc2callPred2invariant) {
		final Map<IPredicate, IPredicate> result = new HashMap<>();
		for (final IPredicate loc : loc2callPred2invariant.keySet()) {
			final List<Term> precondDisjuncts = new ArrayList<>();
			final Map<IPredicate, Term> callpred2invariant = loc2callPred2invariant.get(loc);
			final List<Term> conjuncts = new ArrayList<>(callpred2invariant.size());
			for (final Entry<IPredicate, Term> entry : callpred2invariant.entrySet()) {

				final IPredicate postForCallpred;
				if (!USE_ENTRY && !containsAnOldVar(entry.getKey())) {
					// compute SP
					throw new AssertionError("not implemented");
				}
				if (entry.getKey() == mSurrogateForEmptyCallPred) {
					postForCallpred = mSurrogateForEmptyCallPred;
				} else {
					postForCallpred = mHoareAnnotationFragments.getCallpred2Entry().get(entry.getKey());
				}
				assert postForCallpred != null : "no post for callpred";
				final Term precond =
						renameGlobalsToOldGlobals(postForCallpred, mServices, mCsToolkit.getManagedScript());
				precondDisjuncts.add(precond);

				if (mLogger.isDebugEnabled()) {
					mLogger.debug("In " + loc + " holds " + entry.getValue() + " for precond " + precond);
				}
				Term precondImpliesInvariant =
						Util.implies(mCsToolkit.getManagedScript().getScript(), precond, entry.getValue());
				if (AVOID_IMPLICATIONS) {
					precondImpliesInvariant =
							new NnfTransformer(mCsToolkit.getManagedScript(), mServices, QuantifierHandling.KEEP)
									.transform(precondImpliesInvariant);
				}

				conjuncts.add(precondImpliesInvariant);
			}
			final Term precondDisjunction = SmtUtils.or(mCsToolkit.getManagedScript().getScript(), precondDisjuncts);
			conjuncts.add(precondDisjunction);
			Term conjunction = SmtUtils.and(mCsToolkit.getManagedScript().getScript(), conjuncts);

			final Set<IProgramVar> vars = TermVarsProc
					.computeTermVarsProc(conjunction, mCsToolkit.getManagedScript(), mCsToolkit.getSymbolTable())
					.getVars();
			conjunction = substituteOldVarsOfNonModifiableGlobals(getRelevantProcedure(loc), vars, conjunction,
					mCsToolkit.getModifiableGlobalsTable(), mCsToolkit.getManagedScript());

			final ExtendedSimplificationResult simplificationResult = SmtUtils.simplifyWithStatistics(
					mCsToolkit.getManagedScript(), conjunction, mServices, SimplificationTechnique.SIMPLIFY_DDA);
			mHoareAnnotationStatisticsGenerator.reportSimplificationInter();
			mHoareAnnotationStatisticsGenerator.reportReductionInter(simplificationResult.getReductionOfTreeSize());
			mHoareAnnotationStatisticsGenerator
					.reportSimplificationTimeInter(simplificationResult.getSimplificationTimeNano());
			mHoareAnnotationStatisticsGenerator
					.reportAnnotationSize(new DAGSize().treesize(simplificationResult.getSimplifiedTerm()));
			final Term simplified = simplificationResult.getSimplifiedTerm();
			final Term pnf =
					SmtUtils.constructPositiveNormalForm(mCsToolkit.getManagedScript().getScript(), simplified);
			final BasicPredicate pred = mPredicateFactory.newPredicate(pnf);
			result.put(loc, pred);
		}
		return result;
	}

	private static String getRelevantProcedure(final IPredicate location) {
		if (location instanceof ISLPredicate) {
			return ((ISLPredicate) location).getProgramPoint().getProcedure();
		}
		if (location instanceof IMLPredicate) {
			final var programPoints = ((IMLPredicate) location).getProgramPoints();
			if (programPoints.length == 1) {
				return programPoints[0].getProcedure();
			}
			// We cannot associate a unique procedure to the location, as multiple threads are running.
			// We fall back to ULTIMATE.init, as it is the entry point and any global variable modifiable by any thread
			// must be modifiable by ULTIMATE.init as well.
			return "ULTIMATE.init";
		}
		throw new IllegalArgumentException("unsupported type: " + location.getClass());
	}

	private NestedMap2<IPredicate, IPredicate, Term> constructLoc2Callpred2DisjunctionMapping(
			final HashRelation3<IPredicate, IPredicate, Term> loc2precond2invariantSet) {
		final NestedMap2<IPredicate, IPredicate, Term> loc2precond2invariant = new NestedMap2<>();
		for (final IPredicate loc : loc2precond2invariantSet.projectToFst()) {
			for (final IPredicate precond : loc2precond2invariantSet.projectToSnd(loc)) {
				final Set<Term> terms = loc2precond2invariantSet.projectToTrd(loc, precond);
				mNumberOfFragments += terms.size();
				final Term invariant = or(terms);
				loc2precond2invariant.put(loc, precond, invariant);
			}
		}
		return loc2precond2invariant;
	}

	private Term or(final Set<Term> terms) {
		final Term disjunction = SmtUtils.or(mCsToolkit.getManagedScript().getScript(), terms);
		final ExtendedSimplificationResult simplificationResult = SmtUtils.simplifyWithStatistics(
				mCsToolkit.getManagedScript(), disjunction, mServices, SimplificationTechnique.POLY_PAC);
		mHoareAnnotationStatisticsGenerator.reportSimplification();
		mHoareAnnotationStatisticsGenerator.reportReduction(simplificationResult.getReductionOfTreeSize());
		mHoareAnnotationStatisticsGenerator.reportSimplificationTime(simplificationResult.getSimplificationTimeNano());
		return simplificationResult.getSimplifiedTerm();
	}

	/**
	 * Construct mapping for our three cases: - invariants for empty callpred - invariants for dead callpred -
	 * invariants for live callpred
	 *
	 */
	public HashRelation3<IPredicate, IPredicate, Term> constructLoc2CallPred2DisjunctsMapping() {
		final HashRelation3<IPredicate, IPredicate, Term> loc2callpred2invariant = new HashRelation3<>();

		addHoareAnnotationForCallPred(loc2callpred2invariant, mSurrogateForEmptyCallPred,
				mHoareAnnotationFragments.getProgPoint2StatesWithEmptyContext());

		for (final IPredicate callPred : mHoareAnnotationFragments.getDeadContexts2ProgPoint2Preds().keySet()) {
			final HashRelation<IPredicate, IPredicate> pp2preds =
					mHoareAnnotationFragments.getDeadContexts2ProgPoint2Preds().get(callPred);
			addHoareAnnotationForCallPred(loc2callpred2invariant, callPred, pp2preds);
		}

		for (final IPredicate callPred : mHoareAnnotationFragments.getLiveContexts2ProgPoint2Preds().keySet()) {
			final HashRelation<IPredicate, IPredicate> pp2preds =
					mHoareAnnotationFragments.getLiveContexts2ProgPoint2Preds().get(callPred);
			addHoareAnnotationForCallPred(loc2callpred2invariant, callPred, pp2preds);
		}
		return loc2callpred2invariant;
	}

	/**
	 * Construct mapping for our three cases: - invariants for empty callpred - invariants for dead callpred -
	 * invariants for live callpred
	 *
	 */
	public HashRelation3<IPredicate, IPredicate, Term> constructMappingOld() {
		final HashRelation3<IPredicate, IPredicate, Term> loc2callpred2invariant = new HashRelation3<>();

		final IPredicate surrogateForEmptyCallPred =
				mPredicateFactory.newPredicate(mCsToolkit.getManagedScript().getScript().term("true"));
		addHoareAnnotationForCallPred(loc2callpred2invariant, surrogateForEmptyCallPred,
				mHoareAnnotationFragments.getProgPoint2StatesWithEmptyContext());

		for (final IPredicate context : mHoareAnnotationFragments.getDeadContexts2ProgPoint2Preds().keySet()) {
			IPredicate precondForContext;
			if (!USE_ENTRY && !containsAnOldVar(context)) {
				// compute SP
				throw new AssertionError("not implemented");
			}
			precondForContext = mHoareAnnotationFragments.getCallpred2Entry().get(context);
			precondForContext = renameGlobalsToOldGlobals(precondForContext, mServices, mCsToolkit.getManagedScript(),
					mPredicateFactory, SimplificationTechnique.SIMPLIFY_DDA);
			final HashRelation<IPredicate, IPredicate> pp2preds =
					mHoareAnnotationFragments.getDeadContexts2ProgPoint2Preds().get(context);
			addHoareAnnotationForCallPred(loc2callpred2invariant, precondForContext, pp2preds);
		}

		for (final IPredicate context : mHoareAnnotationFragments.getLiveContexts2ProgPoint2Preds().keySet()) {
			IPredicate precondForContext;
			if (!USE_ENTRY && !containsAnOldVar(context)) {
				// compute SP
				throw new AssertionError("not implemented");
			}
			precondForContext = mHoareAnnotationFragments.getCallpred2Entry().get(context);
			precondForContext = renameGlobalsToOldGlobals(precondForContext, mServices, mCsToolkit.getManagedScript(),
					mPredicateFactory, SimplificationTechnique.SIMPLIFY_DDA);
			final HashRelation<IPredicate, IPredicate> pp2preds =
					mHoareAnnotationFragments.getLiveContexts2ProgPoint2Preds().get(context);
			addHoareAnnotationForCallPred(loc2callpred2invariant, precondForContext, pp2preds);
		}
		return loc2callpred2invariant;
	}

	/**
	 * @param loc2callPred2invariant
	 * @param precondForContext
	 * @param pp2preds
	 */
	private static <DOM extends IPredicate> void addHoareAnnotationForCallPred(
			final HashRelation3<IPredicate, IPredicate, Term> loc2callPred2invariant,
			final IPredicate precondForContext, final HashRelation<DOM, IPredicate> pp2preds) {
		for (final DOM loc : pp2preds.getDomain()) {
			final Set<IPredicate> preds = pp2preds.getImage(loc);
			for (final IPredicate pred : preds) {
				loc2callPred2invariant.addTriple(loc, precondForContext, pred.getFormula());
			}
		}
	}

	private static boolean containsAnOldVar(final IPredicate p) {
		return p.getVars().stream().anyMatch(IProgramVar::isOldvar);
	}

	public HoareAnnotationStatisticsGenerator getHoareAnnotationStatisticsGenerator() {
		return mHoareAnnotationStatisticsGenerator;
	}

	public Map<IPredicate, IPredicate> getLoc2hoare() {
		return mLoc2hoare;
	}

	public IFloydHoareAnnotation<IPredicate> extractAnnotation() {
		// TODO #proofRefactor pre/post
		return new FloydHoareMapping<>(null, null, mLoc2hoare);
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
	private static IPredicate renameGlobalsToOldGlobals(final IPredicate ps, final IUltimateServiceProvider services,
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
		Term renamedFormula = Substitution.apply(mgdScript, substitutionMapping, ps.getFormula());
		renamedFormula = SmtUtils.simplify(mgdScript, renamedFormula, services, simplificationTechnique);
		final IPredicate result = predicateFactory.newPredicate(renamedFormula);
		return result;
	}

	/**
	 * Construct Term which represents the same set of states as ps, but where all globalVars are renamed to
	 * oldGlobalVars.
	 *
	 */
	private static Term renameGlobalsToOldGlobals(final IPredicate ps, final IUltimateServiceProvider services,
			final ManagedScript mgdScript) {
		final Map<Term, Term> substitutionMapping = new HashMap<>();
		for (final IProgramVar pv : ps.getVars()) {
			if (pv instanceof IProgramNonOldVar) {
				final IProgramVar oldVar = ((IProgramNonOldVar) pv).getOldVar();
				substitutionMapping.put(pv.getTermVariable(), oldVar.getTermVariable());
			}
		}
		final Term result = Substitution.apply(mgdScript, substitutionMapping, ps.getFormula());
		return result;
	}

	/**
	 * For each oldVar in vars that is not modifiable by procedure proc: substitute the oldVar by the corresponding
	 * globalVar in term and remove the oldvar from vars.
	 */
	private static Term substituteOldVarsOfNonModifiableGlobals(final String proc, final Set<IProgramVar> vars,
			final Term term, final ModifiableGlobalsTable modifiableGlobals, final ManagedScript mgdScript) {
		final Set<IProgramNonOldVar> modifiableGlobalsOfProc = modifiableGlobals.getModifiedBoogieVars(proc);
		final List<IProgramVar> replacedOldVars = new ArrayList<>();
		final Map<Term, Term> substitutionMapping = new HashMap<>();
		for (final IProgramVar bv : vars) {
			if (bv instanceof IProgramOldVar) {
				final IProgramNonOldVar pnov = ((IProgramOldVar) bv).getNonOldVar();
				if (!modifiableGlobalsOfProc.contains(pnov)) {
					substitutionMapping.put(bv.getTermVariable(),
							((IProgramOldVar) bv).getNonOldVar().getTermVariable());
					replacedOldVars.add(bv);
				}
			}
		}
		final Term result = Substitution.apply(mgdScript, substitutionMapping, term);
		for (final IProgramVar bv : replacedOldVars) {
			vars.remove(bv);
			vars.add(((IProgramOldVar) bv).getNonOldVar());
		}
		return result;
	}
}
